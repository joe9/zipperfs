{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

-- Zipper over the Map with path accumulation
-- and sharing preservation
-- $Id: ZipperM.hs,v 1.4 2005/09/22 03:06:38 oleg Exp $

module ZipperM (Term(..)
		, FileName
		, FileCont
		, NavigateDir(..)
		, DZipper(..)
		, dzip'term
	        , module Control.Monad.CC.CCCxe
	       ) where

-- Import (one of the) CC libraries
-- http://okmij.org/ftp/continuations/implementations.html#CC-monads
-- We chose CCCxe; CCExe would work just as well
-- We chose the prompt flavor PP
import           Control.Monad.CC.CCCxe

import           Control.Monad.Identity
import           Control.Monad.Trans
import qualified Data.Map               as Map
import           Data.Typeable

-- -------------------------------------------------------------
-- The Term to traverse: the representation of a file system
-- Currently, the file system is in-memory; in virtual memory, to be precise
-- It is easy to change the Term below so that "File" only points to file
-- data rather than containing them.

type FileName = String
type FileCont = String			-- File content
data Term = File FileCont | Folder (Map.Map FileName Term)

instance Show Term where
    showsPrec _ (File file) = (file ++)
    showsPrec _ (Folder dir) =
	("\n >>>" ++) . (Map.foldWithKey fl ("\n<<<" ++) dir)
	where fl k term acc = ("\n" ++) . (k ++) . (": " ++) .
			      (showsPrec 5 term) . acc

-- -------------------------------------------------------------
-- Traversable of Term

-- We now derive the function to traverse and update a Term.
-- The traverse function is a variant of fmap, or of Traversable.mapM
-- to be precise.
-- The fmap function assumes that every visited node will be updated,
-- by the mapping function, the iteratee.
-- Our traverse is optimized for the opposite case: most of the
-- traversed nodes will not be updated. If a branch is not modified,
-- it should not be copied into the result; rather, it should be
-- shared with the original term. Furthermore, we permit the
-- iteratee to bypass the branches of the term during the traversal.


-- Index for a place (node) in the file system tree
-- It is the list of FileNames to navigate from the root of the
-- tree, in the REVERSE order
data PathComp = PathName FileName
	      | PathUpdated		-- The update indicator
   deriving (Eq, Show)
type Path = [PathComp]

-- Where to go next: the iteratee tells the global enumerator where
-- to go next. The iteratee may also tell to update the current
-- term
data NavigateDir =
    Update Term		-- replace the current term with the given
  | DownTo FileName
  | Up
  | Next
    deriving (Show)

-- If the term has been updated during the traversal
data UpdateStatus = Dirty | Unmodified deriving Show

-- Updateable traversal that maximally preserves the sharing
-- If the Iteratee always returns Next, the whole tree is traversed
-- pre-order (to be precise, the directory is given to the iteratee
-- before and after traversing any child node)
-- The Iteratee may ask to skip the branches, returning
--  Up     -- return to the parent; skipping the rest of the current folder
--  DownTo -- go immediately to the specified child in the folder
--            skipping what was before in the directory order
-- If the Iteratee returns (Update term), the current term
-- is replaced with the given, and the traversal restarts from it

traverse :: Monad m =>
  (Path -> Term -> m NavigateDir)  -- traversal fn, iteratee
  -> Term			   -- term to traverse
  -> m (Term, UpdateStatus)
traverse tf term = loop Nothing [] term
  where
  loop comefrom path term = tf path term >>= \x -> case x of
    Update new_term -> loop comefrom (PathUpdated:path) new_term  -- re-traverse
    Up              -> up path term				  -- cut
    nav             -> down comefrom path term nav

  up (PathUpdated:_) term = return (term,Dirty)
  up _               term = return (term,Unmodified)

  down _ path term@File{} Next = up path term
  down _ _         File{} nav  =
    error $ "bad navigation from a File: " ++ show nav
  down _ path pt@(Folder fld) (DownTo fname)
                               | Just term <- Map.lookup fname fld =
    child fname path fld term
  down _ path _ (DownTo fname) = error $ "No folder component: " ++ fname
  down _ path pt@(Folder fld) Next | Map.null fld = up path pt
  down Nothing path pt@(Folder fld) Next | (fname, term) <- Map.findMin fld =
      child fname path fld term

  down (Just fname) path pt@(Folder fld) Next | idx <- Map.findIndex fname fld =
      let idx' = succ idx in
      if idx' == Map.size fld then up path pt
      else let (fname,term) = Map.elemAt idx' fld in
      child fname path fld term

  child fname path fld term =
    loop Nothing (PathName fname:path) term >>= \x -> case x of
      (term, Dirty) ->
	   loop (Just fname) (PathUpdated:path)
		    (Folder (Map.insert fname term fld))
      _             -> loop (Just fname) path (Folder fld)


-- A sample file system, to be used in examples
fs1 :: Term
fs1 = Folder $ Map.fromList [("d1",d1), ("d2",Folder $ Map.empty),
			      ("fl1", File "File1"),
			      ("fl2", File "File2")]
	   where d1  = Folder $ Map.fromList [("fl13",File "File 3"),
					     ("d11", d11)]
		 d11 = Folder $ Map.fromList [("d111", Folder $ Map.empty)]


testt1 = runIdentity (traverse (\_ term -> return Next) fs1)
-- *Zipper2> fst testt1 == fs1
-- True

testt2 = traverse tf fs1
    where tf path term = do print path; print term; return Next

testt3 = traverse tf fs1
  where
  tf (PathName "d11":_) term  = do
     print "cutting"
     print term
     return Up
  tf path term = do
     print term
     return Next


testt4 = runIdentity (traverse tf fs1)
    where tf (PathName "d11":_) _ = return (Update $ Folder $ Map.empty)
	  tf (PathName "fl2":_) _ = return (Update $ File $ "New file2")
	  tf _ _ = return Next

lprint x = liftIO $ print x


-- -------------------------------------------------------------
-- Zipper data structure
-- It is generic:
-- It depends only on the _interface_ of the traversal function
-- (but not on its implementation)

-- One may say, why not to put path accumulation into `traverse' itself?
-- We could have. However, we wish to illustrate here that the traverse
-- deals only with the local information. Accumulating it into a global
-- state is left for the clients. Zipper can let us add a new, `missing'
-- aspect to the enumerator.

data DZipper m =
    DZipper{
	    dz_path :: [FileName],
	    dz_term :: Term,
	    dz_k    ::     NavigateDir -> CC PP m (DZipper m)
	    }
  | DZipDone Term
    deriving (Typeable)

-- instance Typeable1 m => Typeable (DZipper m) where
--   typeOf x = mkTyConApp (mkTyCon "ZipperM.DZipper") [typeOf1 $ mof x]
--     where mof :: DZipper m -> m (); mof = undefined

-- One prompt, used by the generator (the yield/enumerate pair)
-- We instantiate the global pp to the desired answer-type.
pz :: Typeable1 m => Prompt PP m (DZipper m)
pz = pp

dzip'term :: (Typeable1 m, Monad m) => Term -> CC PP m (DZipper m)
dzip'term term = pushPrompt pz (traverse tf term >>= return . DZipDone . fst)
 where
 tf path term = shift0P pz (\k -> return $ DZipper (dir_path path) term k)
 dir_path = foldr filterfn []
 filterfn (PathName fname) acc = fname : acc
 filterfn _                acc = acc

testdz1 :: IO ()
testdz1 = runCC $ do
  dz <- dzip'term fs1
  let loop (DZipDone term) = lprint "Finished" >> lprint term
      loop dz = do
	lprint $ (show $ dz_path dz)
        lprint $ dz_term dz
        dz_k dz Next >>= loop
  loop dz

