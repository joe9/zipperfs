{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE Rank2Types         #-}
{-# LANGUAGE StandaloneDeriving #-}

-- Zipper-based File/Operating system
-- with threading and exceptions all realized via delimited continuations.
-- There are no unsafe operations, no GHC (let alone) Unix threads,
-- no concurrency problems. Our threads can't even do IO and can't
-- mutate any global state -- and the type system sees to it.

-- Please see http://okmij.org/ftp/continuations/ZFS/zfs-talk.pdf
-- for the demo and explanations.

-- $Id: ZFS.hs,v 1.8 2005/10/14 23:00:41 oleg Exp $


module ZFS where

import           ZipperM
-- From the Iteratee library
import           LowLevelIO

import           Data.List           as List
import qualified Data.Map            as Map
import           Data.Typeable

import           Control.Exception   (bracket, throwIO)
import           Control.Monad.Trans (liftIO)
import           Foreign.C.Error     (errnoToIOError)
import           Network.Socket
import           System.IO
import           System.IO.Error     as IO
import           System.Posix.Types  (Fd (..))


-- Port to serve clients from
newClientPort = 1503
-- select_timeout = 100000 -- microseconds

-- Initial content of the file system
-- Certainly, structurally richer filesystems are equally possible
-- (where content is annotated with attributes, e.g.)
-- A lambda-term can be made a filesystem too
fs1 :: Term
fs1 = Folder $ Map.fromList [("d1",d1), ("d2",Folder $ Map.empty),
			      ("fl1", File "File1"),
			      ("fl2", File "File2")]
	   where d1  = Folder $ Map.fromList [("fl13",File "File 3"),
					     ("d11", d11)]
		 d11 = Folder $ Map.fromList [("d111", Folder $ Map.empty)]

-- Another file system -- this time, it is cyclic!
fs2 :: Term
fs2 = Folder $ Map.fromList [("d1",fs2), ("fl1", File "File1")]


-- Operating system requests: from a ``process'' to the ``OS''

type FSZipper m = DZipper m

type CCM m = CC PP m			-- the type of the CC monad transformer

-- The base monad type `m' is left polymorphic.
-- A Process doesn't do any IO (it asks the ``OS'').
-- The significant part of the OS, the process itself, is overtly
-- outside the IO monad!
-- By using different prompts, the requests can be modularized.
-- Unlike OS (with its only one syscall handler), we can have as
-- many syscall handlers as we wish.
data OSReq m = OSRDone
	     | OSRRead (ReadK m)
	     | OSRWrite String (UnitK m)
	     | OSRTrace String (UnitK m) -- so a process can syslog
	     | OSRCommit Term (UnitK  m)
	     | OSRefresh (FSZipper m -> CCM m (OSReq m))
               deriving (Typeable)

-- instance Typeable1 m => Typeable (OSReq m) where
--   typeOf x = mkTyConApp (mkTyCon "ZFS.OSReq") [typeOf1 $ mof x]
--     where mof :: OSReq m -> m (); mof = undefined

-- The OS services prompt
-- We instantiate the global pp to the desired answer-type.
pOS :: Typeable1 m => Prompt PP m (OSReq m)
pOS = pp

type UnitK m = () -> CCM m (OSReq m)
type ReadK m = String -> CCM m (OSReq m)

data ProcessCTX = ProcessCTX { psocket :: Socket -- process' socket
			     }

-- A process can only be blocked on reading. For simplicity we assume
-- that writing into the client socket never blocks

data JobQueueT = JQBlockedOnRead ProcessCTX (ReadK IO)
	       | JQRunnable ProcessCTX (UnitK IO)
	       | JQNewClient Socket  -- accept new clients from

data World = World { mountedFS :: Term
		   , jobQueue  :: [JobQueueT ]
		   }
main = main' fs1

main' fs = bracket (serverSocket newClientPort) sClose $
  \s ->
    do
    -- The following doesn't help: accept blocks anyway...
    -- setFdOption (Fd (fdSocket s)) NonBlockingRead True
    runCC $ do
	    syslog ["Entering the osloop",show s]
	    osloop $ World{mountedFS = fs, jobQueue = [JQNewClient s]}
 where
 serverSocket port = do
  s <- socket AF_INET Stream 0
  setSocketOption s ReuseAddr 1
  localhost <- inet_addr "127.0.0.1"
  bindSocket s (SockAddrInet port localhost)
  listen s 5
  return s

-- In OS parlance, the following is the interrupt handler.
-- It `waits' for interrupts that is, if any input socket has something
-- to read from.
-- It doesn't actually return, so the answer type is just any

osloop :: World -> CCM IO any
osloop world =
    maybe (wait'for'intr world) (uncurry try'to'run) (find'runnable world)
    >>= osloop

  where

  -- Try to find the first runnable job
  find'runnable world = case break is'runnable (jobQueue world) of
       (jq,[]) -> Nothing
       (jq1,(runnable:jq2)) -> Just (runnable, world{jobQueue=jq1++jq2})
   where is'runnable (JQRunnable _ _) = True
	 is'runnable _                = False

  wait'for'intr world@World{jobQueue=jq} =
      do readyfd <- liftIO ( select'read'pending mfd >>=
                             either select_err return )
	 case break (\e -> maybe False (`elem` readyfd) (toFD e)) jq of
	    (jq,[]) -> return world -- nothing found
	    (jq1,(now'runnable:jq2)) ->
		try'to'run now'runnable world{jobQueue=jq1++jq2}
   where
   -- compile the list of file descriptors we are waiting at
   mfd :: [Fd]
   mfd = foldr (\e a -> maybe [] (:a) (toFD e)) [] jq
   toFD :: JobQueueT -> Maybe Fd
   toFD (JQNewClient s) = Just . fromIntegral $ fdSocket s
   toFD (JQBlockedOnRead ProcessCTX{psocket=s} _) =
       Just . fromIntegral $ fdSocket s
   toFD _ = Nothing

   select_err :: Errno -> IO any
   select_err e = throwIO $ errnoToIOError "select" e Nothing Nothing

  -- Add to the end of the job queue
  enqueue el world = world{jobQueue = jobQueue world ++ [el]}

  ifnM action onf ont = liftIO action >>= \b -> if b then ont else onf

  -- New client is trying to connect
  try'to'run qe@(JQNewClient s) world = do
      syslog ["accepting from",show s]
      (clientS,addr) <- liftIO $ accept s
      liftIO $ setSocketOption clientS NoDelay 1
      syslog ["accepted new client connection from ", show addr]
      let newCtx = ProcessCTX clientS
      run'process (fsProcess (dzip'term (mountedFS world)))
	      >>= interpret'req (enqueue qe world) newCtx

  try'to'run (JQRunnable ctx k) world = k () >>= interpret'req world ctx

  -- A client socket may have something to read
  try'to'run qe@(JQBlockedOnRead ctx@ProcessCTX{psocket=s} k) world = do
      syslog ["reading from",show s]
      syslog ["osloop: queue size: ", show $ length $ jobQueue world]
      dat <- liftIO $ (
	     do r <-  IO.tryIOError (recv s (1024 * 8))
                case r of
                       Left err  -> if isEOFError err then return ""
                                    else ioError err
		       Right msg -> return msg)
      k dat >>= interpret'req world ctx


-- The system logger
syslog s = liftIO $ putStrLn (concat s)


-- The interpreter of OS requests -- the syscall handler, in OS parlance
-- It handles simple requests by itself. When the request involves
-- rescheduling or a change in the global OS state, it returns to
-- the scheduler/interrupt-handler/osloop.

interpret'req :: World -> ProcessCTX -> OSReq IO -> CCM IO World

-- The process is finished
interpret'req world ctx OSRDone = (liftIO . sClose $ psocket ctx)
				  >> return world

-- The request for read may block. So, we do the context switch and go
-- to the main loop, to check if the process socket has something to read
-- from
interpret'req world ctx (OSRRead k) =
       return world{jobQueue = (jobQueue world) ++ [JQBlockedOnRead ctx k]}

-- We assume that writing to a socket never blocks
interpret'req world ctx (OSRWrite datum k) = do
  send' (psocket ctx) datum
  k () >>= interpret'req world ctx
 where
  send' _ ""  = return ()
  send' s msg = do  c <- liftIO $ send s msg
                    send' s (drop c msg)

interpret'req world ctx (OSRTrace datum k) = do
  syslog ["Trace from",show $ psocket ctx,": ",datum]
  k () >>= interpret'req world ctx

interpret'req world ctx (OSRCommit term k) =
  return world{jobQueue = jobQueue world ++ [JQRunnable ctx k],
	       mountedFS = term}

interpret'req world ctx (OSRefresh k) =
       (dzip'term $ mountedFS world) >>= k >>= interpret'req world ctx


-- We have the functionality of threads -- although our whole program
-- is simply threaded, both at the OS level and at the GHC runtime level.
-- Our process functions don't even have the IO type!
-- Note, the function to run the process has forall m. That means, a process
-- function can't do any IO and can't have any reference cells.
-- Processes can't mutate the global state -- and the type system checks that!
-- Because processes can't interfere with each other and with the OS, there
-- is no need for any thread synchronization, locking, etc. We get
-- the transactional semantics for free.
-- Of course, as different processes manipulate their own (copy-on-write)
-- terms (file systems), when the processes commit, there may be conflicts.
-- So, one has to implement some conflict resolution -- be it versioning,
-- patching, asking for permission for update, etc. But
-- these policies are implemented at the higher-level; the programmer can
-- implement any set of policies. Because processes always ask the supervisor
-- for anything, and the supervisor has the view of the global state,
-- the resolution policies are easier to implement in this execution model.

run'process :: (forall m. (Typeable1 m, Monad m) => CCM m (OSReq m))
	    -> CCM IO (OSReq IO)
run'process body = pushPrompt pOS body



------------------------------------------------------------------------
-- Processes. No IO action is possible in here


fsProcess :: (Typeable1 m, Monad m) =>
	     CCM m (FSZipper m) -> CCM m (OSReq m)
fsProcess zipper'action = do
  z <- zipper'action
  svc $ OSRTrace "Begin process"
  fsloop z ""


fsloop :: (Typeable1 m, Monad m) =>
	  FSZipper m -> String -> CCM m (OSReq m)
fsloop z line'acc = do
  send_shell_prompt z
  (line,rest) <- read'line line'acc
  let (cmd,arg) = breakspan is'whitespace line
  svc $ OSRTrace $ "received command: " ++ cmd
  maybe (svc (OSRWrite $ "bad command: " ++ cmd) >>  fsloop z rest)
	(\h -> h z cmd arg rest)
	(List.lookup cmd fsCommands)
  where
  -- Read until we get newline
  read'line acc = case break is'nl acc of
		  (_,"") -> do
			    b <- svc OSRRead
			    svc $ OSRTrace $ "Read str: " ++ b
			    (l,rest) <- read'line b
			    return (acc ++ l, rest)
		  (l,rest) -> return (l,snd $ span is'nl rest)

  send_shell_prompt z =
    svc $ OSRWrite $ ("\n" ++ show_path (dz_path z) ++ "> ")


show_path path = concatMap ('/':) $ reverse path

fsCommands :: (Typeable1 m, Monad m) =>
	      [(String,
		FSZipper m -> String -> String -> String -> CCM m (OSReq m))]

fsCommands =
    [
     ("quit", \z _ _ _ -> svc $ const OSRDone),
     ("cd", fsWrapper (\z _ path -> cd'zipper z path >>= return . FSCZ)),
     ("ls",    fsWrapper cmd'ls),
     ("cat",   fsWrapper cmd'ls),
     ("next",  fsWrapper cmd'next),

     ("mkdir", fsWrapper (\z _ path ->
			  cmd'mknode (Folder Map.empty) z path)),
     ("touch", fsWrapper (\z _ path ->
			  cmd'mknode (File "") z path)),

     ("echo",  fsWrapper cmd'echo),
     ("rm",    fsWrapper cmd'rm),
     ("mv",    fsWrapper cmd'mv),
     ("cp",    fsWrapper cmd'cp),

     ("help",  fsWrapper cmd'help),

     ("commit",  fcmd'commit),
     ("refresh", \z _ _ rest -> svc OSRefresh >>= \z -> fsloop z rest)
   -- next is really cool!
   -- We can cd inside a file! So, cat is just `ls' inside a file
    ]

fcmd'commit z _ _ rest = aux z
  where
  aux (DZipDone term) = (svc $ OSRCommit term) >> fsloop z rest
  aux DZipper{dz_k = k} = k Up >>= aux


-- Execute a file system navigation/update command
-- The command may report an error, which we catch and show
-- We use delimited continuations rather than an Error monad
data FSCmdResp m = FSCS String | FSCZ (FSZipper m)
                 deriving (Typeable)

type ShellCmd =
    (Typeable1 m, Monad m) =>
    FSZipper m -> String -> String -> CCM m (FSCmdResp m)

-- instance Typeable1 m => Typeable (FSCmdResp m) where
--   typeOf x = mkTyConApp (mkTyCon "ZFS.FSCmdResp") [typeOf1 $ mof x]
--     where mof :: FSCmdResp m -> m (); mof = undefined

-- The Shell services prompt
-- We instantiate the global pp to the desired answer-type.
pShell :: Typeable1 m => Prompt PP m (FSCmdResp m)
pShell = pp

shellErr :: (Typeable1 m, Monad m) => String -> CCM m any
shellErr = abortP pShell . return . FSCS

fsWrapper cmd z cmd'name cmd'arg rest = do
  resp <- pushPrompt pShell (cmd z cmd'name cmd'arg)
  z' <- case resp of
         FSCS str -> (svc $ OSRWrite str) >> return z
         FSCZ z   -> return z
  fsloop z' rest



cmd'help :: ShellCmd
cmd'help z _ _ = return $ FSCS $ "Commands: " ++
		   (concat $ intersperse ", " $ List.map fst cmds)
  where
  cmds = fsCommands
  -- The following statement does nothing at run-time. It is here
  -- just to tell the typechecker that the monad `m' in fsCommands and
  -- that in 'z' are the same
  _ = snd (head cmds) z


cmd'ls z _ slash'path = cd'zipper z slash'path >>= return . FSCS . list_node

cmd'next z _ _ = do
  z' <- dz_k z Next
  return $ FSCZ $ case z' of DZipDone _ -> z; _ -> z'


-- main navigation function
cd'zipper :: (Typeable1 m, Monad m) =>
	     FSZipper m -> String  -> CCM m (FSZipper m)
cd'zipper z "" = return z
cd'zipper z ('/':path) = do z' <- ascend'to'root z; cd'zipper z' path
  where
  ascend'to'root z@DZipper{dz_path=[]} = return z
  ascend'to'root z                     = dz_k z Up >>= ascend'to'root

cd'zipper z ('.':'.':path) = aux z (snd $ span (=='/') path)
 where
 aux DZipper{dz_path = []} _ = return z -- already at the top
 aux DZipper{dz_k = k} path  = k Up >>= (\z -> cd'zipper z path)

cd'zipper DZipper{dz_term = File _} _ =
    shellErr $ "cannot descend down the file"
cd'zipper DZipper{dz_term = Folder fld, dz_k = k} path
    = let (pc,prest) = breakspan (== '/') path
      in if Map.member pc fld then do
				   z' <- k (DownTo pc)
				   cd'zipper z' prest
	 else shellErr $ "No such dir component " ++ pc


-- List the current contents of the node pointed by the zipper
-- This function subsumes both `ls' and `cat'
-- For files, it sends the content of the file
list_node DZipper{dz_term = File str} = str
list_node DZipper{dz_term = Folder fld} =
    Map.foldWithKey (\name el acc ->
		     "\n" ++ name ++ (case el of Folder _ -> "/"
				                 _ -> "") ++ acc)
                    "" fld


-- make or replace a node (an empty directory or an empty file or a moved node)
-- named 'dirn' in the current directory
-- Return the updated zipper plus the old value, if existed
cmd'updnode :: (Typeable1 m, Monad m) =>
	      Term			-- new value
	      -> FSZipper m
	      -> FileName
	      -> CCM m (Maybe Term, FSCmdResp m)
cmd'updnode _ _ dirn | '/' `elem` dirn =
    shellErr "the name of the new node can't contain slash"
cmd'updnode _ _ "" =
    shellErr "the name of the new node is empty"
cmd'updnode newnode DZipper{dz_term = File _} _ =
    shellErr "cannot create anything in a file"
cmd'updnode newnode DZipper{dz_term = Folder fld, dz_k = k} dirn =
    let (old, fld') = Map.insertLookupWithKey
		        (\_ newnode _ -> newnode) dirn newnode fld
    in k (Update $ Folder fld') >>= \z -> return (old, FSCZ z)

-- Really make a new node; it should not have existed before
cmd'mknode :: (Typeable1 m, Monad m) =>
	      Term			-- new value
	      -> FSZipper m
	      -> FileName
	      -> CCM m (FSCmdResp m)
cmd'mknode newnode z fname = do
  (old,z) <- cmd'updnode newnode z fname
  maybe (return z) (const $ shellErr $ "Already exists: " ++ fname) old

-- "echo string > path"
cmd'echo z _ args = aux $ (reads::ReadS String) args
 where
 aux [(content,rest)] = aux1 content (snd $ span is'whitespace rest)
 aux _ = shellErr $ "bad format, str, of the echo cmd"
 aux1 content ('>':rest) =
     cd'zipper z (snd $ span is'whitespace rest) >>= aux2 content rest
 aux1 _ _ = shellErr $ "bad format, path, of the echo cmd"
 aux2 content rest DZipper{dz_term = File _, dz_k = k} =
     k (Update (File content)) >>= return . FSCZ
 aux2 _ rest _ = shellErr $ rest ++ " does not point to a file"


-- Delete the node pointed to by path and return the
-- updated zipper (which points to z's parent) and the
-- deleted node
del'zipper z path = cd'zipper z path >>= aux
  where
  aux DZipper{dz_path=[]} =
      shellErr $ "cannot remove the root folder"
  aux DZipper{dz_path=(fname:_), dz_k=k} = k Up >>= aux1 fname
  aux1 fname DZipper{dz_term = Folder fld, dz_k = k} =
   let (Just old'node, fld') = Map.updateLookupWithKey (\_ _ -> Nothing)
			          fname fld
   in k (Update $ Folder $ fld') >>= \z -> return (z,old'node)

-- insert a node as `path'
ins'zipper node z0 path = do
  let (dirname,basename) = split'path path
  z <- if dirname == "" then return z0 else cd'zipper z0 dirname
  cmd'mknode node z basename


-- rm path
-- works both on directories and files
-- One can even try to remove one's own parent -- and this is safe!
cmd'rm z _ path = del'zipper z path >>= return . FSCZ . fst

-- mv path_from path_to
cmd'mv z _ args = aux $ breakspan is'whitespace args
  where
  aux ("",_) = shellErr "mv: from-path is empty"
  aux (_,"") = shellErr "mv: to-path is empty"
  aux (pfrom,pto) = del'zipper z pfrom >>=
		    \ (z,node) -> ins'zipper node z pto

-- cp path_from path_to
-- We don't do any copying: we merely establish sharing:
-- so a node accessible via `from_path' becomes accessible via `to_path'
-- The copy-on-write semantics of ZFS does the rest.
-- In ZFS, we can copy arbitrary file systems trees in constant time!
cmd'cp z0 _ args = aux $ breakspan is'whitespace args
  where
  aux ("",_) = shellErr "cp: from-path is empty"
  aux (_,"") = shellErr "cp: to-path is empty"
  aux (pfrom,pto) = cd'zipper z0 pfrom >>= aux1 pto
  aux1 pto DZipper{dz_term = term} = do
    let (dirname,basename) = split'path pto
    z <- if dirname == "" then return z0 else cd'zipper z0 dirname
    cmd'updnode term z basename >>= return . snd


-- Supervisor call
svc req = shift0P pOS (return . req)

is'whitespace c = c == ' ' || c == '\t'
is'nl c = c == '\n' || c == '\r'

breakspan pred l = let (p1,p2) = break pred l
		   in (p1,snd $ span pred p2)

-- break the path into (dirname,basename)
split'path path = let (p1,p2) = breakspan (=='/') (reverse path)
		  in (reverse p2, reverse p1)

