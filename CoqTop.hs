{-# LANGUAGE RankNTypes, NoMonomorphismRestriction, ScopedTypeVariables #-}

module CoqTop
    ( coqtop
    , coqtopRaw
    ) where

import Prelude hiding (catch)
import System.IO
import System.Process
import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Exception
import Text.XML.Light.Input
import Text.XML.Light
import Data.List.Split

-- You'll need ezyang's private copy of Coq https://github.com/ezyang/coq

coqtopProcess :: String -> Handle -> CreateProcess
coqtopProcess theory err = CreateProcess
    { cmdspec = RawCommand "coqtop"
                            [ "-boot"
                            , "-l"
                            , theory ++ ".v"
                            , "-pgip"]
    , cwd = Nothing
    , env = Nothing
    , std_in = CreatePipe
    , std_out = CreatePipe
    , std_err = UseHandle err
    , close_fds = False
    , create_group = False
    }

onlyOnce :: IO () -> IO (IO ())
onlyOnce m = do
    i <- newMVar m
    return (modifyMVar_ i (\x -> x >> return (return ())))

coqtopRaw :: String -> IO (String -> IO [Content], IO ())
coqtopRaw theory = do
    --hPutStrLn stderr "Starting up coqtop..."
    -- XXX We're not really doing good things with warnings.
    -- Fortunately, fatal errors DO get put on stdout.
    err <- openFile "/dev/null" WriteMode -- XXX gimme a platform independent version!
    (Just fin, Just fout, _, pid) <- createProcess (coqtopProcess theory err)
    hSetBuffering fin LineBuffering
    hSetBuffering fout LineBuffering -- should be good enough to pick up on <ready/>
    resultChan <- newChan
    -- XXX do we really want to give them the <ready/> marker? (elim
    -- keepDelimsR if not)
    tout <- forkIO $
        -- Lazy IO at its finest
        let p (Elem e) | qName (elName e) == "ready" = True
            p _ = False
        in writeList2Chan resultChan . split (keepDelimsR (whenElt p)) =<< parseXML `fmap` hGetContents fout
    _ <- readChan resultChan -- read out the intro message
    --hPutStrLn stderr "Ready coqtop"
    -- XXX this doesn't do particularly good things if you don't
    -- pass it enough information.  Correct thing to do is on COQ
    -- side say "I want more information!"  Nor does it do good things
    -- if you give it too much information... (de-synchronization risk)
    interactVar <- newMVar (\s -> {- hPutStrLn stderr s >> -} hPutStr fin (s ++ ".\n") >> readChan resultChan)
    let run s = withMVar interactVar (\f -> f s)
    end <- onlyOnce $ do
        -- hPutStrLn stderr "Closing coqtop..."
        killThread tout
        hClose fin
        hClose fout
        hClose err
        m <- getProcessExitCode pid
        maybe (terminateProcess pid) (const (return ())) m
        -- We're erring on the safe side here.  If no escape of coqtop
        -- from bracket is enforced, this is impossible
        modifyMVar_ interactVar (\_ -> return (error "coqtopRaw/end: coqtop is dead"))
    return (run, end)

coqtop :: String -> ((String -> IO [Content]) -> IO a) -> IO a
coqtop theory inner = bracket (coqtopRaw theory) snd (inner . fst)
