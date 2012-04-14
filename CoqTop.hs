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
import Control.Monad
import Text.XML.Light.Input
import Text.XML.Light
import Data.List.Split

-- You'll need ezyang's private copy of Coq https://github.com/ezyang/coq

coqtopProcess theory err = CreateProcess
    -- XXX Filepaths should be more generic...
    { cmdspec = RawCommand "/home/ezyang/Dev/coq-git/bin/coqtop.opt"
                            [ "-coqlib"
                            , "/home/ezyang/Dev/coq-git"
                            , "-l"
                            , "/home/ezyang/Dev/logitext/" ++ theory ++ ".v"
                            , "-pgip"]
    , cwd = Nothing
    , env = Nothing
    , std_in = CreatePipe
    , std_out = CreatePipe
    , std_err = UseHandle err
    , close_fds = False
    }

onlyOnce :: IO () -> IO (IO ())
onlyOnce m = do
    i <- newMVar m
    return (modifyMVar_ i (\m -> m >> return (return ())))

coqtopRaw theory = do
    putStrLn "Starting up coqtop..."
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
    putStrLn "Ready coqtop"
    -- XXX this doesn't do particularly good things if you don't
    -- pass it enough information.  Correct thing to do is on COQ
    -- side say "I want more information!"  Nor does it do good things
    -- if you give it too much information... (de-synchronization risk)
    interactVar <- newMVar (\s -> hPutStr fin (s ++ ".\n") >> readChan resultChan)
    let interact s = withMVar interactVar (\f -> f s)
    end <- onlyOnce $ do
        putStrLn "Closing coqtop..."
        killThread tout
        hClose fin
        hClose fout
        hClose err
        m <- getProcessExitCode pid
        maybe (terminateProcess pid) (const (return ())) m
        -- We're erring on the safe side here.  If no escape of coqtop
        -- from bracket is enforced, this is impossible
        modifyMVar_ interactVar (\_ -> return (error "coqtopRaw/end: coqtop is dead"))
    return (interact, end)

coqtop theory inner = bracket (coqtopRaw theory) snd (inner . fst)

{-
main =
    coqtop "ClassicalFOL" $ \f -> do
        let run s = f s >>= print >> putStrLn ""
        run "Goal True."
        run "trivial."
        run "Qed."
-}
