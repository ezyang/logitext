{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, ScopedTypeVariables, DeriveDataTypeable #-}

module ClassicalFOLFFI where

import Prelude hiding (catch)
import qualified Data.ByteString as S
import qualified Data.ByteString.Lazy as L
import Foreign
import Foreign.C.String
import Control.Exception
import Control.Concurrent

import ClassicalFOL
import JSONGeneric
import CommonFFI

_uw_Haskell_initClassicalFOL :: IO ()
_uw_Haskell_initClassicalFOL = forkIO (evaluate theCoq >> return ()) >> return ()

uw_Haskell_startClassicalFOL :: Ptr UrwebContext -> CString -> IO CString
uw_Haskell_startClassicalFOL ctx s = serialize ctx (start =<< peekUTF8String s)

uw_Haskell_parseUniverseClassicalFOL :: Ptr UrwebContext -> CString -> IO CString
uw_Haskell_parseUniverseClassicalFOL ctx s = serialize ctx (parseUniverse =<< peekUTF8String s)

uw_Haskell_refineClassicalFOL :: Ptr UrwebContext -> CString -> IO CString
uw_Haskell_refineClassicalFOL ctx s = serialize ctx $ do
    bs <- S.packCString s
    r <- maybe (error "ClassicalFOLFFI.uw_Haskell_refineClassicalFOL") return (decode (L.fromChunks [bs]))
    refine r

foreign export ccall uw_Haskell_refineClassicalFOL :: Ptr UrwebContext -> CString -> IO CString
foreign export ccall uw_Haskell_startClassicalFOL :: Ptr UrwebContext -> CString -> IO CString
foreign export ccall uw_Haskell_parseUniverseClassicalFOL :: Ptr UrwebContext -> CString -> IO CString
foreign export ccall _uw_Haskell_initClassicalFOL :: IO ()
