{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, ScopedTypeVariables, DeriveDataTypeable #-}

module ClassicalFOLFFI where

import Prelude hiding (catch)
import ClassicalFOL
import qualified Data.ByteString as S
import qualified Data.ByteString.Unsafe as S
import qualified Data.ByteString.Lazy as L
import Foreign.Marshal.Utils
import Foreign
import Foreign.C.String
import Data.Data
import Control.Exception
import Control.Monad
import System.IO
import qualified Data.ByteString.UTF8 as U
import GHC.Conc
import qualified Data.Aeson.Encode as E

import JSONGeneric

data UrwebContext

data Result a = EndUserFailure EndUserFailure
              | InternalFailure String
              | Success a
    deriving (Data, Typeable)

-- here's how you parse this: first, you try parsing using
-- the expected result type.  If that doesn't work, try parsing
-- using EndUserFailure.  And then finally, parse as string.
-- XXX this doesn't work if we have something that legitimately
-- needs to return a string, although we can force fix that
-- by adding a wrapper...
result m =
    liftM Success m `catches`
        [ Handler (return . EndUserFailure)
        , Handler (return . InternalFailure . (show :: SomeException -> String))
        ]

-- incoming string doesn't have to be Haskell managed
-- outgoing string is on Urweb allocated memory, and
-- is the unique outgoing one
serialize ctx m = lazyByteStringToUrWebCString ctx . E.encode . toJSON =<< result m

-- (f =<< peekUTF8String cs)

initFFI :: IO ()
initFFI = evaluate theCoq >> return ()

startFFI :: Ptr UrwebContext -> CString -> IO CString
startFFI ctx s = serialize ctx (start =<< peekUTF8String s)

parseUniverseFFI :: Ptr UrwebContext -> CString -> IO CString
parseUniverseFFI ctx s = serialize ctx (parseUniverse =<< peekUTF8String s)

peekUTF8String = liftM U.toString . S.packCString

refineFFI :: Ptr UrwebContext -> CString -> IO CString
refineFFI ctx s = serialize ctx $ do
    bs <- S.packCString s
    r <- maybe (error "ClassicalFOLFFI.refineFFI") return (decode (L.fromChunks [bs]))
    refine r

lazyByteStringToUrWebCString ctx bs = do
    -- XXX S.concat is really bad! Bad Edward!
    S.unsafeUseAsCStringLen (S.concat (L.toChunks bs)) $ \(c,n) -> do
        x <- uw_malloc ctx (n+1)
        copyBytes x c n
        poke (plusPtr x n) (0 :: Word8)
        return x
    {- This is the right way to do it, which doesn't
     - involve copying everything, but it might be overkill
    -- XXX This would be a useful helper function for bytestring to have.
    let l = fromIntegral (L.length bs' + 1) -- XXX overflow
    x <- uw_malloc ctx l
    let f x c = ...
    foldlChunks f x
    -}

foreign export ccall refineFFI :: Ptr UrwebContext -> CString -> IO CString
foreign export ccall startFFI :: Ptr UrwebContext -> CString -> IO CString
foreign export ccall parseUniverseFFI :: Ptr UrwebContext -> CString -> IO CString
foreign export ccall initFFI :: IO ()

foreign import ccall "urweb.h uw_malloc"
    uw_malloc :: Ptr UrwebContext -> Int -> IO (Ptr a)

foreign export ccall ensureIOManagerIsRunning :: IO ()
