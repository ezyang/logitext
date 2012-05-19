{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, ScopedTypeVariables #-}

module ClassicalFOLFFI where

import Prelude hiding (catch)
import ClassicalFOL
import qualified Data.ByteString as S
import qualified Data.ByteString.Unsafe as S
import qualified Data.ByteString.Lazy as L
import Foreign.Marshal.Utils
import Foreign
import Foreign.C.String
import Control.Exception
import Control.Monad
import System.IO
import qualified Data.ByteString.UTF8 as U
import GHC.Conc

data UrwebContext

catchToNull m =
    m `catch` (\(e :: SomeException) -> hPutStrLn stderr (show e) >> return nullPtr)

-- incoming string doesn't have to be Haskell managed
-- outgoing string is on Urweb allocated memory, and
-- is the unique outgoing one
wrapper f = \ctx cs -> catchToNull (peekUTF8String cs >>= startString >>= lazyByteStringToUrWebCString ctx)

initFFI :: IO ()
initFFI = evaluate theCoq >> return ()

startFFI :: Ptr UrwebContext -> CString -> IO CString
startFFI = wrapper startString

parseUniverseFFI :: Ptr UrwebContext -> CString -> IO CString
parseUniverseFFI = wrapper parseUniverseString

peekUTF8String = liftM U.toString . S.packCString

refineFFI :: Ptr UrwebContext -> CString -> IO CString
refineFFI ctx s = catchToNull $ do
    -- bs must not escape from this function
    bs <- S.packCString s
    r <- refineString (L.fromChunks [bs])
    lazyByteStringToUrWebCString ctx r

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
