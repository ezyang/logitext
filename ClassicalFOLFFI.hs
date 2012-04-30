{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls #-}

module ClassicalFOLFFI where

import ClassicalFOL
import Data.ByteString as S
import Data.ByteString.Unsafe
import qualified Data.ByteString.Lazy as L
import Foreign.Marshal.Utils
import Foreign
import Foreign.C.String
import GHC.Conc

data UrwebContext

startFFI :: Ptr UrwebContext -> CString -> IO CString
startFFI ctx cs = do
    s <- peekCAString cs
    r <- startString s
    lazyByteStringToUrWebCString ctx r

-- incoming string doesn't have to be Haskell managed
-- outgoing string is on Urweb allocated memory, and
-- is the unique outgoing one
refineFFI :: Ptr UrwebContext -> CString -> IO CString
refineFFI ctx s = do
    -- bs must not escape from this function
    bs <- packCString s
    r <- refineString (L.fromChunks [bs])
    case r of
     Nothing -> return nullPtr
     Just bs' -> lazyByteStringToUrWebCString ctx bs'

lazyByteStringToUrWebCString ctx bs = do
    -- XXX S.concat is really bad! Bad Edward!
    unsafeUseAsCStringLen (S.concat (L.toChunks bs)) $ \(c,n) -> do
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

foreign import ccall "urweb.h uw_malloc"
    uw_malloc :: Ptr UrwebContext -> Int -> IO (Ptr a)

foreign export ccall ensureIOManagerIsRunning :: IO ()
