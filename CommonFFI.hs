{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, ScopedTypeVariables, DeriveDataTypeable, GADTs #-}

module CommonFFI where

import Prelude hiding (catch)
import qualified Data.ByteString as S
import qualified Data.ByteString.Unsafe as S
import qualified Data.ByteString.Lazy as L
import Foreign.Marshal.Utils
import Foreign
import Foreign.C.String
import Data.Data
import Control.Exception
import Control.Monad
import qualified Data.ByteString.UTF8 as U
import qualified Data.Aeson.Encode as E
import GHC.Conc

import JSONGeneric
import Common

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
result :: IO a -> IO (Result a)
result m =
    liftM Success m `catches`
        [ Handler (return . EndUserFailure)
        , Handler (return . InternalFailure . (show :: SomeException -> String))
        ]

-- incoming string doesn't have to be Haskell managed
-- outgoing string is on Urweb allocated memory, and
-- is the unique outgoing one
serialize :: Data a => Ptr UrwebContext -> IO a -> IO CString
serialize ctx m = lazyByteStringToUrWebCString ctx . E.encode . toJSON =<< result m

peekUTF8String :: CString -> IO String
peekUTF8String = liftM U.toString . S.packCString

lazyByteStringToUrWebCString :: Ptr UrwebContext -> L.ByteString -> IO CString
lazyByteStringToUrWebCString ctx bs = do
    let s = S.concat (L.toChunks bs)
    -- XXX S.concat is really bad! Bad Edward!
    S.unsafeUseAsCStringLen s $ \(c,n) -> do
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

foreign import ccall "urweb.h uw_malloc"
    uw_malloc :: Ptr UrwebContext -> Int -> IO (Ptr a)

foreign export ccall ensureIOManagerIsRunning :: IO ()
