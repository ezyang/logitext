{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, ScopedTypeVariables, DeriveDataTypeable #-}

module LinearFFI where

import Foreign
import Foreign.C.String

import Prelude hiding (catch)
import Linear

import CommonFFI

uw_Haskell_parseLinear :: Ptr UrwebContext -> CString -> IO CString
uw_Haskell_parseLinear ctx s = serialize ctx (parseSequent =<< peekUTF8String s)

foreign export ccall uw_Haskell_parseLinear :: Ptr UrwebContext -> CString -> IO CString
