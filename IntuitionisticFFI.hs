{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, ScopedTypeVariables, DeriveDataTypeable #-}

module IntuitionisticFFI where

import Foreign
import Foreign.C.String

import Prelude hiding (catch)
import Intuitionistic

import CommonFFI

uw_Haskell_parseIntuitionistic :: Ptr UrwebContext -> CString -> IO CString
uw_Haskell_parseIntuitionistic ctx s = serialize ctx (parseSequent =<< peekUTF8String s)

foreign export ccall uw_Haskell_parseIntuitionistic :: Ptr UrwebContext -> CString -> IO CString
