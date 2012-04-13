{-# LANGUAGE ForeignFunctionInterface #-}

module ClassicalFOLFFI where

import ClassicalFOL

foo = return ()
foreign export ccall foo :: IO ()
