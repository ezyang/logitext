{-# LANGUAGE DeriveDataTypeable #-}

module Common where

import Control.Exception
import Data.Typeable
import Data.Data

-- A EndUserFailure corresponds to user error; anything other exceptions
-- are our fault
data EndUserFailure = UpdateFailure | ParseFailure
    deriving (Typeable, Show, Data)
instance Exception EndUserFailure
