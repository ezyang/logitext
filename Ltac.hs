module Ltac where

import Data.List

data Expr = Seq Expr [Expr]
          -- | Progress Expr
          -- | Solve [Expr]
          | Tac String [String] -- technically should point to tacarg; we only allow qualids for now

-- Useful atomic tactics
admit :: Expr
admit = Tac "admit" []

-- This is kind of deficient for handling tacexpr_1, tacexpr_2,
-- tacexpr_3 parsing rules
instance Show Expr where
    show (Seq e1 [e2]) = show e1 ++ "; " ++ show e2
    show (Seq e es) = show e ++ "; [ " ++ intercalate " | " (map show es) ++ " ]"
    -- show (Progress e) = "progress " ++ show e
    -- show (Solve es) = "solve [" ++ intercalate "|" (map show es) ++ "]"
    show (Tac s []) = s
    -- XXX invariant: args must be appropriately parenthesized
    show (Tac s as) = s ++ " " ++ intercalate " " as
