module Ltac where

import Data.List

data Expr = Seq Expr Expr
          -- | Progress Expr
          -- | Solve [Expr]
          | Atom String -- technically could be qualid, not worrying about that for now
                        -- also, exists distinction between this and atomic tactic
          | App String [String] -- technically should point to tacarg; we only allow qualids for now

-- Useful atomic tactics
admit = Atom "admit"

-- This is kind of deficient for handling tacexpr_1, tacexpr_2,
-- tacexpr_3 parsing rules
instance Show Expr where
    show (Seq e1 e2) = show e1 ++ "; " ++ show e2
    -- show (Progress e) = "progress " ++ show e
    -- show (Solve es) = "solve [" ++ intercalate "|" (map show es) ++ "]"
    show (Atom s) = s
    show (App s as) = s ++ " " ++ intercalate " " as

-- example = Seq (App "lDisj" ["Hyp3"]) (Solve [App "rTop" ["Con0"]])
