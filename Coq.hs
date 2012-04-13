{-# LANGUAGE RankNTypes, TupleSections #-}

module Coq (
      Term(..)
    , Binder
    , Name
    , Sort(..)
    , term
    , parseTerm
    , CoqTerm(..)
    , render
    ) where

import Control.Applicative hiding ((<|>), many)
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (emptyDef)
import Data.Functor.Identity
import Data.List hiding (sort)

coqStyle :: P.LanguageDef st
coqStyle = emptyDef
                { P.commentStart    = "(*"
                , P.commentEnd      = "*)"
                , P.nestedComments  = True
                , P.identStart      = letter <|> oneOf "_"
                , P.identLetter     = alphaNum <|> oneOf "_'"
                -- Ops are sloppy, but should work OK for our use case.
                -- There might be a bug here.
                , P.opStart         = P.opLetter coqStyle
                , P.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
                -- Lifted straight out of the manual
                , P.reservedOpNames =
                    ["!","%","&","&&","(","()",")",
                    "*","+","++",",","-","->",".",
                    ".(","..","/","/\\",":","::",":<",
                    ":=",":>",";","<","<-","<->","<:",
                    "<=","<>","=","=>","=_D",">",">->",
                    ">=","?","?=","@","[","\\/","]",
                    "^","{","|","|-","||","}","~"]
                , P.reservedNames   =
                    ["_","as","at","cofix","else","end",
                    "exists","exists2","fix","for","forall","fun",
                    "if","IF","in","let","match","mod",
                    "Prop","return","Set","then","Type","using",
                    "where","with"]
                , P.caseSensitive   = True
                }

lexer = P.makeTokenParser coqStyle

reserved   = P.reserved lexer
identifier = P.identifier lexer
reservedOp = P.reservedOp lexer
integer    = P.integer lexer
whiteSpace = P.whiteSpace lexer

-- http://coq.inria.fr/doc/Reference-Manual003.html

-- Here is the restricted BNF we will support:
--
--  term ::= forall binders , term
--         | fun binders => term
--         | term : term
--         | term -> term
--         | term arg ... arg
--         | @ qualid term ... term
--         | qualid
--         | sort
--         | num
--  arg ::= term
--  binders ::= binder .. binder
--  binder ::= name | ( name ... name : term )
--  name ::= ident
--  qualid ::= ident
--  sort ::= Prop | Set | Type

data Term = Forall [Binder] Term
          | Fun [Binder] Term
          | Typed Term Term -- extra info
          | Imp Term Term
          | App Term [Term]
          | Sort Sort
          | Num Integer
          | Atom Name
    deriving (Show, Eq)

render :: Term -> String
render (Forall bs t) = "(forall " ++ renderBinders bs ++ ", " ++ render t ++ ")"
render (Fun bs t) = "(fun " ++ renderBinders bs ++ " => " ++ render t ++ ")"
render (Typed t t') = "(" ++ render t ++ " : " ++ render t' ++ ")"
render (Imp t t') = "(" ++ render t ++ " -> " ++ render t' ++ ")"
render (App t ts) = "(" ++ render t ++ " " ++ intercalate " " (map render ts) ++ ")"
render (Sort Prop) = "Prop"
render (Sort Set) = "Set"
render (Sort Type) = "Type"
render (Num i) = show i
render (Atom n) = n

renderBinders :: [Binder] -> String
renderBinders [] = error "renderBinders: empty binder"
renderBinders [(n, t)] = "(" ++ n ++ ":" ++ render t ++ ")"
renderBinders (x:xs) = renderBinders [x] ++ " " ++ renderBinders xs -- XXX code reuse at its finest

-- We require the types of our binders!  If you Set Printing All you
-- should get them.
type Binder = (Name, Term)
type Name = String -- qualid's are squashed in here
data Sort = Prop | Set | Type
    deriving (Show, Eq)

-- But the BNF is not enough to actually properly parse...
-- (precedences?)
--
-- Fortunately, we already have a nice converted definition in
-- parsing/g_constr.ml4.  They also have some batshit weird interaction
-- between their infix and prefix operators, so we don't use Parsec's
-- nice table support.
--
-- Levels are pretty important to understanding g_constr.ml4; there is a
-- good treatment here:
-- http://caml.inria.fr/pub/docs/tutorial-camlp4/tutorial003.html
-- Notationally, operconstr.90 === operconstr LEVEL 90; we've translated
-- all of the NEXT and SELF identifiers.
--
-- We had to manually resolve some levels, so if you add more levels you
-- will need to fix them.

type P a = forall u. ParsecT String u Identity a

global :: P Term
global = Atom <$> identifier

name :: P String
name = identifier

-- operconstr:
--  200 RIGHTA binder_constr
--  100 RIGHTA operconstr.90 ":" binder_constr
--             operconstr.90 ":" operconstr.100
--   90 RIGHTA operconstr.10 "->" binder_constr
--             operconstr.10 "->" operconstr.90
--   10 LEFTA  operconstr.0 appl_arg+ // this one might be wrong
--             "@" global operconstr.0*
--    0        atomic_constr
--             "(" operconstr.200 ")"

term :: P Term
term = operconstr200

-- There is a more efficient, left-factored representation for many of
-- these rules, and some of the tries are not necessary, but sprinkling
-- in try makes it easier to tell that things are correct, and
-- performance is not a primary concern.  If you're curious what the
-- left-factored representation looks like, see Coq_efficient.hs

operconstr200, operconstr100, operconstr90, operconstr10, operconstr0 :: P Term
operconstr200 = try binder_constr <|> operconstr100
operconstr100 = try (Typed <$> operconstr90 <* reservedOp ":" <*> binder_constr)
            <|> try (Typed <$> operconstr90 <* reservedOp ":" <*> operconstr100)
            <|> operconstr90
operconstr90 = try (Imp <$> operconstr10 <* reservedOp "->" <*> binder_constr)
           <|> try (Imp <$> operconstr10 <* reservedOp "->" <*> operconstr90)
           <|> operconstr10
operconstr10 = try (App <$> operconstr0 <*> many1 appl_arg)
          -- XXX dropping the @ cuz we're lazy
           <|> try (reservedOp "@" >> App <$> global <*> many operconstr0)
           <|> operconstr0
operconstr0 = try atomic_constr
          <|> reservedOp "(" *> operconstr200 <* reservedOp ")"

-- lconstr: operconstr.200
lconstr :: P Term
lconstr = operconstr200

-- constr:
--  operconstr.8
--  "@" global
constr :: P Term
constr = try operconstr0
     <|> (reservedOp "@" >> Atom . ('@':) <$> identifier)

-- binder_constr:
--  "forall" open_binders "," operconstr.200
--  "fun" open_binders "=>" operconstr.200
binder_constr :: P Term
binder_constr = try (reserved "forall" >> Forall <$> open_binders <* reservedOp "," <*> operconstr200)
            <|> (reserved "fun" >> Fun <$> open_binders <* reservedOp "=>" <*> operconstr200)

-- open_binders:
--  name name* ":" lconstr
--  name name* binders
--  closed_binder binders
msBinder ns t = map (,t) ns
open_binders :: P [Binder]
open_binders = try (msBinder <$> many1 name <* reservedOp ":" <*> lconstr)
           <|> ((++) <$> closed_binder <*> binders)

-- binders: binder*
binders :: P [Binder]
binders = concat <$> many binder

-- binder:
--  closed_binder
binder :: P [Binder]
binder = closed_binder

-- closed_binder:
--  "(" name+ ":" lconstr ")"
closed_binder :: P [Binder]
closed_binder = reservedOp "(" >> msBinder <$> many name <* reservedOp ":" <*> lconstr <* reservedOp ")"

-- appl_arg:
--  "(" lconstr ")" -- we don't need the hack yay!
--  operconstr.0
appl_arg = try (reservedOp "(" >> lconstr <* reservedOp ")")
       <|> operconstr0

-- atomic_constr:
--  global
--  sort
--  INT
atomic_constr :: P Term
atomic_constr = try global
            <|> try (Sort <$> sort)
            <|> Num <$> integer
sort :: P Sort
sort = Prop <$ reserved "Prop" <|> Set <$ reserved "Set" <|> Type <$ reserved "Type"

parse_sample = "or ((forall x : U, P x) -> @ex U (fun x : U => P x)) False"
sample = parse (term <* eof) "" parse_sample

parseTerm = parse (whiteSpace >> term <* eof) ""

-- XXX can haz test please (do it before you make changes)

class CoqTerm a where
    toCoq :: a -> Term
    fromCoq :: Term -> a
