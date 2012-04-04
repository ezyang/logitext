module Coq where

import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Expr
import Data.Functor.Identity

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
--
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

global = identifier >> return ()
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

term = operconstr200

-- There is a more efficient, factored representation, but sprinkling
-- in try makes things much more straight-forward, and performance
-- is not a primary concern

operconstr200 = try binder_constr <|> operconstr100
operconstr100 = try (operconstr90 >> reservedOp ":" >> binder_constr)
            <|> try (operconstr90 >> reservedOp ":" >> operconstr100)
            <|> operconstr90
operconstr90 = try (operconstr10 >> reservedOp "->" >> binder_constr)
           <|> try (operconstr10 >> reservedOp "->" >> operconstr90)
           <|> operconstr10
operconstr10 = try (operconstr0 >> many1 appl_arg >> return ())
           <|> try (reservedOp "@" >> global >> many operconstr0 >> return ())
           <|> operconstr0
operconstr0 = try atomic_constr
          <|> (reservedOp "(" >> operconstr200 >> reservedOp ")")

-- lconstr: operconstr.200
lconstr = operconstr200

-- constr:
--  operconstr.8
--  "@" global
constr = try operconstr0
     <|> (reservedOp "@" >> global >> return ())

-- binder_constr:
--  "forall" open_binders "," operconstr.200
--  "fun" open_binders "=>" operconstr.200
binder_constr = try (reserved "forall" >> open_binders >> reservedOp "," >> operconstr200)
            <|> (reserved "fun" >> open_binders >> reservedOp "=>" >> operconstr200)

-- open_binders:
--  name name* ":" lconstr
--  name name* binders
--  closed_binder binders
open_binders = try (many1 name >> reservedOp ":" >> lconstr)
           <|> try (many1 name >> binders)
           <|> (closed_binder >> binders)

-- binders: binder*
binders = many binder >> return ()

-- binder:
--  name
--  closed_binder
binder = try (name >> return ())
     <|> closed_binder

-- closed_binder:
--  "(" name+ ":" lconstr ")"
closed_binder = reservedOp "(" >> many name >> reservedOp ":" >> lconstr >> reservedOp ")" >> return ()

-- appl_arg:
--  "(" lconstr ")" -- we don't need the hack yay!
--  operconstr.0
appl_arg = try (reservedOp "(" >> lconstr >> reservedOp ")")
       <|> operconstr0

-- atomic_constr:
--  global
--  sort
--  INT
atomic_constr = try global
            <|> try sort
            <|> (integer >> return ())
sort = (reserved "Prop" <|> reserved "Set" <|> reserved "Type") >> return ()

parse_sample = "or ((forall x : U, P x) -> @ex U (fun x : U => P x)) False"
main = parseTest (term >> eof) parse_sample -- parse_sample
