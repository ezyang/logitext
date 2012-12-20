{-# LANGUAGE GADTs, EmptyDataDecls, KindSignatures, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, DeriveFunctor, NoMonomorphismRestriction, ViewPatterns, RankNTypes #-}

module Linear where

import Prelude hiding (catch)
import Data.Typeable
import Data.Functor.Identity
import Data.Data hiding (Prefix,Infix)
import Control.Applicative hiding ((<|>),many)
import Control.Exception hiding (try)
-- import Debug.Trace

-- XXX super namespace collision!
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (emptyDef)

import Common

errorModule :: String -> a
errorModule s = error ("Linear." ++ s)

-- Sequent
data S = S { persistent :: [L], ephemeral :: [L], goal :: L }
    deriving (Show, Eq, Data, Typeable)

-- All of these are *linear* variants (this is reflected syntactically)
data L = Prop String
       | Conj L L
       | Disj L L
       | Imp L L
       | Bang L
       | Top
       | Bot
    deriving (Show, Eq, Data, Typeable)

-- Parsing

userParseError :: Either e a -> IO a
userParseError = either (\_ -> throwIO ParseFailure) return

parseSequent :: String -> IO S
parseSequent g = userParseError $ parse (whiteSpace >> sequent <* eof) "goal" g

linearStyle, linearStyleUpper, linearStyleLower :: P.LanguageDef st
linearStyle = emptyDef
                { P.commentStart    = "(*"
                , P.commentEnd      = "*)"
                , P.nestedComments  = True
                , P.identStart      = letter <|> oneOf "_"
                , P.identLetter     = alphaNum <|> oneOf "_'"
                -- Ops are sloppy, but should work OK for our use case.
                , P.opStart         = P.opLetter linearStyle
                , P.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~,"
                , P.reservedOpNames =
                    ["(", ")", ",", ";",
                    "-o", "⊸",
                    "!",
                    "&",
                    "?&", "⅋", -- what is conventional?
                    "+", "⊕",
                    "*", "⊗",
                    -- "/\\","∧",
                    -- "\\/","∨",
                    "|-","⊢"
                    -- "~","¬"
                    ]
                , P.reservedNames   =
                    [
                    "True","False","⊤","⊥",
                    "and", "or", "ex", "iff", "not"
                    ]
                , P.caseSensitive   = True
                }
linearStyleUpper = linearStyle {P.identStart = upper}
linearStyleLower = linearStyle {P.identStart = lower}

lexer, lexerUpper, lexerLower :: P.GenTokenParser String u Identity
lexer = P.makeTokenParser linearStyle
lexerUpper = P.makeTokenParser linearStyleUpper
lexerLower = P.makeTokenParser linearStyleLower

type Parser a = forall u. ParsecT String u Identity a
reserved :: String -> Parser ()
reserved   = P.reserved lexer
upperIdentifier :: Parser String
upperIdentifier = P.identifier lexerUpper
lowerIdentifier :: Parser String
lowerIdentifier = P.identifier lexerLower
reservedOp :: String -> Parser ()
reservedOp = P.reservedOp lexer
integer :: Parser Integer
integer    = P.integer lexer
whiteSpace :: Parser ()
whiteSpace = P.whiteSpace lexer
parens :: ParsecT String u Identity a -> ParsecT String u Identity a
parens     = P.parens lexer
comma :: Parser String
comma      = P.comma lexer
commaSep :: ParsecT String u Identity a -> ParsecT String u Identity [a]
commaSep   = P.commaSep lexer
commaSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
commaSep1  = P.commaSep1 lexer
lexeme :: ParsecT String u Identity a -> ParsecT String u Identity a
lexeme     = P.lexeme lexer

-- term ::= term /\ term
--          term \/ term
--          ~ term
--          True
--          False
--          identifier (universe , ... universe)
--
-- also Unicode supported, so that copypasta works

sequent :: Parser S
sequent = try (S <$> commaSep expr <* choice [reservedOp ";"] <*> commaSep expr <* choice [reservedOp "|-", reservedOp "⊢" ] <*> expr)
       <|> try (S <$> commaSep expr <*> return [] <* choice [reservedOp "|-", reservedOp "⊢" ] <*> expr)
       <|> try (S [] [] <$> expr)
       <?> "sequent"

table :: [[Operator String u Identity L]]
table   = [ [binary "/\\" Conj AssocLeft, binary "∧" Conj AssocLeft ]
          , [binary "\\/" Disj AssocLeft, binary "∨" Disj AssocLeft ]
          , [binary "->" Imp AssocRight, binary "→" Imp AssocRight ]
          ]

binary :: String -> (a -> a -> a) -> Assoc -> Operator String u Identity a
binary  name fun assoc = Infix (do{ reservedOp name; return fun }) assoc
prefix, postfix :: String -> (a -> a) -> Operator String u Identity a
prefix  name fun       = Prefix (do{ reservedOp name; return fun })
postfix name fun       = Postfix (do{ reservedOp name; return fun })

expr :: Parser L
expr    = buildExpressionParser table term
       <?> "expression"

term :: Parser L
term    =  try (parens expr)
       <|> try (Top <$ choice [reserved "True", reserved "⊤"])
       <|> try (Bot <$ choice [reserved "False", reserved "⊥"])
       <|> try (Prop <$> upperIdentifier)
       <?> "simple expression"
