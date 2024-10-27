
{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.IO.Parser.Expression
-- Description : parsing expressions.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- parsing expressions.
module OAlg.Homology.IO.Parser.Expression
  ( prsExpression
  , Expression(..), Command(..), ComplexId(..)
  ) where

import Prelude hiding (Word,(!!),repeat)

import Control.Applicative

import Data.Char

import OAlg.Data.Canonical
import OAlg.Data.Number

import OAlg.Homology.ChainComplex (Regular(..))

import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Term
import OAlg.Homology.IO.Value

import OAlg.Homology.IO.Parser.Definition
import OAlg.Homology.IO.Parser.Lexer

--------------------------------------------------------------------------------
-- keys -

-- | the keys for expressions.
keys :: Keys
keys = Keys comment alphas symbols where
  alphas :: [String]
  alphas
    = [ "let", "in", "ext"
      , "A", "B", "C", "H", "K"
      , "h", "d", "d'"
      ]
  
  -- | the symbols.
  symbols :: [String]
  symbols
    = [ "(",")"
      , ":quit", ":q" 
      , ":help", ":h", ":?"
      , ":load", ":l"
      , "+","-", "!"
      , "=", "#"
      ]
  
  -- | the comment-symbol string. Everything after this symbol will be ignored by the lexer until
  --   the end of line.
  comment :: String
  comment = "//"

--------------------------------------------------------------------------------
-- Load -

data ComplexId
  = EmptyComplex
  | KleinBottle
  | Sphere N
  deriving (Show)
--------------------------------------------------------------------------------
-- Command -

data Command x
  = Quit
  | Help
  | Load Regular ComplexId
  | Let String (TermValue x)
  deriving (Show)

--------------------------------------------------------------------------------
-- Expression -

data Expression x
  = Empty
  | Command (Command x)
  | TermValue (TermValue x)
  deriving (Show)
           
--------------------------------------------------------------------------------
-- OprVec -

data OprVec = Add | Sub | SMlt deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- oprVec -

oprVec :: Parser OprVec
oprVec = do
  ts <- getTokens
  case fmap fst ts of
    []           -> empty
    Symbol o : _ -> case o of
      "+"        -> setTokens (tail ts) >> return Add
      "-"        -> setTokens (tail ts) >> return Sub
      "!"        -> setTokens (tail ts) >> return SMlt
      _          -> empty
    _            -> empty -- failure $ Just $ UnexpectedToken $ head ts

--------------------------------------------------------------------------------
-- prcVec -

prcVec :: OprVec -> Z
prcVec Add  = 0
prcVec Sub  = 0
prcVec SMlt = 1

--------------------------------------------------------------------------------
-- applVec -

applVec :: OprVec -> TermValue x -> TermValue x -> TermValue x
applVec Add a  = Opr Addition a
applVec Sub a  = \b -> Opr Addition a (Opr ScalarMultiplication (Value (ZValue (-1))) b)
applVec SMlt a = Opr ScalarMultiplication a

--------------------------------------------------------------------------------
-- linearCombination -

linearCombination :: Parser (TermValue x) -> Parser (TermValue x)
linearCombination = infixesl oprVec prcVec applVec

--------------------------------------------------------------------------------
-- unexpected -

unexpected :: Parser a
unexpected = getTokens >>= failure . Just . UnexpectedToken . head  

--------------------------------------------------------------------------------
-- quit -

quit :: Parser (Command x)
quit = symbol ":quit" <|> symbol ":q" >> return Quit

--------------------------------------------------------------------------------
-- help -

help :: Parser (Command x)
help = symbol ":help" <|> symbol ":h" <|> symbol ":?" >> return Help


--------------------------------------------------------------------------------
-- varbind -

varbind :: Parser (Command x)
varbind
  =   key "let" >> (ident !! ExpectedIdent)
  >>= \x -> (symbol "=" !! ExpectedToken (Symbol "=")) >> (value !! Expected "value")
  >>= \v -> end empty (Let x v)

--------------------------------------------------------------------------------
-- letdecl -

letdecl :: Parser (TermValue x)
letdecl
  =   key "let" >> (ident !! ExpectedIdent)
  >>= \x -> (symbol "=" !! ExpectedToken (Symbol "=")) >> (value !! Expected "value")
  >>= \v -> (key "in" !! ExpectedToken (Key "in")) >> (value !! Expected "value")
  >>= \w -> return (abstracts [x] w :!> v)

--------------------------------------------------------------------------------
-- loadEmpty -

loadEmpty :: Parser ComplexId
loadEmpty = do
  "empty" <- ident
  return EmptyComplex
  
--------------------------------------------------------------------------------
-- loadKleinBottle -

loadKleinBottle :: Parser ComplexId
loadKleinBottle = do
  "kleinBottle" <- ident
  return KleinBottle

--------------------------------------------------------------------------------
-- loadSphere -

loadSphere :: Parser ComplexId
loadSphere = do
  "sphere" <- ident
  n        <- num !! Expected "mumber"
  return (Sphere n)

--------------------------------------------------------------------------------
-- extended -

extended :: Parser Regular
extended = key "ext" >> return Extended
   
--------------------------------------------------------------------------------
-- load -

load :: Parser (Command x)
load = (symbol ":load" <|> symbol ":l")
    >> (   (extended <|> return Regular)
       >>= \r -> (loadEmpty <|> loadKleinBottle <|> loadSphere)
           >>= return . Load r
       )  
       
--------------------------------------------------------------------------------
-- command -

command :: Parser (Command x)
command = quit <|> help <|> load <|> varbind

--------------------------------------------------------------------------------
-- num -

num :: Parser N
num = do
  ts <- getTokens
  case map fst ts of
    Id n :_ | isNum n -> setTokens (tail ts) >> (return $ fromInteger $ read n)
    _                 -> empty
  where isNum ds@(_:_) = and $ map ((DecimalNumber==) . generalCategory) ds
        isNum _        = False

--------------------------------------------------------------------------------
-- sig -

sig :: Parser Z
sig = do
  ts <- getTokens
  case map fst ts of
    Symbol "-" :_ -> setTokens (tail ts) >> return (-1)
    Symbol "+" :_ -> setTokens (tail ts) >> return 1
    _             -> empty

--------------------------------------------------------------------------------
-- value -

value :: Parser (TermValue x)
value = linearCombination sigTerm

--------------------------------------------------------------------------------
-- sigTerm -

sigTerm :: Parser (TermValue x)
sigTerm = do
  s <- repeat sig
  case foldl (*) 1 s of
    -1 -> term >>= return . Opr (!) (Value $ ZValue (-1))
    _  -> term
  where (!) = ScalarMultiplication

--------------------------------------------------------------------------------
-- term -

term :: Parser (TermValue x)
term = letdecl <|> application

--------------------------------------------------------------------------------
-- application -

application :: Parser (TermValue x)
application = atom >>= \a -> repeat atom >>= \as -> return (applys a as)

--------------------------------------------------------------------------------
-- atom -

atom :: Parser (TermValue x)
atom 
   =  (key "A" >> return (Free "A"))
  <|> (key "B" >> return (Free "B"))
  <|> (key "C" >> return (Free "C"))
  <|> (key "H" >> return (Free "H"))
  <|> (key "K" >> return (Free "K"))
  <|> (key "d" >> return (Free "d"))
  <|> (key "d'" >> return (Free "d'"))
  <|> (key "h" >> return (Free "h"))
  <|> (symbol "#" >> return (Free "#"))
  <|> fmap (Value . ZValue . inj) num
  <|> fmap Free ident
  <|> bracket value

--------------------------------------------------------------------------------
-- expression -

expression :: Parser (Expression x)
expression
  =   end empty Empty
  <|> (command >>= return . Command)
  <|> (value >>= return . TermValue)
  >>= end unexpected

--------------------------------------------------------------------------------
-- prsExpression -

prsExpression :: String -> Either ParserFailure (Expression x)
prsExpression = parse keys expression

