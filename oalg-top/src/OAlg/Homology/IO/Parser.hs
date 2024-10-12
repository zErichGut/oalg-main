
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
-- Module      : OAlg.Homology.IO.Parser
-- Description : parsing
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- parsing
module OAlg.Homology.IO.Parser
  ( -- * Parser
     parse, ParserFailure(..)
     -- * Expression
  , Expression(..), Command(..)
   ) where

import Control.Applicative

import OAlg.Control.Exception

import OAlg.Homology.IO.ActionM
import OAlg.Homology.IO.Lexer
import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Term

--------------------------------------------------------------------------------
-- Command -

data Command
  = Quit
  | Help
  deriving (Show)

--------------------------------------------------------------------------------
-- Expression -

data Expression x
  = Command Command
  | TermValue (TermValue x)
  deriving (Show)
           
--------------------------------------------------------------------------------
-- ParserFailure -

data ParserFailure
  = UnexpectedToken (Token,Integer)
  | LexerFailure LexerFailure
  deriving (Show)

--------------------------------------------------------------------------------
-- Parser -

type Parser = ActionE [(Token,Integer)] ParserFailure

--------------------------------------------------------------------------------
-- prsCommand -

-- | pre: the underlying state is not empty.
prsCommand :: Parser (Expression x)
prsCommand = do
  ts <- getState
  case map fst ts of
    [Symbol ":",t] -> case t of
      Id "quit"     -> return $ Command Quit
      Id "q"        -> return $ Command Quit
      Id "help"     -> return $ Command Help
      Id "h"        -> return $ Command Help
      Symbol "?"    -> return $ Command Help
      _             -> empty
    _               -> empty

--------------------------------------------------------------------------------
-- prsFree -

prsFree :: Parser (Expression x)
prsFree = do
  ts <- getState
  case ts of
    (Id v,_):ts' -> setState ts' >> (return $ TermValue $ Free v)
    _            -> empty
    
--------------------------------------------------------------------------------
-- prsTermValue -

-- | pre: the underlying state is not empty.
prsTermValue :: Parser (Expression x)
prsTermValue = prsFree

--------------------------------------------------------------------------------
-- unexpectedToken -

-- | pre: the underlying state is not empty.
unexpectedToken :: Parser a
unexpectedToken = do
  ts <- getState
  failure $ Just $ UnexpectedToken $ head ts

--------------------------------------------------------------------------------
-- prsExpression -

prsExpression :: Parser (Expression x)
prsExpression = do
  ts <- getState
  case ts of
    [] -> empty
    _  -> prsCommand <|> prsTermValue <|> unexpectedToken


--------------------------------------------------------------------------------
-- parse -

parse :: String -> Either ParserFailure (Expression x)
parse s = case scan s of
  Right ts      -> case run prsExpression ts of
    Right (e,_) -> return e
    Left me     -> case me of
      Just e    -> Left e
      Nothing   -> throw $ ImplementationError "parse: unknown failure"
  Left e  -> Left $ LexerFailure e




