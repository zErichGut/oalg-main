
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

data Command x
  = Empty
  | Quit
  | Help
  | Let String (TermValue x)
  deriving (Show)

--------------------------------------------------------------------------------
-- Expression -

data Expression x
  = Command (Command x)
  | TermValue (TermValue x)
  deriving (Show)
           
--------------------------------------------------------------------------------
-- ParserFailure -

data ParserFailure
  = LexerFailure LexerFailure
  | UnexpectedToken (Token,Integer)
  | UnknownCommand ([Token],Integer)
  | Expected (Token) (Token,Integer)
  | ExpectedId (Token,Integer)
  | EmptyFailure -- ^ if more tokens are expected
  deriving (Show)

--------------------------------------------------------------------------------
-- Parser -

type Parser = ActionE [(Token,Integer)] ParserFailure

--------------------------------------------------------------------------------
-- prsCommand -

-- | pre: - the underlying list of tokens starts with a symbol.
--        - the first symbol starts with the character @\':\'@.
prsCommand :: Parser (Expression x)
prsCommand = do
  ts <- getState
  case map fst ts of
    [Symbol ":quit"] -> return $ Command Quit
    [Symbol ":q"]    -> return $ Command Quit
    [Symbol ":help"] -> return $ Command Help
    [Symbol ":h"]    -> return $ Command Help
    [Symbol ":?"]    -> return $ Command Help
    _                -> failure $ Just $ UnknownCommand $ (map fst ts, snd $ head ts)

--------------------------------------------------------------------------------
-- prsFree -

prsFree :: Parser (Expression x)
prsFree = do
  ts <- getState
  case ts of
    (Id v,_):ts'  -> setState ts' >> (return $ TermValue $ Free v)
    (Key k,_):ts' -> setState ts' >> (return $ TermValue $ Free k)
    _             -> empty
    
--------------------------------------------------------------------------------
-- prsTermValue -

-- | pre: the underlying state is not empty.
prsTermValue :: e x -> Parser (Expression x)
prsTermValue _ = prsFree

--------------------------------------------------------------------------------
-- unexpectedToken -

-- | pre: the underlying state is not empty.
unexpectedToken :: Parser a
unexpectedToken = do
  ts <- getState
  failure $ Just $ UnexpectedToken $ head ts

--------------------------------------------------------------------------------
-- prsLet -

-- | pre: the underlying tokens start with @'Key' \"let\"@.
prsLet :: e x -> Parser (Expression x)
prsLet e = do
  ts <- getState
  case map fst ts of
    Key "let" : Id _ : Symbol "=" : [] -> failure $ Just $ EmptyFailure
    Key "let" : Id x : Symbol "=" : _ -> do
      trm <- setState (drop 3 ts) >> prsTermValue e
      ts  <- getState
      case map fst ts of
        []            -> case trm of
          TermValue v -> return $ Command $ Let x $ v
          _           -> throw $ ImplementationError "prsLet"
        _             -> error "nyi"
                                           
    Key "let" : Id _ : _ : _ -> failure $ Just $ Expected (Symbol "=") (head $ drop 2 ts)
    Key "let" : _    : _     -> failure $ Just $ ExpectedId (head $ drop 1 ts)
    _                        -> throw $ ImplementationError "prsLet"
    
--------------------------------------------------------------------------------
-- prsExpression -

prsExpression :: e x -> Parser (Expression x)
prsExpression e = do
  ts <- getState
  case map fst ts of
    [] -> return (Command Empty)
    Symbol (':':_) : _ -> prsCommand
    Key "let" :_       -> prsLet e
    _                  -> prsTermValue e

--------------------------------------------------------------------------------
-- parse -

parse :: e x -> String -> Either ParserFailure (Expression x)
parse e s = case scan s of
  Right ts        -> case run (prsExpression e) ts of
    Right (exp,_) -> return exp
    Left me       -> case me of
      Just f      -> Left f
      Nothing     -> throw $ ImplementationError "parse: unknown failure"
  Left e  -> Left $ LexerFailure e




