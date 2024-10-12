
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
-- Module      : OAlg.Homology.IO.Lexer
-- Description : lexical analysis of strings.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- lexical analysis of strings.
module OAlg.Homology.IO.Lexer
  ( -- * Scanning Tokens
    scan
    
    -- * Token
  , Token(..)

    -- * Lexer
  , Lexer, nextToken
  , LexerFailure(..)
  ) where

import Control.Applicative

import Data.Char

import OAlg.Control.Exception

import OAlg.Homology.IO.Keywords
import OAlg.Homology.IO.ActionM

--------------------------------------------------------------------------------
-- Token -

data Token = Id String | Key String | Symbol String deriving (Show)

--------------------------------------------------------------------------------
-- LexerFailure -

data LexerFailure
  = Unknown
  | Unexpected String
  deriving (Show)

instance DefaultFailure LexerFailure where
  defaultFailure = Unknown

instance Exception LexerFailure
  
--------------------------------------------------------------------------------
-- Lexer -

type Lexer = ActionM String (Either LexerFailure)

--------------------------------------------------------------------------------
-- startsWith -

startsWith :: String -> Lexer String
startsWith name = do
  s <- getState
  case splitAt (length name) s of
    (s',s'') | s' == name -> setState s'' >> return name
             | otherwise  -> empty

--------------------------------------------------------------------------------
-- prsSymbol -

-- | pre: the underlying string is not empty
prsSymbol :: Lexer Token
prsSymbol = foldl (<|) empty symbols where
  t <| s = t <|> (startsWith s >>= return . Symbol)

--------------------------------------------------------------------------------
-- headSymbols -

headSymbols :: [Char]
headSymbols = map head symbols

--------------------------------------------------------------------------------
-- isIdChar -

isIdChar :: Char -> Bool
isIdChar c = not (c `elem` headSymbols) && isAlphaNum c

--------------------------------------------------------------------------------
-- prsId -

-- | pre: the underlying string is not empty
prsId :: Lexer Token
prsId = do
  s <- getState
  case span isIdChar s of
    ([],_) -> empty
    (k,s') -> setState s' >> return (Id k)

--------------------------------------------------------------------------------
-- prsKey -

-- | pre: the underlying string is not empty
prsKey :: Lexer Token
prsKey = do
  Id id <- prsId
  case id `elem` alphas of
    True  -> return (Key id)
    False -> empty

--------------------------------------------------------------------------------
-- unexpectedString -

unexpected :: Lexer Token
unexpected = do
  s <- getState
  failure $ Unexpected $ take 5 s
  
--------------------------------------------------------------------------------
-- nextToken -

-- | parses the next token.
nextToken :: Lexer (Maybe Token)
nextToken = do
  s <- getState
  case dropWhile isSpace s of
    [] -> setState [] >> return Nothing
    s' -> setState s' >> (prsSymbol <|> prsKey <|> prsId <|> unexpected) >>= return . Just


--------------------------------------------------------------------------------
-- scan -

scan :: String -> [Token]
scan s = case run nextToken s of
  Right (mt,s') -> case mt of
    Just t      -> t : scan s'
    Nothing     -> []
  Left e        -> throw e


