
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
  = Unexpected Integer String
  deriving (Show)

--------------------------------------------------------------------------------
-- Lexer -

type Lexer = ActionE [(Char,Integer)] LexerFailure

--------------------------------------------------------------------------------
-- startsWith -
-- | pre: - the underlying string is not empty
--        - the given name is not empty
startsWith :: String -> Lexer (String,Integer)
startsWith name = do
  s <- getState
  case splitAt (length name) s of
    (s',s'') | map fst s' == name -> setState s'' >> return (name,snd $ head s')
             | otherwise          -> empty

--------------------------------------------------------------------------------
-- prsSymbol -

-- | pre: the underlying string is not empty
prsSymbol :: Lexer (Token,Integer)
prsSymbol = foldl (<|) empty symbols where
  t <| s = t <|> (startsWith s >>= \(s,i) -> return (Symbol s,i))

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
prsId :: Lexer (Token,Integer)
prsId = do
  s <- getState
  case span (isIdChar . fst) s of
    ([],_) -> empty
    (k,s') -> setState s' >> return (Id $ map fst k, snd $ head k)

--------------------------------------------------------------------------------
-- prsKey -

-- | pre: the underlying string is not empty
prsKey :: Lexer (Token,Integer)
prsKey = do
  (Id id,i) <- prsId
  case id `elem` alphas of
    True  -> return (Key id,i)
    False -> empty

--------------------------------------------------------------------------------
-- unexpectedString -

-- | pre: the underlying string is not empty
unexpectedChars :: Lexer a
unexpectedChars = do
  s <- getState
  let s' = take 5 $ map fst s
      i  = snd $ head s
   in failure $ Just $ Unexpected i s'
    
--------------------------------------------------------------------------------
-- nextToken -

-- | parses the next token.
nextToken :: Lexer (Maybe (Token,Integer))
nextToken = do
  s <- getState
  case dropWhile (isSpace . fst) s of
    [] -> setState [] >> return Nothing
    s' -> setState s' >> (prsSymbol <|> prsKey <|> prsId <|> unexpectedChars) >>= return . Just

--------------------------------------------------------------------------------
-- tokens -

tokens :: Lexer [(Token,Integer)]
tokens = do
  mt <- nextToken
  case mt of
    Nothing -> return []
    Just t  -> tokens >>= return . (t:)

--------------------------------------------------------------------------------
-- scan -

scan :: String -> Either LexerFailure [(Token,Integer)]
scan s = case run tokens (s `zip` [0..]) of
  Right (ts,_) -> return ts
  Left me      -> case me of
    Just e     -> Left e
    Nothing    -> throw $ ImplementationError "scan: unknwon failure"
