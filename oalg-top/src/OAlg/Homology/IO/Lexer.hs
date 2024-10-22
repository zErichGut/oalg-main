
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
  (
    -- * Scanning Tokens
    scan
    
    -- * Token
  , Token(..), Tokens, Word

    -- * Lexer
  , Lexer, Pos
  , LexerFailure(..)

  ) where

import Prelude hiding (Word)

import Control.Monad
import Control.Applicative

import Data.Char

import OAlg.Control.Exception

import OAlg.Homology.IO.Keywords
import OAlg.Homology.IO.ActionM

--------------------------------------------------------------------------------
-- Pos -

-- | line number and character number of the characters of a string.
type Pos = (Integer,Integer)

--------------------------------------------------------------------------------
-- Word -

-- | a string not containing white space.
type Word = String

--------------------------------------------------------------------------------
-- Chars -

-- | characters with there position.
type Chars = [(Char,Pos)]

--------------------------------------------------------------------------------
-- Token -

data Token = Id Word | Key Word | Symbol Word deriving (Show)

--------------------------------------------------------------------------------
-- Tokens -

-- | tokens with there beginning position.
type Tokens = [(Token,Pos)]

--------------------------------------------------------------------------------
-- chars -

-- | the list of characters with there position in the stirng
chars :: String -> Chars
chars s = join $ map chp (lines s `zip` [1..]) where
  chp :: (String,Integer) -> [(Char,Pos)]
  chp (s,l) = s `zip` map (\p -> (l,p)) [1..] 

--------------------------------------------------------------------------------
-- LexerFailure -

data LexerFailure
  = Unexpected Pos Word
  deriving (Show)

--------------------------------------------------------------------------------
-- Lexer -

type Lexer = ActionE Chars LexerFailure

--------------------------------------------------------------------------------
-- startsWith -
-- | pre: - the underlying chars is not empty
--        - the given name is not empty
startsWith :: String -> Lexer (String,Pos)
startsWith name = do
  s <- getState
  case splitAt (length name) s of
    (s',s'') | map fst s' == name -> setState s'' >> return (name,snd $ head s')
             | otherwise          -> empty

--------------------------------------------------------------------------------
-- prsSymbol -

-- | pre: the underlying string is not empty
prsSymbol :: Lexer (Token,Pos)
prsSymbol = foldl (<|) empty symbols where
  t <| s = t <|> (startsWith s >>= \(s,i) -> return (Symbol s,i))

--------------------------------------------------------------------------------
-- isIdChar -

symbolsHead = map head symbols

isIdChar :: Char -> Bool
isIdChar c = not (elem c symbolsHead || isSpace c)

--------------------------------------------------------------------------------
-- prsId -

-- | pre: the underlying string is not empty
prsId :: Lexer (Token,Pos)
prsId = do
  s <- getState
  case span (isIdChar . fst) s of
    ([],_) -> empty
    (k,s') -> setState s' >> return (Id $ map fst k, snd $ head k)

--------------------------------------------------------------------------------
-- prsKey -

-- | pre: the underlying string is not empty
prsKey :: Lexer (Token,Pos)
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
-- nextChars -

-- | eliminates white space from the beginning and comments.
nextChars :: Lexer Chars
nextChars = do
  chps <- getState
  case dropWhile (isSpace . fst) chps of
    chps'   -> case startsWithComment chps' of
      True  -> setState chps'' >> return chps'' where
                 chps'' = dropWhile ((l==) . fst . snd) chps'
                 l      = fst $ snd $ head $ chps'
      False -> setState chps' >> return chps'
        

  where startsWithComment chps
          = comment == (map fst $ take (length comment) chps)

--------------------------------------------------------------------------------
-- nextToken -

-- | parses the next token.
nextToken :: Lexer (Maybe (Token,Pos))
nextToken = do
  s <- nextChars
  case s of
    [] -> return Nothing
    _  -> (prsSymbol <|> prsKey <|> prsId <|> unexpectedChars) >>= return . Just

--------------------------------------------------------------------------------
-- tokens -

tokens :: Lexer Tokens
tokens = do
  mt <- nextToken
  case mt of
    Nothing -> return []
    Just t  -> tokens >>= return . (t:)

--------------------------------------------------------------------------------
-- scan -

scan :: String -> Either LexerFailure Tokens
scan s = case run tokens $ chars s of
  Right (ts,chs) -> case chs of
    []           -> return ts
    _            -> throw $ ImplementationError ("unscaned chars: " ++ show chs)
  Left me        -> case me of
    Just e       -> Left e
    Nothing      -> throw $ ImplementationError "scan: unknwon failure"

