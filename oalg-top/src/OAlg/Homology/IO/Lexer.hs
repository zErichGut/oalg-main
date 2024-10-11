
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
  ( scan
  , Token(..)
  ) where

import Prelude hiding (Word)

import Control.Monad

import Data.Char

import OAlg.Homology.IO.Keywords
import OAlg.Homology.IO.ActionM

--------------------------------------------------------------------------------
-- Token -

data Token = Id String | Key String deriving (Show)

--------------------------------------------------------------------------------
-- Word -

-- | strings without spaces.
type Word = String

--------------------------------------------------------------------------------
-- Parser -

type Parser = ActionM [Word] Maybe

prsIsEmpty :: Parser Bool
prsIsEmpty = do
  ws <- getState
  return (ws == [])

nextToken :: Parser (Maybe Token)
nextToken = do
  ws <- getState
  case ws of
    []    -> return Nothing
    w:ws' -> setState ws' >> return (Just $ Id w) 

--------------------------------------------------------------------------------
-- prsTokens -

prsTokens :: Parser [Token]
prsTokens = do
  mt <- nextToken
  case mt of
    Nothing -> return []
    Just t  -> prsTokens >>= return . (t:)


--------------------------------------------------------------------------------
-- scan -

scan :: String -> [Token]
scan s = case run prsTokens $ words s of
  Just (ts,_) -> ts
  Nothing     -> []

ss = join $ repeat "hallo "
