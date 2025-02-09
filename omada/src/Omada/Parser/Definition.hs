
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
-- Module      : Omada.Parser.Definition
-- Description : general definitions and parser utilities.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- general definitions and parser utilities.
module Omada.Parser.Definition
  ( -- * Parsing
    parse, Parser, Token(..), Pos
  , ParserFailure(..), LexerFailure(..)
    -- * Utilities
  , getTokens, setTokens, getPos
  , symbol, key, ident, string
  , repeat, bracket, infixesl, infixesr
  , failure, handle
  , (!!), (??)
  , end
  ) where

import Prelude hiding ((!!), repeat, Word)

import Control.Applicative

import Omada.Parser.ActionM
import Omada.Parser.Lexer

--------------------------------------------------------------------------------
-- ParserFailure -

data ParserFailure
  = LexerFailure LexerFailure
  | EmptyFailure -- ^ if more tokens are expected
  | UnexpectedToken (Token,Pos)
  | ExpectedToken Token (Token,Pos)
  | ExpectedIdent (Token,Pos)
  | ExpectedString (Token,Pos)
  | Expected String (Token,Pos)
  | Unparsed (Token,Pos) Tokens
  | DuplicateVars Word Pos
  | Unknown String
  deriving (Show)

--------------------------------------------------------------------------------
-- Parser -

type Parser = ActionE Tokens ParserFailure

--------------------------------------------------------------------------------
-- getTokens -

getTokens :: Parser Tokens
getTokens = getState

--------------------------------------------------------------------------------
-- getPos -

getPos :: Parser Pos
getPos = do
  ts <- getState
  case ts of
    (_,p):_ -> return p
    _       -> failure $ Just EmptyFailure

--------------------------------------------------------------------------------
-- setTokens -

setTokens :: Tokens -> Parser ()
setTokens = setState

--------------------------------------------------------------------------------
-- (!!) -

infixl 9 !!
  
(!!) :: Parser x -> ((Token,Pos) ->  ParserFailure) -> Parser x
p !! f = p `handle` expected where
  expected Nothing  = getState >>= expc  where
    expc ts  = case ts of
      []    -> failure $ Just EmptyFailure
      t':_  -> failure $ Just $ f t'
  expected f = failure f

--------------------------------------------------------------------------------
-- symbol -

-- | parsing a symbol.
symbol :: Word -> Parser ()
symbol s = do
  ts <- getState
  case map fst ts of
    Symbol w :_ | w == s -> setState (tail ts) >> return ()
    _                    -> empty

--------------------------------------------------------------------------------
-- key -

-- | parsing a key.
key :: Word -> Parser ()
key k = do
  ts <- getState
  case map fst ts of
    Key w:_ | w == k -> setState (tail ts) >> return ()
    _                -> empty

--------------------------------------------------------------------------------
-- ident -

-- | parsing an identifier.
ident :: Parser Word
ident = do
  ts <- getState
  case map fst ts of
    Id x:_ -> setState (tail ts) >> return x
    _      -> empty

--------------------------------------------------------------------------------
-- string -

string :: Parser Word
string = do
  ts <- getState
  case map fst ts of
    Str w:_ -> setState (tail ts) >> return w
    _       -> empty
    
--------------------------------------------------------------------------------
-- end -

-- | expecting end.
end :: Parser a -> a -> Parser a
end e x = do
  ts <- getState
  case ts of
    [] -> return x
    _  -> e

--------------------------------------------------------------------------------
-- bracket -

-- | the phrase @( a )@,
bracket :: Parser a -> Parser a
bracket a
  = symbol "(" >> a >>= \z -> symbol ")" !! ExpectedToken (Symbol ")") >> return z 

--------------------------------------------------------------------------------
-- parse -

parse :: Keys -> Parser a -> String -> Either ParserFailure a
parse ks p s = case scan ks s of
  Right ts        -> case run p ts of
    Right (a,ts)  -> case ts of
      []          -> return a
      t:ts        -> Left $ Unparsed t ts
    Left me       -> case me of
      Just f      -> Left f
      Nothing     -> Left $ Unknown ""
  Left e          -> Left $ LexerFailure e

