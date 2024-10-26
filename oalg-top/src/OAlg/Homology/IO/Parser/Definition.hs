
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
-- Module      : OAlg.Homology.IO.Parser.Definition
-- Description : general definitions and parser utilities.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- general definitions and parser utilities.
module OAlg.Homology.IO.Parser.Definition
  ( -- * Parsing
    parse, Parser, ParserFailure(..)

    -- * Utilities
  , getTokens, setTokens
  , symbol, key, ident
  , repeat, bracket, infixesl, infixesr
  , failure, handle
  , (!!), (??)
  , end
  ) where

import Prelude hiding ((!!), repeat, Word)

import Control.Applicative

import OAlg.Control.Exception

import OAlg.Homology.IO.Parser.ActionM
import OAlg.Homology.IO.Parser.Lexer

--------------------------------------------------------------------------------
-- ParserFailure -

data ParserFailure
  = LexerFailure LexerFailure
  | EmptyFailure -- ^ if more tokens are expected
  | UnexpectedToken (Token,Pos)
  | ExpectedToken Token (Token,Pos)
  | ExpectedIdent (Token,Pos)
  | Expected String (Token,Pos)
  deriving (Show)

--------------------------------------------------------------------------------
-- Parser -

type Parser = ActionE Tokens ParserFailure

--------------------------------------------------------------------------------
-- getTokens -

getTokens :: Parser Tokens
getTokens = getState

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
    Right (a,_)   -> return a
    Left me       -> case me of
      Just f      -> Left f
      Nothing     -> throw $ ImplementationError "parse: unknown failure"
  Left e          -> Left $ LexerFailure e

