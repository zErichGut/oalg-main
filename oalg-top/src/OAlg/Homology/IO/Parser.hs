
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
  (
    -- * Parser
     parse, ParserFailure(..)
     -- * Expression
  , Expression(..), Command(..)

   ) where

import Prelude hiding (Word,(!!))

import Control.Applicative

import OAlg.Control.Exception

import OAlg.Homology.IO.ActionM
import OAlg.Homology.IO.Lexer
import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Term

--------------------------------------------------------------------------------
-- Command -

data Command x
  = Quit
  | Help
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
-- ParserFailure -

data ParserFailure
  = LexerFailure LexerFailure
  -- | UnknownCommand ([Token],Pos)
  | EmptyFailure -- ^ if more tokens are expected
  | UnexpectedToken (Token,Pos)
  | Expected Token (Token,Pos)
  | ExpectedId (Token,Pos)
  | ExpectedValue (Token,Pos)
  deriving (Show)

--------------------------------------------------------------------------------
-- Parser -

type Parser = ActionE Tokens ParserFailure

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
-- key -

key :: Word -> Parser ()
key k = do
  ts <- getState
  case map fst ts of
    Key w:_ | w == k -> setState (tail ts) >> return ()
    _                -> empty

--------------------------------------------------------------------------------
-- symbol -

symbol :: Word -> Parser ()
symbol s = do
  ts <- getState
  case map fst ts of
    Symbol w:_ | w == s -> setState (tail ts) >> return ()
    _                   -> empty

--------------------------------------------------------------------------------
-- var -

var :: Parser Word
var = do
  ts <- getState
  case map fst ts of
    Id x:_ -> setState (tail ts) >> return x
    _      -> empty
    
--------------------------------------------------------------------------------
-- empty' -

empty' :: Parser (Expression x)
empty' = do
  ts <- getState
  case ts of
    [] -> return Empty
    _  -> empty

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
  =   key "let" >> (var !! ExpectedId)
  >>= \x -> (symbol "=" !! Expected (Symbol "=")) >> (value !! ExpectedValue)
  >>= \v -> empty' >> return (Let x v)

--------------------------------------------------------------------------------
-- letdecl -

letdecl :: Parser (TermValue x)
letdecl
  =   key "let" >> (var !! ExpectedId)
  >>= \x -> (symbol "=" !! Expected (Symbol "=")) >> (value !! ExpectedValue)
  >>= \v -> (key "in" !! Expected (Key "in")) >> (value !! ExpectedValue)
  >>= \w -> empty' >> return (abstracts [x] w :!> v)

--------------------------------------------------------------------------------
-- command -

command :: Parser (Command x)
command = quit <|> help <|> varbind

--------------------------------------------------------------------------------
-- value -

value :: Parser (TermValue x)
value
  =   (key "H" >> return (Free "H"))
  <|> letdecl
  <|> (var >>= \x -> return $ Free x)

--------------------------------------------------------------------------------
-- unexpected -

unexpected :: Parser (Expression x)
unexpected = getState >>= failure . Just . UnexpectedToken . head  

--------------------------------------------------------------------------------
-- expression -

expression :: Parser (Expression x)
expression
  =   empty'
  <|> (command >>= return . Command)
  <|> (value >>= return . TermValue)
  <|> unexpected

--------------------------------------------------------------------------------
-- parse -

parse :: String -> Either ParserFailure (Expression x)
parse s = case scan s of
  Right ts        -> case run expression ts of
    Right (exp,_) -> return exp
    Left me       -> case me of
      Just f      -> Left f
      Nothing     -> throw $ ImplementationError "parse: unknown failure"
  Left e  -> Left $ LexerFailure e
