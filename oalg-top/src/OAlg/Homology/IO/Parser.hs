
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

import Prelude hiding (Word,(!!),repeat)

import Control.Applicative

import Data.Char

import OAlg.Control.Exception

import OAlg.Data.Number
import OAlg.Data.Ord

import OAlg.Homology.IO.ActionM
import OAlg.Homology.IO.Lexer
import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Term
import OAlg.Homology.IO.Value

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
-- repeat -

repeat :: Parser x -> Parser [x]
repeat px = (px >>= \x -> fmap (x:) $ repeat px) <|> return []

--------------------------------------------------------------------------------
-- infixesr -

oprPrc :: Ord k => Parser o -> (o -> k) -> k -> Parser (o,k)
oprPrc po prc k
  = po >>= \o -> let k' = prc o in if k <= k' then return (o,k') else empty

infixesr :: Ord k => Parser a -> Parser o -> (o -> k) -> (o -> a -> a -> a) -> Parser a
infixesr px po prc appl = over NegInf where
  over k = px >>= next k

  next k x = (oprPrc po prc' k >>= \(o,k') -> fmap (appl o x) (over k') >>= next k) <|> return x

  prc' = It . prc

--------------------------------------------------------------------------------
-- infixesl -

infixesl :: Ord k => Parser a -> Parser o -> (o -> k) -> (o -> a -> a -> a) -> Parser a
infixesl px po prc appl = over NegInf where
  over k = px >>= next k

  next k x = error "nyi"
  -- (oprPrc po prc' k >>= \(o,k') -> over k' >>= return . (appl o x)) <|> return x 
  
  prc' = It . prc

--------------------------------------------------------------------------------
-- OprVec -

data OprVec = Add | Sub | SMlt deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- oprVec -

oprVec :: Parser OprVec
oprVec = do
  ts <- getState
  case fmap fst ts of
    []           -> empty
    Symbol o : _ -> case o of
      "+"        -> setState (tail ts) >> return Add
      "-"        -> setState (tail ts) >> return Sub
      "!"        -> setState (tail ts) >> return SMlt
      _          -> empty
    _            -> failure $ Just $ UnexpectedToken $ head ts

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
-- bracket -

-- | the phrase @( a )@,
bracket :: Parser a -> Parser a
bracket a
  = symbol "(" >> a >>= \z -> symbol ")" !! Expected (Symbol ")") >> return z 

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
    Symbol w :_ | w == s -> setState (tail ts) >> return ()
    _                    -> empty

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
-- num -

num :: Parser Z
num = do
  ts <- getState
  case map fst ts of
    Id n :_ | isNum n -> setState (tail ts) >> (return $ fromInteger $ read n)
    _                 -> empty
  where isNum ds@(_:_) = and $ map ((DecimalNumber==) . generalCategory) ds
        isNum _        = False

--------------------------------------------------------------------------------
-- sig -

sig :: Parser Z
sig = do
  ts <- getState
  case map fst ts of
    Symbol "-" :_ -> setState (tail ts) >> return (-1)
    _             -> return 1

--------------------------------------------------------------------------------
-- znum -

znum :: Parser (TermValue x)
znum =  sig >>= \s  -> (num >>= return . Value . ZValue . (s*))
    <|> fmap Free var
    <|> bracket zval
                       
--------------------------------------------------------------------------------
-- zval -

zval :: Parser (TermValue x)
zval = infixesr znum oprVec prcVec applVec

--------------------------------------------------------------------------------
-- atom -

atom :: Parser (TermValue x)
atom
   =  (key "H" >> return (Free "H"))
  <|> (key "C" >> return (Free "C"))
  <|> (key "D" >> return (Free "D"))
  <|> (key "L" >> return (Free "L"))
  <|> zval
  <|> fmap Free var
  <|> bracket value

--------------------------------------------------------------------------------
-- application -

application :: Parser (TermValue x)
application = atom >>= \a -> repeat atom >>= \as -> return (applys a as)

--------------------------------------------------------------------------------
-- linearCombination -

linearCombination :: Parser (TermValue x)
linearCombination = error "nyi"

--------------------------------------------------------------------------------
-- value -

value :: Parser (TermValue x)
value = 
      letdecl
  <|> application
  <|> linearCombination
  
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
