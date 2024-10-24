
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
  , Expression(..), Command(..), ComplexId(..)

   ) where

import Prelude hiding (Word,(!!),repeat)

import Control.Applicative

import Data.Char

import OAlg.Control.Exception

import OAlg.Data.Canonical
import OAlg.Data.Number
import OAlg.Data.Ord

import OAlg.Homology.ChainComplex (Regular(..))

import OAlg.Homology.IO.ActionM
import OAlg.Homology.IO.Lexer
import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Term
import OAlg.Homology.IO.Value

--------------------------------------------------------------------------------
-- Load -

data ComplexId
  = EmptyComplex
  | KleinBottle
  | Sphere N
  deriving (Show)
--------------------------------------------------------------------------------
-- Command -

data Command x
  = Quit
  | Help
  | Load Regular ComplexId
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
  | EmptyFailure -- ^ if more tokens are expected
  | UnexpectedToken (Token,Pos)
  | Expected Token (Token,Pos)
  | ExpectedId (Token,Pos)
  | ExpectedValue (Token,Pos)
  | ExpectedNumber (Token,Pos)
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
-- (??) -

-- | looking forward.
(??) :: Parser a -> (a -> Bool) -> Parser Bool
pa ?? p = do
      ts <- getState
      a  <- pa
      setState ts
      return (p a)

--------------------------------------------------------------------------------
-- bracket -

-- | the phrase @( a )@,
bracket :: Parser a -> Parser a
bracket a
  = symbol "(" >> a >>= \z -> symbol ")" !! Expected (Symbol ")") >> return z 

--------------------------------------------------------------------------------
-- repeat -

repeat :: Parser x -> Parser [x]
repeat px = (px >>= \x -> fmap (x:) $ repeat px) <|> return []

--------------------------------------------------------------------------------
-- <.> -

(<.>) :: Parser a -> Parser b -> Parser (a,b)
a <.> b = do
  x <- a
  y <- b
  return (x,y)

--------------------------------------------------------------------------------
-- infixesr -

oprMax :: Ord k => Parser o -> (o -> k) -> k -> Parser (o,k)
oprMax po prc k
  = po >>= \o -> let k' = prc o in if k <= k' then return (o,k') else empty

infixesr :: Ord k => Parser a -> Parser o -> (o -> k) -> (o -> a -> a -> a) -> Parser a
infixesr px po prc appl = over NegInf where
  over k = px >>= next k

  next k x = (oprMax po prc' k >>= \(o,k') -> fmap (appl o x) (over k') >>= next k) <|> return x

  prc' = It . prc

--------------------------------------------------------------------------------
-- infixesl -

infixesl :: Ord k => Parser o -> (o -> k) -> (o -> a -> a -> a) -> Parser a -> Parser a
infixesl po prc appl px = px >>= over NegInf where
  prc' = It . prc

  po' k = po >>= \o -> if k < prc' o then return o else empty

  next k x o y = do
        dec <- po ?? (\o' -> prc' o' <= prc' o)
        case dec of
          True  -> over k (appl o x y)
          False -> over (prc' o) y >>= over k . appl o x
    <|> return (appl o x y)

  -- all applications o with k < prc' o
  over k x = do
        o   <- po' k
        y   <- px !! const EmptyFailure
        next k x o y
    <|> return x

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
    _            -> empty -- failure $ Just $ UnexpectedToken $ head ts

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
-- linearCombination -

linearCombination :: Parser (TermValue x) -> Parser (TermValue x)
linearCombination = infixesl oprVec prcVec applVec

--------------------------------------------------------------------------------
-- unexpected -

unexpected :: Parser a
unexpected = getState >>= failure . Just . UnexpectedToken . head  


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
-- end -

end :: Parser a -> a -> Parser a
end e x = do
  ts <- getState
  case ts of
    [] -> return x
    _  -> e

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
  >>= \v -> end empty (Let x v)

--------------------------------------------------------------------------------
-- letdecl -

letdecl :: Parser (TermValue x)
letdecl
  =   key "let" >> (var !! ExpectedId)
  >>= \x -> (symbol "=" !! Expected (Symbol "=")) >> (value !! ExpectedValue)
  >>= \v -> (key "in" !! Expected (Key "in")) >> (value !! ExpectedValue)
  >>= \w -> return (abstracts [x] w :!> v)

--------------------------------------------------------------------------------
-- loadEmpty -

loadEmpty :: Parser ComplexId
loadEmpty = do
  "empty" <- var
  return EmptyComplex
  
--------------------------------------------------------------------------------
-- loadKleinBottle -

loadKleinBottle :: Parser ComplexId
loadKleinBottle = do
  "kleinBottle" <- var
  return KleinBottle

--------------------------------------------------------------------------------
-- loadSphere -

loadSphere :: Parser ComplexId
loadSphere = do
  "sphere" <- var
  n        <- num !! ExpectedNumber
  return (Sphere n)

--------------------------------------------------------------------------------
-- extended -

extended :: Parser Regular
extended = key "ext" >> return Extended
   
--------------------------------------------------------------------------------
-- load -

load :: Parser (Command x)
load = (symbol ":load" <|> symbol ":l")
    >> (   (extended <|> return Regular)
       >>= \r -> (loadEmpty <|> loadKleinBottle <|> loadSphere)
           >>= return . Load r
       )  
       
--------------------------------------------------------------------------------
-- command -

command :: Parser (Command x)
command = quit <|> help <|> load <|> varbind

--------------------------------------------------------------------------------
-- num -

num :: Parser N
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
    Symbol "+" :_ -> setState (tail ts) >> return 1
    _             -> empty

--------------------------------------------------------------------------------
-- value -

value :: Parser (TermValue x)
value = linearCombination sigTerm

--------------------------------------------------------------------------------
-- sigTerm -

sigTerm :: Parser (TermValue x)
sigTerm = do
  s <- repeat sig
  case foldl (*) 1 s of
    -1 -> term >>= return . Opr (!) (Value $ ZValue (-1))
    _  -> term
  where (!) = ScalarMultiplication

--------------------------------------------------------------------------------
-- term -

term :: Parser (TermValue x)
term = letdecl <|> application

--------------------------------------------------------------------------------
-- application -

application :: Parser (TermValue x)
application = atom >>= \a -> repeat atom >>= \as -> return (applys a as)

--------------------------------------------------------------------------------
-- atom -

atom :: Parser (TermValue x)
atom 
   =  (key "A" >> return (Free "A"))
  <|> (key "B" >> return (Free "B"))
  <|> (key "C" >> return (Free "C"))
  <|> (key "H" >> return (Free "H"))
  <|> (key "K" >> return (Free "K"))
  <|> (key "d" >> return (Free "d"))
  <|> (key "d'" >> return (Free "d'"))
  <|> (key "h" >> return (Free "h"))
  <|> (symbol "#" >> return (Free "#"))
  <|> fmap (Value . ZValue . inj) num
  <|> fmap Free var
  <|> bracket value

--------------------------------------------------------------------------------
-- expression -

expression :: Parser (Expression x)
expression
  =   end empty Empty
  <|> (command >>= return . Command)
  <|> (value >>= return . TermValue)
  >>= end unexpected


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
