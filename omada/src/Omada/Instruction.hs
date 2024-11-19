
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
-- Module      : Omada.Instruction
-- Description : parsing instructions.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- parsing instructions.
module Omada.Instruction
  ( prsInstruction
  , Instruction(..), Command(..), ComplexId(..)
  ) where

import Prelude hiding (Word,(!!),repeat)

import Control.Applicative

import Data.Char

import OAlg.Data.Canonical
import OAlg.Data.Number

import OAlg.Homology.ChainComplex (Regular(..))

import Omada.Parser.Definition
import Omada.Parser.Lexer

import Omada.Term
import Omada.Evaluation
import Omada.Value

--------------------------------------------------------------------------------
-- keys -

-- | the keys for instructions.
keys :: Keys
keys = Keys comment alphas symbols where
  alphas :: [String]
  alphas
    = [ "let", "in", "ext"
      , "C", "D", "H", "K", "L"
      , "b", "d", "h"
      ]
  
  -- | the symbols.
  symbols :: [String]
  symbols
    = [ "(",")"
      , ":quit", ":q" 
      , ":help", ":h", ":?"
      , ":load", ":l"
      , ":complex", ":c"
      , ":tutorial"
      , ":valid", ":v"
      , "+","-", "!"
      , "=", "#"
      ]
  
  -- | the comment-symbol string. Everything after this symbol will be ignored by the lexer until
  --   the end of line.
  comment :: String
  comment = "//"

--------------------------------------------------------------------------------
-- Complex -

data ComplexId
  = EmptyComplex
  | KleinBottle
  | MoebiusStrip
  | Torus N
  | ProjectiveSpace N
  | Simplex N
  | Sphere N
  | Plane N N
  deriving (Show)

--------------------------------------------------------------------------------
-- Command -

data Command x
  = Quit
  | Help
  | SetComplex Regular ComplexId
  | Load FilePath
  | Let String (TermValue x)
  | Tutorial
  | Valid (Maybe (TermValue x))
  deriving (Show)

--------------------------------------------------------------------------------
-- Instruction -

data Instruction x
  = Empty
  | Command (Command x)
  | TermValue (TermValue x)
  deriving (Show)
           
--------------------------------------------------------------------------------
-- OprVec -

data OprVec = Add | Sub | SMlt deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- oprVec -

oprVec :: Parser OprVec
oprVec = do
  ts <- getTokens
  case fmap fst ts of
    []           -> empty
    Symbol o : _ -> case o of
      "+"        -> setTokens (tail ts) >> return Add
      "-"        -> setTokens (tail ts) >> return Sub
      "!"        -> setTokens (tail ts) >> return SMlt
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
unexpected = getTokens >>= failure . Just . UnexpectedToken . head  

--------------------------------------------------------------------------------
-- quit -

quit :: Parser (Command x)
quit = symbol ":quit" <|> symbol ":q" >> return Quit

--------------------------------------------------------------------------------
-- help -

help :: Parser (Command x)
help = symbol ":help" <|> symbol ":h" <|> symbol ":?" >> return Help

--------------------------------------------------------------------------------
-- load -

load :: Parser (Command x)
load = do
  symbol ":load" <|> symbol ":l"
  (string !! ExpectedString) >>= return . Load

--------------------------------------------------------------------------------
-- vars -

vars :: Parser (Word,[Word])
vars = ident >>= \v0 -> repeat ident >>= \vs -> return (v0,vs)

--------------------------------------------------------------------------------
-- varbind -

varbind :: Parser (Command x)
varbind = do
  key "let"
  v  <- ident !! ExpectedIdent
  symbol "=" !! ExpectedToken (Symbol "=")
  e <- expression !! Expected "expression"
  end empty $ Let v e 

{-
varbind = do
  key "let"
  p  <- getPos
  v  <- ident
  vs <- repeat ident 
  case duplicates (v:vs) of
    d:_ -> failure $ Just $ DuplicateVars (head d) p
    []  -> do
            symbol "=" !! ExpectedToken (Symbol "=")
            e <- expression !! Expected "expression"
            end empty $ Let v $ abstracts vs e 
  where duplicates vs = filter ((>1) . length) $ group $ sort vs
-}               

--------------------------------------------------------------------------------
-- letdecl -

letdecl :: Parser (TermValue x)
letdecl
  =   key "let" >> (ident !! ExpectedIdent)
  >>= \x -> (symbol "=" !! ExpectedToken (Symbol "=")) >> (expression !! Expected "expression")
  >>= \v -> (key "in" !! ExpectedToken (Key "in")) >> (expression !! Expected "expression")
  >>= \w -> return (abstracts [x] w :!> v)

--------------------------------------------------------------------------------
-- complexEmpty -

complexEmpty :: Parser ComplexId
complexEmpty = do
  "empty" <- ident
  return EmptyComplex
  
--------------------------------------------------------------------------------
-- complexKleinBottle -

complexKleinBottle :: Parser ComplexId
complexKleinBottle = do
  "kleinBottle" <- ident
  return KleinBottle

--------------------------------------------------------------------------------
-- complexSphere -

complexSphere :: Parser ComplexId
complexSphere = do
  "sphere" <- ident
  n        <- num !! Expected "mum"
  return (Sphere n)

--------------------------------------------------------------------------------
-- complexPlane -

complexPlane :: Parser ComplexId
complexPlane = do
  "plane" <- ident
  a       <- num !! Expected "num"
  b       <- num !! Expected "num"
  return (Plane a b)

--------------------------------------------------------------------------------
-- complexMoebiusStrip -

complexMoebiusStrip :: Parser ComplexId
complexMoebiusStrip = do
  "moebiusStrip" <- ident
  return MoebiusStrip

--------------------------------------------------------------------------------
-- complexTorus -

complexTorus :: Parser ComplexId
complexTorus = do
  "torus" <- ident
  n        <- num !! Expected "mum"
  return (Torus n)

--------------------------------------------------------------------------------
-- complexProjectiveSpace -

complexProjectiveSpace :: Parser ComplexId
complexProjectiveSpace = do
  "projectiveSpace" <- ident
  n        <- num !! Expected "mum"
  return (ProjectiveSpace n)

--------------------------------------------------------------------------------
-- complexSimplex -

complexSimplex :: Parser ComplexId
complexSimplex = do
  "simplex" <- ident
  n        <- num !! Expected "mum"
  return (Simplex n)

--------------------------------------------------------------------------------
-- extended -

extended :: Parser Regular
extended = key "ext" >> return Extended
   
--------------------------------------------------------------------------------
-- setComplex -

setComplex :: Parser (Command x)
setComplex
  =    (symbol ":complex" <|> symbol ":c")
    >> (   (   (extended <|> return Regular)
           >>= \r -> (   complexEmpty <|> complexKleinBottle <|> complexMoebiusStrip
                     <|> complexTorus <|> complexProjectiveSpace
                     <|> complexSimplex <|> complexSphere <|> complexPlane
                     <|> (failure $ Just $ Unknown "cpxId") 
                     )
               >>= return . SetComplex r
           )
       <|> (failure $ Just $ Unknown "complex") 
       )

--------------------------------------------------------------------------------
-- valid -

valid :: Parser (Command x)
valid = (symbol ":valid" <|> symbol ":v") >> end (fmap (Valid . Just) expression) (Valid Nothing) 

--------------------------------------------------------------------------------
-- tutorial -

tutorial :: Parser (Command x)
tutorial = symbol ":tutorial" >> return Tutorial

--------------------------------------------------------------------------------
-- command -

command :: Parser (Command x)
command = quit <|> help <|> setComplex <|> load <|> varbind <|> valid <|> tutorial

--------------------------------------------------------------------------------
-- num -

num :: Parser N
num = do
  ts <- getTokens
  case map fst ts of
    Id n :_ | isNum n -> setTokens (tail ts) >> (return $ fromInteger $ read n)
    _                 -> empty
  where isNum ds@(_:_) = and $ map ((DecimalNumber==) . generalCategory) ds
        isNum _        = False

--------------------------------------------------------------------------------
-- sig -

sig :: Parser Z
sig = do
  ts <- getTokens
  case map fst ts of
    Symbol "-" :_ -> setTokens (tail ts) >> return (-1)
    Symbol "+" :_ -> setTokens (tail ts) >> return 1
    _             -> empty

--------------------------------------------------------------------------------
-- expression -

expression :: Parser (TermValue x)
expression = linearCombination sigTerm

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
   =  (key "C" >> return (Free "C"))
  <|> (key "D" >> return (Free "D"))
  <|> (key "H" >> return (Free "H"))
  <|> (key "K" >> return (Free "K"))
  <|> (key "L" >> return (Free "L"))
  <|> (key "d" >> return (Free "d"))
  <|> (key "b" >> return (Free "b"))
  <|> (key "h" >> return (Free "h"))
  <|> (symbol "#" >> return (Free "#"))
  <|> fmap (Value . ZValue . inj) num
  <|> fmap Free ident
  <|> bracket expression

--------------------------------------------------------------------------------
-- instruction -

instruction :: Parser (Instruction x)
instruction
  =   end empty Empty
  <|> (command >>= return . Command)
  <|> (expression >>= return . TermValue)
  >>= end unexpected

--------------------------------------------------------------------------------
-- prsInstruction -

prsInstruction :: String -> Either ParserFailure (Instruction x)
prsInstruction = parse keys instruction

