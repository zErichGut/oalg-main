
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
-- Module      : Omada.Parser.Lexer
-- Description : lexing of strings.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- lexing of strings.
module Omada.Parser.Lexer
  (
    -- * Scanning
    scan, Token(..), Tokens

    -- * Lexer
  , Lexer, Pos, Word, Chars, LexerFailure(..) 
    -- * Key
  , Keys(..), isAlpha
  ) where

import Prelude hiding (repeat, Word)

import Control.Monad
import Control.Applicative

import Data.Char hiding (isAlpha)
import Data.Maybe

import OAlg.Control.Exception

import Omada.Parser.ActionM


--------------------------------------------------------------------------------
-- Word -

-- | a string not containing white space.
type Word = String

--------------------------------------------------------------------------------
-- Keys -

data Keys
  = Keys
  { kysComment :: Word
  , kysAlphas  :: [Word]
  , kysSymbols :: [Word]
  }

--------------------------------------------------------------------------------
-- isAlpha

-- | predicate for eligible alphas.
isAlpha :: Keys -> Char -> Bool
isAlpha (Keys cm _ sybs) c = not (isSpace c || elem c (map head (cm:sybs)))


--------------------------------------------------------------------------------
-- Pos -

-- | line number and character number of the characters of a string.
type Pos = (Integer,Integer)

--------------------------------------------------------------------------------
-- Chars -

-- | characters with there position.
type Chars = [(Char,Pos)]

--------------------------------------------------------------------------------
-- Token -

data Token = Id Word | Key Word | Symbol Word | Str Word deriving (Show)

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
  = UnexpectedChars Chars
  | ExpectedChar Char Pos
  | UnexpectedChar Char Pos
  | UnexpectedEnd
  deriving (Show)

--------------------------------------------------------------------------------
-- Lexer -

type Lexer = ActionE Chars LexerFailure


-----------------------------------------------------------------------------------------
-- dropSpace -

-- | drops space and returns @()@ if the resulting chars are not empty, otherwise it will be 'empty'.
dropSpace :: Lexer ()
dropSpace = do
  cps <- getState
  case dropWhile (isSpace . fst) cps of
    cps' -> case cps' of
      [] -> empty
      _  -> setState cps' >> return ()

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
-- comment -

-- | pre: the underlying chars is not empty
comment :: Keys -> Lexer String
comment ks = do
  (_,p) <- startsWith (kysComment ks)
  cps   <- getState
  case span (sameLine $ fst p) cps of
    (cps',cps'') -> setState cps'' >> return (map fst cps')

  where sameLine l cp = (fst $ snd $ cp) == l

--------------------------------------------------------------------------------
-- symbol -

-- | a 'Symbol'.
--
--  pre: the underlying chars is not empty
symbol :: Keys -> Lexer (Token,Pos)
symbol ks = foldl (<|) empty $ kysSymbols ks where
  t <| s = t <|> (startsWith s >>= \(s,p) -> return (Symbol s,p))


--------------------------------------------------------------------------------
-- keyOrId -

-- | a 'Key' or 'Id'.
keyOrId :: Keys -> Lexer (Token,Pos)
keyOrId ks = do
  cps <- getState
  case span (isAlpha ks . fst) cps of
    (cps',cps'') -> case map fst cps' of
      ""         -> empty
      w          ->    setState cps''
                    >> let p = head $ map snd cps'
                       in case elem w (kysAlphas ks) of
        True     -> return (Key w,p)
        False    -> return (Id w,p)

--------------------------------------------------------------------------------
-- char -

char :: Integer -> Lexer Char
char l = do
  (c,(l',_)):cps  <- getState
  if l' /= l then empty else case c of
    '"'  -> empty
    _    -> setState cps >> return c
    
--------------------------------------------------------------------------------
-- sring -

string :: Lexer (Token,Pos)
string = do
  ('"',p@(l,_)):cps <- getState
  setState cps
  cs <- repeat $ char l
  cps' <- getState
  case cps' of
    []                  -> failure $ Just $ UnexpectedEnd
    (c,p'@(l',_)):cps'' -> case c of
      '"' | l == l'     -> setState cps'' >> return (Str cs,p)
      _   | l == l'     -> failure $ Just $ ExpectedChar '"' p'
      _                 -> failure $ Just $ UnexpectedChar c p'

--------------------------------------------------------------------------------
-- token -

token :: Keys -> Lexer (Maybe (Token,Pos))
token ks = dropSpace >>
         (   fmap (const Nothing) (comment ks)
         <|> fmap Just string
         <|> fmap Just (symbol ks)
         <|> fmap Just (keyOrId ks)
         )


--------------------------------------------------------------------------------
-- scan -

scan :: Keys -> String -> Either LexerFailure [(Token,Pos)]
scan ks s = case run (repeat $ token ks) (chars s) of
  Right (mtks,cps) -> case dropWhile (isSpace . fst) cps of
    []             -> Right $ catMaybes mtks
    _              -> Left $ UnexpectedChars cps
  Left me          -> case me of
    Nothing        -> throw $ ImplementationError "scan"
    Just e         -> Left e

