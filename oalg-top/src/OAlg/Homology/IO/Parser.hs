
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
  ) where

import Control.Applicative

import Prelude hiding ((!!),repeat)

import OAlg.Homology.IO.ActionM

--------------------------------------------------------------------------------
-- SyntayError -

data ParserFailure
  = SyntaxError String
  | Failure String
  | Unknown
  deriving (Show)

instance Alternative (Either ParserFailure) where
  empty = Left $ Unknown
  Left _ <|> y = y
  r      <|> _ = r  

--------------------------------------------------------------------------------
-- Parser -

type Parser s x = ActionM s (Either ParserFailure) x 

--------------------------------------------------------------------------------
-- failure -

failure :: ParserFailure -> Parser s a
failure e = ActionM (const $ Left e)

--------------------------------------------------------------------------------
-- handle -

handle :: Parser s a -> (ParserFailure -> Parser s a) -> Parser s a
handle pa h = ActionM (\s -> case run pa s of
                               Right as -> Right as
                               Left e   -> run (h e) s
                      )
                     
--------------------------------------------------------------------------------
-- syntaxError -

syntaxError :: String -> Parser s a
syntaxError msg = failure (SyntaxError msg)

{-
--------------------------------------------------------------------------------
-- infix declaration -

infix 6 $->
infix 5 >->
infix 0 <||>

--------------------------------------------------------------------------------
-- id -

id :: Parser [Token] String
id = do
  ts <- getState
  case ts of
    Id s : ts' -> do
      setState ts'
      return s
    _ -> syntaxError "Identifier expected"

--------------------------------------------------------------------------------
-- key -

-- | @$@
key :: String -> Parser [Token] String
key a = do
  ts <- getState
  case ts of
    Key b : ts' | b == a    -> do
                               setState ts'
                               return b
                | otherwise -> syntaxError a 
    _                       -> syntaxError "Symbol expected"


--------------------------------------------------------------------------------
-- (<||> -

-- | @||@
(<||>) :: Parser s a -> Parser s a -> Parser s a
a <||> b = a `handle` isSyntaxError b where
  isSyntaxError b (SyntaxError _) = b
  isSyntaxError _ e               = failure e
  
--------------------------------------------------------------------------------
-- (>->) -

-- | @--@
(>->) :: Parser s a -> Parser s b -> Parser s (a,b)
pa >-> pb = do
  a <- pa
  b <- pb
  return (a,b)
  
--------------------------------------------------------------------------------
-- (!!) -

(!!) :: Parser s a -> Parser s a
(!!) a = a `handle` failed where
  failed (SyntaxError msg) = failure (Failure msg)
  failed e                 = failure e

--------------------------------------------------------------------------------
-- ($->) -

-- | @$--@
($->) :: String -> Parser [Token] a -> Parser [Token] a
a $-> b = fmap snd (key a >-> (!!) b)

--------------------------------------------------------------------------------
-- repeat -

repeat :: Parser s a -> Parser s [a]
repeat a = fmap (uncurry (:)) (a >-> repeat a) <||> return []

--------------------------------------------------------------------------------
-- infixes -

infixis :: (o -> Integer) -> (o -> a -> a -> a) -> Parser s o -> Parser s a -> Parser s a
infixis prec appl po pa = infx 0 where
  infx k = do
    s <- getState
    a <- pa
    o <- po
    let ko = prec o in case ko < k of
      True -> setState s 
-}

{-
infixis :: Parser [Token] a -> (String -> Integer) -> (String -> a -> a -> a) -> Parser [Token] a
infixis pa prec appl = next 0 pa where
  next k pa = do
    x  <- pa
    ts <- getState 
    case ts of
      (Key a:_) -> let ak = prec a in case ak < k of
        True    -> setState ts >> return x
        False   -> next k (fmap (appl a x) $ next ak pa)
      _         -> return x
-}
