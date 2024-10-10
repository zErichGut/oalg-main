
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

--------------------------------------------------------------------------------
-- MAction -

newtype MAction s m x = MAction (s -> m (x,s))

--------------------------------------------------------------------------------
-- run -

run :: MAction s m x -> s -> m (x,s)
run (MAction p) = p

--------------------------------------------------------------------------------
-- Monad -

instance Monad m => Functor (MAction s m) where
  fmap f (MAction p) = MAction (\s -> p s >>= \(x,s) -> return (f x,s))

instance Monad m => Applicative (MAction s m) where
  pure x = MAction (\s -> return (x,s))
  MAction f <*> MAction g
    = MAction (\s -> do
                  (x,s')   <- g s
                  (f',s'') <- f s'
                  return (f' x,s'')
             )
      
instance Monad m => Monad (MAction s m) where
  return = pure
  MAction p >>= f
    = MAction (\s -> do
                  (x,s') <- p s -- p :: s -> m (x,s)
                  run (f x) s'  -- f :: x -> MAction s y
             )

instance (Monad m, Alternative m) => Alternative (MAction s m) where
  empty = MAction $ const empty
  MAction p <|> MAction q = MAction (\s -> p s <|> q s)
  
--------------------------------------------------------------------------------
-- setState -

setState :: Monad m => s -> MAction s m ()
setState s = MAction (const $ return ((),s))

--------------------------------------------------------------------------------
-- getState -

getState :: Monad m => MAction s m s
getState = MAction (\s -> return (s,s))

--------------------------------------------------------------------------------
-- SyntayError -

data ParserFailure
  = SyntaxError String
  | Failure String
  deriving (Show)

instance Alternative (Either ParserFailure) where
  empty = Left $ Failure ""
  Left _ <|> y = y
  r      <|> _ = r  

--------------------------------------------------------------------------------
-- Parser -

type Parser s x = MAction s (Either ParserFailure) x 

--------------------------------------------------------------------------------
-- syntaxError -

syntaxError :: String -> Parser s a
syntaxError msg = MAction (const $ Left $ SyntaxError msg)

--------------------------------------------------------------------------------
-- handle -

handle :: (ParserFailure -> Parser s a) -> Parser s a -> Parser s a
handle h pa = MAction (\s -> case run pa s of
                               Right as -> Right as
                               Left e   -> run (h e) s
                      )
                     
--------------------------------------------------------------------------------
-- failure -

failure :: String -> Parser s a
failure msg = MAction (const $ Left $ Failure msg)

--------------------------------------------------------------------------------
-- Token -

data Token = Id String | Key String deriving (Show)

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
-- (>->) -

(>->) :: Parser s a -> Parser s b -> Parser s (a,b)
pa >-> pb = do
  a <- pa
  b <- pb
  return (a,b)
  
