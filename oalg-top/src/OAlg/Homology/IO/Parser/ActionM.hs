
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
-- Module      : OAlg.Homology.IO.ActionM
-- Description : monadic actions.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- monadic actions.
module OAlg.Homology.IO.Parser.ActionM
  ( -- * Monadic Action
    ActionM(..), run
  , getState, setState

    -- * ActionE
  , ActionE, failure, handle

    -- * Utilities
  , (??),(<.>), repeat, infixesr, infixesl   ) where

import Prelude hiding (repeat)

import Control.Applicative

import OAlg.Data.Ord

--------------------------------------------------------------------------------
-- ActionM -

newtype ActionM s m x = ActionM (s -> m (x,s))

--------------------------------------------------------------------------------
-- run -

run :: ActionM s m x -> s -> m (x,s)
run (ActionM p) = p

--------------------------------------------------------------------------------
-- Monad -

instance Monad m => Functor (ActionM s m) where
  fmap f (ActionM p) = ActionM (\s -> p s >>= \(x,s) -> return (f x,s))

instance Monad m => Applicative (ActionM s m) where
  pure x = ActionM (\s -> return (x,s))
  ActionM f <*> ActionM g
    = ActionM (\s -> do
                  (x,s')   <- g s
                  (f',s'') <- f s'
                  return (f' x,s'')
             )
      
instance Monad m => Monad (ActionM s m) where
  return = pure
  ActionM p >>= f
    = ActionM (\s -> do
                  (x,s') <- p s -- p :: s -> m (x,s)
                  run (f x) s'  -- f :: x -> ActionM s y
             )

instance (Monad m, Alternative m) => Alternative (ActionM s m) where
  empty = ActionM $ const empty
  ActionM p <|> ActionM q = ActionM (\s -> p s <|> q s)

instance MonadFail m => MonadFail (ActionM s m) where
  fail = ActionM . const . fail

--------------------------------------------------------------------------------
-- setState -

setState :: Monad m => s -> ActionM s m ()
setState s = ActionM (const $ return ((),s))

--------------------------------------------------------------------------------
-- getState -

getState :: Monad m => ActionM s m s
getState = ActionM (\s -> return (s,s))


--------------------------------------------------------------------------------
-- Either (Maybe e) -

instance Alternative (Either (Maybe e)) where
  empty = Left Nothing
  Left Nothing <|> b = b
  a            <|> _ = a  

instance MonadFail (Either (Maybe e)) where
  fail _ = empty
  

--------------------------------------------------------------------------------
-- ActionE -

type ActionE s e = ActionM s (Either (Maybe e)) 

--------------------------------------------------------------------------------
-- failure -

failure :: Maybe e -> ActionE s e a
failure e = ActionM (const $ Left $ e)

--------------------------------------------------------------------------------
-- handle -

handle :: ActionE s e a -> (Maybe e -> ActionE s e a) -> ActionE s e a
handle pa h = ActionM (\s -> case run pa s of
                               Right as -> Right as
                               Left e   -> run (h e) s
                      )

--------------------------------------------------------------------------------
-- (??) -

-- | looking forward.
(??) :: ActionE s e a -> (a -> Bool) -> ActionE s e Bool
pa ?? p = do
  ts <- getState
  a  <- pa
  setState ts
  return (p a)

--------------------------------------------------------------------------------
-- repeat -

repeat :: ActionE s e x -> ActionE s e [x]
repeat px = (px >>= \x -> fmap (x:) $ repeat px) <|> return []

--------------------------------------------------------------------------------
-- <.> -

(<.>) :: ActionE s e a -> ActionE s e b -> ActionE s e (a,b)
a <.> b = do
  x <- a
  y <- b
  return (x,y)

--------------------------------------------------------------------------------
-- infixesr -

oprMax :: Ord k => ActionE s e o -> (o -> k) -> k -> ActionE s e (o,k)
oprMax po prc k
  = po >>= \o -> let k' = prc o in if k <= k' then return (o,k') else empty

infixesr :: Ord k => ActionE s e a -> ActionE s e o -> (o -> k) -> (o -> a -> a -> a) -> ActionE s e a
infixesr px po prc appl = over NegInf where
  over k = px >>= next k

  next k x = (oprMax po prc' k >>= \(o,k') -> fmap (appl o x) (over k') >>= next k) <|> return x

  prc' = It . prc

--------------------------------------------------------------------------------
-- infixesl -

infixesl :: Ord k => ActionE s e o -> (o -> k) -> (o -> a -> a -> a) -> ActionE s e a -> ActionE s e a
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
        y   <- px
        next k x o y
    <|> return x

