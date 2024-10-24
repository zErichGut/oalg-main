
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
module OAlg.Homology.IO.ActionM
  ( -- * Monadic Action
    ActionM(..), run
  , getState, setState

    -- * Either Action
  , ActionE, failure, handle
  ) where

import Control.Applicative

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


