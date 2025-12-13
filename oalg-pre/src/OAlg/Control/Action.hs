
-- |
-- Module      : OAlg.Control.Action
-- Description : statefull evaluation
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Actions over a state type, i.e. statefull evaluation.
module OAlg.Control.Action
  ( Action(..), run, getState, setState
  )
  where

--------------------------------------------------------------------------------
-- Action -

-- | action over a state @__s__@.
newtype Action s x = Action (s -> (x,s))


instance Functor (Action s)  where
  fmap f (Action r) = Action (\s -> let (x,s') = r s in (f x,s'))


instance Applicative (Action s) where
  pure x = Action (\s -> (x,s))
  mf <*> mx = do
    f <- mf
    x <- mx
    return (f x)

instance Monad (Action s) where
  return = pure 
  Action ax >>= f = Action
    (\s -> let (a,s') = ax s
               Action ay = f a
           in ay s'
    )

-- | running an action on the gicen state.
run :: Action s x -> s -> (x,s)
run (Action a) s = a s

-- | sets the state.
setState :: s -> Action s s
setState s = Action (\s' -> (s',s))

-- | gets the state.
getState :: Action s s
getState = Action (\s -> (s,s))

