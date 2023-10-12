
-- |
-- Module      : OAlg.Data.Reducible
-- Description : reducible data
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- reducing values to there canonical value.
module OAlg.Data.Reducible
  (
    -- * Reducible
    Reducible(..), reduceWith, (>>>=), Rdc, RdcState(..), reducesTo

  )
  where 

import OAlg.Control.Action

--------------------------------------------------------------------------------
-- Reducible -

-- | types admitting reducible values.
--
-- __Definition__ @'reduce' e@ is called the __/algebraic value/__ of @e@.
--
-- Reducing an @e@ twice yield the \'same\' value and the idea is that in an algebraic calculation
-- it will be \'safe\' to substitute any occurrence of @e@ by its reduced value, i.e. both calculations
-- will yield the same result.
--
-- __Property__ Let @__e__@ be a reducible type admitting equality, then
-- for all @e@ in @__e__@ holds: @'reduce' ('reduce' e) == 'reduce' e@.
class Reducible e where

  -- | reducing @e@ to its algebraic value. 
  --
  --   __Note__ The default implementation is @'reduce' = 'id'@.
  reduce :: e -> e
  reduce = id

--------------------------------------------------------------------------------
-- Rdc -

-- | 'Action' according to the state type 'RdcState'.
type Rdc = Action RdcState

-- | reduction state.
data RdcState
  = Unchanged  -- ^ no reduction has been applied.
  | Changed -- ^ a reduction has been applied.
  deriving (Show,Read,Eq,Ord,Enum,Bounded)

--------------------------------------------------------------------------------
-- reducesTo -

-- | indicates that a term has the given reduction step, i.e. returns the given value and sets the
-- state to 'Changed'.
reducesTo :: x -> Rdc x
reducesTo x = do
  _ <- setState Changed
  return x

--------------------------------------------------------------------------------
-- reduceWith -

-- | reduces @x@ by the given rules until no more reductions are applicable. 
reduceWith :: (x -> Rdc x) -> x -> x
reduceWith r x = case s of
                   Unchanged -> x'
                   _         -> reduceWith r x'
                
  where (x',s) = run (r x) $ Unchanged

--------------------------------------------------------------------------------
-- (>>>=) -
infixr 1 >>>=

-- | composition of two reductions.
(>>>=) :: (x -> Rdc x) -> (x -> Rdc x) -> x -> Rdc x
(>>>=) f g x = f x >>= g


