
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : OAlg.Data.Opposite
-- Description : predicate for the opposite
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- predicate for the opposite.
module OAlg.Data.Opposite
  (
    -- * Op
    Op(..), fromOp, fromOpOp

    -- * Op2
  , Op2(..)

    -- * Duality
  , OpDualisable(..)
  ) where

import Prelude hiding ((&&),(||))

import OAlg.Data.Show
import OAlg.Data.Equal
import OAlg.Data.Logical

--------------------------------------------------------------------------------
-- Op -

-- | Predicate for the opposite of a type @__x__@. 
newtype Op x = Op x deriving (Show,Read,Eq)

--------------------------------------------------------------------------------
-- Op (x) - Instances -

instance Ord x => Ord (Op x) where Op x `compare` Op y = y `compare` x

instance Logical a => Logical (Op a) where
  Op a || Op b = Op (a && b)
  Op a && Op b = Op (a || b)

--------------------------------------------------------------------------------
-- fromOp -
-- | from @'Op' x@.
fromOp :: Op x -> x
fromOp (Op x) = x

--------------------------------------------------------------------------------
-- fromOpOp -

-- | from @'Op' ('Op' x)@.
fromOpOp :: Op (Op x) -> x
fromOpOp (Op (Op x)) = x

--------------------------------------------------------------------------------
-- Op2 -

-- | Predicat for the opposite of a two parametrized type @__h__@ where
--   the two parameters @__x__@ and @__y__@ are switched
newtype Op2 h x y = Op2 (h y x)

instance Show2 h => Show2 (Op2 h) where
  show2 (Op2 h) = "Op2[" ++ show2 h ++ "]"

instance Eq2 h => Eq2 (Op2 h) where
  eq2 (Op2 f) (Op2 g) = eq2 f g 

--------------------------------------------------------------------------------
-- OpDualisable -

-- | 'Op'-dualisable structures.
--
-- __Property__ Let @'OpDualisable' __d__ __s__@, then for all @__x__@, @__y__@, @__a__@
-- with @'Eq' (__x__ __a__)@ and  @'Eq' (__y__ ('Op' __a__)) holds:
-- 
-- (1) @'opdFromOp' s ('opdToOp' s x) '==' x@ for all @x@ in @__x__ __a__@ and @s@ in @__s__ __a__@.
--
-- (2) @'opdToOp' s ('opdFromOp' s y) '==' y@ for all and @y@ in @__y__ ('Op' __a__)@ and
-- @s@ in @__s__ __a__@.
class OpDualisable d s where
  opdToOp   :: d x y -> s a -> x a -> y (Op a)
  opdFromOp :: d x y -> s a -> y (Op a) -> x a
