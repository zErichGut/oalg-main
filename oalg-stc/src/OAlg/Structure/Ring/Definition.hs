
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Structure.Ring.Definition
-- Description : definition of rings
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Ring's.
module OAlg.Structure.Ring.Definition
  (
    -- * Semiring
    Semiring, rOne, rZero, isMinusOne

    -- * Ring
  , Ring

    -- * Galoisian
  , Galoisian
  
    -- * Field
  , Field(..)
  ) where

import qualified Prelude as A

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Distributive.Definition

--------------------------------------------------------------------------------
-- Semiring -

-- | distributive structure where '*' and @'+'@ are total.
--
--   __Note__ If @__r__@ is 'Total' and 'Distributive' then
-- @'OAlg.Structure.Fibred.Definition.Root' __r__@ is 'Singleton'.
type Semiring r = (Distributive r, Total r)

--------------------------------------------------------------------------------
-- rZero -

-- | the neutral element according to '+', i.e. @rZero == 'zero' 'unit'@.
rZero :: Semiring r => r
rZero = zero unit

--------------------------------------------------------------------------------
-- rOne -

-- | the neutral element according to '*', i.e. @rOne == 'one' 'unit'@.
rOne :: Semiring r => r
rOne = one unit

--------------------------------------------------------------------------------
-- isMinusOne -

-- | check being the additive inverse of 'rOne'.
isMinusOne :: Semiring r => r -> Bool
isMinusOne r = r + rOne == rZero

--------------------------------------------------------------------------------
-- Ring -

-- | abelian semi rings.
type Ring r = (Semiring r, Abelian r)

--------------------------------------------------------------------------------
-- Galoisian -

-- | __Note__ Not every element not equal to 'zero' has to be invertible. As
--   such 'Z' is 'Galoisian'.
type Galoisian r = (Ring r, Commutative r, Invertible r)

--------------------------------------------------------------------------------
-- Field

infixl 7 /

-- | not degenerated commutative rings where every element not equal to zero
-- has a multiplicative inverse.
--
-- __Properties__
--
-- (1) @'rZero' /= 'rOne'@.
--
-- (2) For all @x@ and @y@ in @__r__@ holds:
--
--     (1) If @y /= 'rZero'@ then @x '/' y@ is 'valid'
--
--     (2) If @y '==' 'rZero'@ then @x '/' y@ is not 'valid' and its evaluation will end up in a
--     'OAlg.Structure.Exception.NotInvertible'-exception.
--
-- (3) For all @x@ and @y@ in @__r__@ with @y /= 'rZero'@ holds: @y '*' (x '/' y) '==' x@.
class Galoisian r => Field r  where
  
  -- | division.
  (/) :: r -> r -> r
  a / b = a * invert b

instance Field Q where
  (/) = (A./)
  

