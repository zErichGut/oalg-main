
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}


-- |
-- Module      : OAlg.Structure.Exponential
-- Description : multiplicative structures with a power function
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'Multiplicative' structures with a power function @('^')@.
module OAlg.Structure.Exponential
  (
    -- * Exponential
    Exponential(..), opower
                            
    -- * Real
  , Real(..)

  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Number.Definition

--------------------------------------------------------------------------------
-- opower -

-- | the power of an orientation by an number.
--
--   __Note__ 'opower' fulfill the properties of 'Exponential' for any number structure.
opower :: (Entity p, Number r) => Orientation p -> r -> Orientation p
opower o r = zpower o z where (z,_) = zFloorFraction r

--------------------------------------------------------------------------------
-- Exponential -

infixl 9 ^
  
-- | 'Multiplicative' structures with a __partially__ defined power function with numbers as exponents.
--
-- __Properties__ 
--
-- (1) For all @f@ and @a@ holds:
--
--     (1) If @'start' f '==' 'end' f@ or @a@ is an element of @[-1,1]@ then
--     @f'^'a@ is 'valid'.
--
--     (2) If @'start' f '/=' 'end' f@ and @a@ is not an element of @[-1,1]@ then
--     @f'^'a@ is not 'valid' and its evaluation will end up in a
--     'OAlg.Structure.Exception.NotExponential'-exception.
--
-- (2) For all @f@ holds: @f'^'1 '==' f@.
--
-- (3) For all @f@ holds: @f'^'(-1) '==' 'invert' f@.
--
-- (4) For all @f@ and @a@ with @'start' f '==' 'end' f@ and @a@ not in @[-1,1]@ holds:
--  @'start' (f'^'a) '==' 'start' f@ and @'end' (f'^'a) '==' 'end' f@.
--
-- (5) For all @f@, @a@ and @b@ with @'start' f '==' 'end' f@ holds:
-- @f'^'(a'*'b) '==' (f'^'a)'^' b@.
--
-- (6) For all @f@ with @'start' f '==' 'end' f@ holds: @f'^'0 == 'one' ('end' f)@.
--
-- (7) For all @f@, @a@ and @b@ with @'start' f '==' 'end' f@ holds:
-- @f'^'(a 'OAlg.Structure.Additive.Definition.+' b) '==' f'^'a '*' f'^'b@.
--
-- (8) For all @a@ and @p@ holds: @('one' p)'^'a '==' 'one' p@.
--
-- (9) For all @f@, @g@ and @a@ with @'start' f '==' 'end' f@, @'start' g '==' 'end' g@
--  @'start' f '==' 'start' g@ and @f '*' g '==' g '*' f@ holds:
--  @(f '*' g)'^'a '==' f'^'a '*' g'^'a@.
--
--  __Note__
--
--  (1) The phrase ..@a@ /is an element of/ @[-1,1]@.. for the properties of '^' is meant
--  to be: @'isOne' a@ or @'OAlg.Structure.Ring.Definition.isMinusOne' a@.
--
--  (2) If @-1@ is an instance of @'Exponent' f@ (see 'minusOne') then @f@ has to be 'Cayleyan'.
class (Multiplicative f, Number (Exponent f)) => Exponential f where
  
  -- | the exponent. 
  type Exponent f
  
  -- | the power of a factor to an exponent.
  (^) :: f -> Exponent f -> f

--------------------------------------------------------------------------------
-- Exponential - Instances -

instance Multiplicative c => Exponential (Inv c) where
  type Exponent (Inv c) = Z
  (^) = zpower
  
--------------------------------------------------------------------------------
-- Real -

-- | reals.
class Multiplicative f => Real f where
  power :: Number r => f -> r -> f

instance Entity p => Real (Orientation p) where
  power = opower
