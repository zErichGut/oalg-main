
-- |
-- Module      : OAlg.Data.Singleton
-- Description : singleton types
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- singleton types having exactly one value.
module OAlg.Data.Singleton
  ( -- ** Singleton
    Singleton(..)
  , Singleton1(..)
  )
  where

import Data.Proxy

--------------------------------------------------------------------------------
-- Singleton -

-- | types @__s__@ with exactly one value which is called the __/unit/__ of @__s__@.
class Singleton s where
  unit :: s

instance Singleton () where
  unit = ()

instance Singleton (Proxy t) where
  unit = Proxy

instance Singleton u => Singleton (a -> u) where
  unit = const unit

--------------------------------------------------------------------------------
-- Singleton1 -

-- | one parameterized types @__s__@ with exactly one element for each @__x__@ which is
-- called the __/unit1/__ of @__s__ __x__@.
class Singleton1 s where
  unit1 :: s x

instance Singleton1 Proxy where
  unit1 = Proxy

