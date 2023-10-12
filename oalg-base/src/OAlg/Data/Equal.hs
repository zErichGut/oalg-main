
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : OAlg.Data.Equal
-- Description : equality on values
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- equality on values.
module OAlg.Data.Equal
  ( -- * Eq
    -- | reexported from standard Haskell
    Eq(..), eql, ngt

    -- * Eq1
  , Eq1(..)

    -- * Eq2
  , Eq2(..)
  )
  where

import Data.Proxy

--------------------------------------------------------------------------------
-- eql -

-- | equal.
eql :: (a -> a -> Ordering) -> a -> a -> Bool
eql cmp a b = (a `cmp` b) == EQ

-----------------------------------------------------------------------------------------
-- ngt -

-- | not greater than.
ngt :: (a -> a -> Ordering) -> a -> a -> Bool
ngt cmp a b = (a `cmp` b) /= GT

--------------------------------------------------------------------------------
-- Eq1 -

-- | equality on values for one parameterized types.
class Eq1 p where
  eq1 :: p x -> p x -> Bool
  default eq1 :: Eq (p x) => p x -> p x -> Bool
  eq1 = (==)

instance Eq1 Proxy

--------------------------------------------------------------------------------
-- Eq2 -

-- | equality on values for two parameterized types.
--
--  __Note__ We use this class meanly in the context of 'OAlg.Category.Path'.
class Eq2 h where
  eq2 :: h x y -> h x y -> Bool
  default eq2 :: Eq (h x y) => h x y -> h x y -> Bool
  eq2 = (==)

