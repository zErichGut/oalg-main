
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : OAlg.Category.Applicative
-- Description : application on values.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- application on values.
module OAlg.Category.Applicative
  ( 
    -- * Applicative
    Applicative(..), ($)
  , Applicative1(..)
  )
  where

import Control.Monad (Functor(..))

import OAlg.Data.Either

--------------------------------------------------------------------------------
-- Applicative -
  
-- | family of types having a representation in @(->)@.
class Applicative h where
  -- | application.
  amap :: h a b -> a -> b

instance Applicative (->) where
  amap h = h  

--------------------------------------------------------------------------------
-- ($)
  
infixr 0 $

-- | right associative application on values.
($) :: Applicative h => h a b -> a -> b
($) = amap

instance (Applicative f, Applicative g) => Applicative (Either2 f g) where
  amap (Left2 f)  = amap f
  amap (Right2 g) = amap g

--------------------------------------------------------------------------------
-- Applicative1 -

-- | family of types having a representation in @f a -> f b@.
class Applicative1 h f where
  -- | application.
  amap1 :: h a b -> f a -> f b

instance Functor f => Applicative1 (->) f where
  amap1 = fmap
