
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, DefaultSignatures #-}


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

    -- * Generalized
  , ApplicativeG(..), amapG'
  , ApplicationG(..), apType, apIdType
  )
  where

import Control.Monad (Functor(..))

import Prelude ((.))
import Data.List (map)

import OAlg.Data.Identity
import OAlg.Data.Either
import OAlg.Data.X

--------------------------------------------------------------------------------
-- ApplicativeG -

-- | generalized application of a family of types.
class ApplicativeG t a b where
  -- | application.
  amapG :: a x y -> b (t x) (t y)

instance ApplicativeG Id (->) (->) where
  amapG = toIdG
  
--------------------------------------------------------------------------------
-- amapG' -

-- | prefixing a proxy.
amapG' :: ApplicativeG t a b => q t a b -> a x y -> b (t x) (t y)
amapG' _ = amapG

--------------------------------------------------------------------------------
-- ApplicationG -

-- | attest of being 'ApplicativeG'.
data ApplicationG t a b where
  ApplicationG :: ApplicativeG t a b => ApplicationG t a b

--------------------------------------------------------------------------------
-- apType -

-- | application to @(->)@ based on @__f__@,
apType :: ApplicativeG t h (->) => ApplicationG t h (->)
apType = ApplicationG

--------------------------------------------------------------------------------
-- apIdType-

-- | application to @(->)@ based on 'Id',
apIdType :: ApplicativeG Id h (->) => ApplicationG Id h (->)
apIdType = ApplicationG

--------------------------------------------------------------------------------
-- Applicative -
  
-- | family of types having a representation in @(->)@.
class Applicative h where
  -- | application.
  amap :: h a b -> a -> b
  default amap :: ApplicativeG Id h (->) => h a b -> a -> b
  amap h = fromId . amapG' apIdType h . Id

instance Applicative (->) where amap h = h  

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
  default amap1 :: ApplicativeG f h (->) => h a b -> f a -> f b
  amap1 = amapG' apType

instance Applicative1 (->) X where amap1 = fmap


instance Applicative1 (->) [] where amap1 = map

instance Applicative1 (->) Id
