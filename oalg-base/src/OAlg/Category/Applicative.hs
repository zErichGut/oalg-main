
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}


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
    Applicative, amap, ($)
  , Applicative1, amap1

    -- * Generalized
  , ApplicativeG(..), amapG'
  , ApplicationG(..), apType, apIdType

  )
  where

import Control.Monad (fmap)

import Data.List (map)

import OAlg.Data.Identity
import OAlg.Data.Either
import OAlg.Data.X

--------------------------------------------------------------------------------
-- ApplicativeG -

-- | generalized application of family of types.
class ApplicativeG t a b where
  -- | application.
  amapG :: a x y -> b (t x) (t y)

--------------------------------------------------------------------------------
-- ApplicativeG - Instances -

instance ApplicativeG Id (->) (->) where amapG = toIdG
instance ApplicativeG X (->) (->)  where amapG = fmap
instance ApplicativeG [] (->) (->) where amapG = map

instance (ApplicativeG t f c, ApplicativeG t g c) => ApplicativeG t (Either2 f g) c where
  amapG (Left2 f)  = amapG f
  amapG (Right2 g) = amapG g
  
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

-- | application to @(->)@ based on @__t__@,
apType :: ApplicativeG t h (->) => ApplicationG t h (->)
apType = ApplicationG

--------------------------------------------------------------------------------
-- apIdType-

-- | application to @(->)@ based on 'Id',
apIdType :: ApplicativeG Id h (->) => ApplicationG Id h (->)
apIdType = ApplicationG

--------------------------------------------------------------------------------
-- Applicative -

-- | representable @__h__@s according to 'Id'.
type Applicative h = ApplicativeG Id h (->)

--------------------------------------------------------------------------------
-- amap -

-- | representation of @__h__@ in @('->')@. 
amap :: Applicative h => h x y -> x -> y
amap h x = y where Id y = amapG h (Id x)

--------------------------------------------------------------------------------
-- ($)
  
infixr 0 $

-- | right associative application on values.
($) :: Applicative h => h x y -> x -> y
($) = amap

--------------------------------------------------------------------------------
-- Applicative1 -

-- | representable @__h__@s according to @__f__@.
type Applicative1 h f = ApplicativeG f h (->)

--------------------------------------------------------------------------------
-- amap1 -

-- | representation of @__h__@ in @('->')@ according to @__f__@.
amap1 :: Applicative1 h f => h x y -> f x -> f y
amap1 = amapG

