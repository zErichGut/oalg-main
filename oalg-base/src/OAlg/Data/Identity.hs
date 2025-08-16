
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

-- |
-- Module      : OAlg.Data.Identity
-- Description : identical predicate
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- identical predicate.
module OAlg.Data.Identity
  (
    -- * Id
    Id(..)
  , fromId
  , trafoFromId
  , trafoToId
  , toIdG, fromIdG

    -- * Applicative
  , Applicative, amap, ($)
  , Functorial, Functor

    -- * Id2
  , Id2(..)
  )
  where

import Prelude (Show,Read,Eq,Ord,Enum,Bounded,Foldable)

import OAlg.Category.Definition
import OAlg.Category.Applicative

--------------------------------------------------------------------------------
-- Id -

-- | identical predicate.
newtype Id x = Id x deriving (Show,Read,Eq,Ord,Enum,Bounded,Foldable)

instance ApplicativeG Id h c => ApplicativeG Id (Inv2 h) c where amapG (Inv2 t _) = amapG t
--------------------------------------------------------------------------------
-- formId -

-- | deconstructs 'Id'.
fromId :: Id x -> x
fromId (Id x) = x

--------------------------------------------------------------------------------
-- trafoFromId -

-- | transforming a @f :: x -> 'Id' y@ to a @f' :: x -> i z@.
trafoFromId :: (y -> i z) -> (x -> Id y) -> x -> i z
trafoFromId i f x = i y where Id y = f x

--------------------------------------------------------------------------------
-- trafoToId -

-- | transforming a @f :: x -> y@ to a @f' :: x -> Id y@.
trafoToId :: (x -> y) -> x -> Id y
trafoToId f = Id . f

--------------------------------------------------------------------------------
-- toIdG -

toIdG :: (x -> y) -> Id x -> Id y
toIdG f (Id x) = Id (f x)

--------------------------------------------------------------------------------
-- fromIdG -

fromIdG :: (Id x -> Id y) -> x -> y
fromIdG i = fromId . i . Id 

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
-- Functorial -

instance ApplicativeG Id (->) (->) where amapG = toIdG

-- | functorials form @__c__@ to @('->')@ according to 'Id'.
type Functorial c = FunctorialG Id c (->)

--------------------------------------------------------------------------------
-- Functor -

-- | attest of being 'Functorial' from the 'Category' __c__ to the 'Category' @('->')@.
data Functor c where
  Functor :: Functorial c => Functor c  

--------------------------------------------------------------------------------
-- Id2 -

-- | identical predicat.
newtype Id2 h x y = Id2 (h x y)

instance Morphism h => Morphism (Id2 h) where
  type ObjectClass (Id2 h) = ObjectClass h
  homomorphous (Id2 h) = homomorphous h

instance ApplicativeG Id h c => ApplicativeG Id (Id2 h) c where
  amapG (Id2 h) = amapG h



