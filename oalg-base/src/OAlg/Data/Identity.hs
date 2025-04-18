
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
  ( Id(..)
  , fromId
  , trafoFromId
  , trafoToId
  , toIdG, fromIdG
  )
  where

--------------------------------------------------------------------------------
-- Id -

-- | identical predicate.
newtype Id x = Id x
  deriving ( Show,Read,Eq,Ord,Enum,Bounded
           , Functor
           , Foldable
           )

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
toIdG = fmap

--------------------------------------------------------------------------------
-- fromIdG -

fromIdG :: (Id x -> Id y) -> x -> y
fromIdG i = fromId . i . Id 
