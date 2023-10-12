
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Data.Dualisable
-- Description : concept of duality
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- data admitting a kind of duality.
module OAlg.Data.Dualisable
  ( -- * Dual
    Dual

    -- * Dualisable
  , Dualisable(..), fromDual'

    -- * Reflexive
  , Reflexive(..), fromBidual'

    -- * Transposable
  , Transposable(..)

    -- * Site
  , Site(..)

    -- * Side
  , Side(..)

    -- * Direction
  , Direction(..)
  )
  where

--------------------------------------------------------------------------------
-- Dual -

-- | the assigned dual kind.
type family Dual (x :: k) :: k

--------------------------------------------------------------------------------
-- Dualisable -

-- | admitting a duality.
--
--   __Property__ Let __@x@__ be 'Dualisable', than holds: 'toDual' is a bijection
--   with its inverse 'fromDual'.
class Dualisable x where
  toDual   :: x -> Dual x
  fromDual :: Dual x -> x

--------------------------------------------------------------------------------
-- fromDual' -

-- | 'fromDual' enriched with a parameterized type __@p@__ which serves as a proxy -
--   e.g. 'Data.Proxy.Proxy' or 'OAlg.Data.Identity.Id' will serve - and will not be evaluated.
--   It serves for the type checker to pick the right 'fromDual'.
fromDual' :: Dualisable x => p x -> Dual x -> x
fromDual' _ = fromDual

--------------------------------------------------------------------------------
-- Reflexive -

-- | admitting reflection.
--
--   __Property__ Let __@x@__ be 'Reflexive', than holds:
--
--   (1) 'toBidual' is a bijection with its inverse 'fromBidual'.
class Reflexive x where
  toBidual   :: x -> Dual (Dual x)
  fromBidual :: Dual (Dual x) -> x

-- | 'fromBidual' enriched with a parameterized type __@p@__ which serves as a proxy -
--   e.g. 'Proxy' or 'OAlg.Data.Identity.Id' will serve - and will not be evaluated.
--   It serves for the type checker to pick the right 'fromBidual'.
fromBidual' :: Reflexive x => p x -> Dual (Dual x) -> x
fromBidual' _ = fromBidual

--------------------------------------------------------------------------------
-- Transposable -

-- | transposable types..
--
--   __Property__ Let __@x@__ be a 'Transposable', then holds:
--  For all @x@ in __@x@__ holds: @'transpose' ('transpose' x) '==' x@.
class Transposable x where 
  transpose :: x -> x

--------------------------------------------------------------------------------
-- Site -

-- | concept of the sites 'From' and 'To'.
data Site = From | To deriving (Show,Eq,Ord,Enum,Bounded)

type instance Dual From = To
type instance Dual To = From

instance Transposable Site where
  transpose From = To
  transpose To = From

--------------------------------------------------------------------------------
-- Side -

-- | concept of sides 'LeftSide' and 'RightSide'
data Side = LeftSide | RightSide deriving (Show,Eq,Ord,Enum,Bounded)

type instance Dual LeftSide = RightSide
type instance Dual RightSide = LeftSide

instance Transposable Side where
  transpose LeftSide = RightSide
  transpose RightSide = LeftSide

--------------------------------------------------------------------------------
-- Direction -

-- | concept of the directions 'LeftToRight' and 'RightToLeft'.
data Direction = LeftToRight | RightToLeft deriving (Show,Eq,Ord,Enum,Bounded)

type instance Dual LeftToRight = RightToLeft
type instance Dual RightToLeft = LeftToRight

instance Transposable Direction where
  transpose LeftToRight = RightToLeft
  transpose RightToLeft = LeftToRight

