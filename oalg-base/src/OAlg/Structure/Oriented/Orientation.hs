
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}


-- |
-- Module      : OAlg.Structure.Oriented.Orientation
-- Description : defining a orientation on a type.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- defining a orientation on a type.
module OAlg.Structure.Oriented.Orientation
  (
    -- * Orientation
    Orientation(..), opposite
  , OS

    -- * Applicative
  , omap
  ) where

import Control.Monad

import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Singleton
import OAlg.Data.Symbol

import OAlg.Structure.Oriented.Point

--------------------------------------------------------------------------------
-- Orientation -

infix 5 :>
  
-- | orientation given by the start point as its first component and the end point as its
--   second.
--
--  __Property__ For all @o@ in __@'Orientation' p@__ holds:
--  @o '==' 'start' o ':>' 'end' o@.
--
--  __Note__ As 'Orientation's are instances of almost all algebraic structures
--  defined here, they serve as a /proof/ that this structures are instanceable.
data Orientation p = p :> p deriving (Show,Eq,Ord)

instance Validable p => Validable (Orientation p) where
  valid (s :> e) = And [valid s,valid e]

instance Singleton u => Singleton (Orientation u) where
  unit = unit :> unit

instance ApplicativeG Orientation (->) (->) where
  amapG f (a :> b) = f a :> f b

instance XStandard p => XStandard (Orientation p) where
  xStandard = xTupple2 xStandard xStandard >>= return . uncurry (:>)

--------------------------------------------------------------------------------
-- opposite -

-- | the opposite orientation.
opposite :: Orientation p -> Orientation p
opposite (s:>e) = e:>s

instance Transposable (Orientation p) where
  transpose = opposite

--------------------------------------------------------------------------------
-- OS -

-- | as @'Orientation' p@ is an instance of almost every structured class it
--   serves as a standard type for validating.
type OS = Orientation Symbol

--------------------------------------------------------------------------------
-- Point - Orientation -

type instance Point (Orientation x) = x

instance Show x => ShowPoint (Orientation x)
instance Eq x => EqPoint (Orientation x)
instance Ord x => OrdPoint (Orientation x)
instance Singleton x => SingletonPoint (Orientation x)
instance Validable x => ValidablePoint (Orientation x)
instance Typeable x => TypeablePoint (Orientation x)
instance XStandard p => XStandardPoint (Orientation p)

--------------------------------------------------------------------------------
-- omap -

-- | the induced mapping of 'Orientation'.
omap :: ApplicativePoint h => h a b -> Orientation (Point a) -> Orientation (Point b)
omap = amapG . pmap


