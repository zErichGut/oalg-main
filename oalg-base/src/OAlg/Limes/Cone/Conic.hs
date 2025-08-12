
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.Conic
-- Description : objects with a naturally underlying cone.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- objects with a naturally underlying cone.
module OAlg.Limes.Cone.Conic
  (
    -- * Conic
    Conic(..), ConeG(..)

    -- * Natural
  , NaturalConic
    
  ) where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.NaturalTransformable


import OAlg.Entity.Diagram
import OAlg.Entity.Natural

import OAlg.Limes.Cone.Definition

--------------------------------------------------------------------------------
-- Conic -

-- | object @__c__@ having an underlying 'Cone'.
class Conic c where
  cone :: c s p d t n m x -> Cone s p d t n m x

instance Conic Cone where cone = id

--------------------------------------------------------------------------------
-- ConeG -

-- | wrapper for 'Conic'-objects.
newtype ConeG (c :: Type -> Perspective
                 -> (DiagramType -> N' -> N' -> Type -> Type)
                 -> DiagramType -> N' -> N'
                 -> Type
                 -> Type
              ) s p d t n m x
  = ConeG (c s p d t n m x)
  deriving (Show,Eq)

type instance Dual1 (ConeG c s p d t n m) = ConeG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- NaturalConic -

-- | natural transformation for 'Conic' objects.
--
-- (1) @'amapG' h '.=. 'cnMap' h@,
class
  ( NaturalDiagrammatic h d t n m
  , NaturalTransformable h (->) (ConeG c s p d t n m) (Cone s p d t n m)
  )
  => NaturalConic h c s p d t n m

-- class Hom s h => Hom' s h

-- type N h c s p d t n m = (Hom s h, NaturalConic h c s p d t n m)

rel ::
  ( Conic c
  , Hom s h
  , NaturalConic h c s p d t n m
  , Eq (d t n m y)
  )
  => h x y -> c s p d t n m x -> Statement
rel h c = (amapG h c' == cnMap h c') :?> Params []
  where c' = cone c
