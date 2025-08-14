
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

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
  , NaturalConic, NaturalConicDual1
  , NaturalConicBi

  , NaturalConicSDualisable
    
  ) where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.NaturalTransformable

import OAlg.Data.Variant

import OAlg.Entity.Diagram
import OAlg.Entity.Natural

import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition

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
-- croh -

-- | the underlying cone.
croh :: Conic c => ConeG c s p d t n m x -> Cone s p d t n m x
croh (ConeG c) = cone c

instance Conic c => Natural s (->) (ConeG c s p d t n m) (Cone s p d t n m) where
  roh _ = croh

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

rel ::
  ( Conic c
  , Hom s h
  , NaturalConic h c s p d t n m
  , Eq (d t n m y)
  )
  => h x y -> c s p d t n m x -> Statement
rel h c = (amapG h c' == cnMap h c') :?> Params []
  where c' = cone c

--------------------------------------------------------------------------------
-- NaturalConicDual1 -

-- | helper class to avoid undecidable instances.
class NaturalConic h c s (Dual p) d (Dual t) n m => NaturalConicDual1 h c s p d t n m

--------------------------------------------------------------------------------
-- NaturalConicBi -

-- | constrains for conic objects @__c__@ which are bi-natural conic.
type NaturalConicBi h c s p d t n m
  = ( NaturalConic h c s p d t n m
    , NaturalConicDual1 h c s p d t n m
    )
--------------------------------------------------------------------------------
-- NaturalConicSDualisable -

-- | natural transformation for 'Conic' objects from @'SDualBi' ('ConeG' __c s p d t n m__)@ to
-- @'SDualBi' ('Cone' __s p d t n m__)@.
class
  ( Conic c
  , NaturalDiagrammaticSDualisable h d t n m
  , NaturalTransformable h (->) (SDualBi (ConeG c s p d t n m)) (SDualBi (Cone s p d t n m))
  )
  => NaturalConicSDualisable h c s p d t n m

instance
  ()
  => NaturalTransformable (Variant2 Covariant (HomDisj s o h)) (->)
       (ConeG c Mlt p d t n m) (Cone Mlt p d t n m)

instance
  ( NaturalDiagrammaticBi h d t n m
  , DualisableDiagrammatic s o d t n m
  )
  => NaturalConic (Variant2 Covariant (HomDisj s o h)) c Mlt p d t n m

