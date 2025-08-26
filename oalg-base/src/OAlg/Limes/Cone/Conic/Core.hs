
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.Conic.Core
-- Description : basic definition for objects with a naturally underlying cone.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- basic definition for objects with a naturally underlying cone.
module OAlg.Limes.Cone.Conic.Core
  (
    -- * Conic
    Conic(..)
  , ConeG(..)

    -- * Natural
  , NaturalConic
  , crohS
{-
    -- * Duality
  , sdbToCncObj, sdbFromCncObj
  , NaturalConicDual
  , NaturalConicBi
-}
  ) where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.NaturalTransformable

import OAlg.Data.Either

import OAlg.Entity.Diagram
import OAlg.Entity.Natural

import OAlg.Hom.Multiplicative

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
croh :: Conic c => ConeG c s p d t n m x -> ConeG Cone s p d t n m x
croh (ConeG c) = ConeG (cone c)

instance Conic c => Natural r (->) (ConeG c s p d t n m) (ConeG Cone s p d t n m) where
  roh _ = croh

--------------------------------------------------------------------------------
-- crohS -

-- | natural assocition induced by 'croh' betewwn @'SDualBi' ('ConeG' __c s p d t n m__)@ and
-- @'SDualBi' ('Cone' __s p d t n m__)@.
crohS :: Conic c => SDualBi (ConeG c s p d t n m) x -> SDualBi (ConeG Cone s p d t n m) x
crohS (SDualBi (Right1 c)) = SDualBi (Right1 (croh c))
crohS (SDualBi (Left1 c')) = SDualBi (Left1 (croh c'))

instance Conic c
  => Natural r (->) (SDualBi (ConeG c s p d t n m)) (SDualBi (ConeG Cone s p d t n m)) where
  roh _ = crohS

--------------------------------------------------------------------------------
-- NaturalConic -

-- | natural transformation for 'Conic' objects from @'SDualBi' ('ConeG' __c s p d t n m__)@ to
-- @'SDualBi' ('Cone' __s p d t n m__)@.
class
  ( Conic c
  , HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d t n m
  , NaturalTransformable h (->) (SDualBi (ConeG c s p d t n m)) (SDualBi (ConeG Cone s p d t n m))
  , p ~ Dual (Dual p)
  )
  => NaturalConic h c s p d t n m

{-
--------------------------------------------------------------------------------
-- sdbToCncObj -

-- | canonical mapping to its underlying conic object.
sdbToCncObj ::
  Dual1 (c s p d t n m) ~ c s (Dual p) d (Dual t) n m
  => SDualBi (ConeG c s p d t n m) x -> SDualBi (c s p d t n m) x
sdbToCncObj (SDualBi (Right1 (ConeG c))) = SDualBi (Right1 c)
sdbToCncObj (SDualBi (Left1 (ConeG c'))) = SDualBi (Left1 c')

--------------------------------------------------------------------------------
-- sdbFromCncObj -

-- | canonical mapping from its underlying conic object.
sdbFromCncObj :: Dual1 (c s p d t n m) ~ c s (Dual p) d (Dual t) n m
  => SDualBi (c s p d t n m) x -> SDualBi (ConeG c s p d t n m) x
sdbFromCncObj (SDualBi (Right1 c)) = SDualBi (Right1 (ConeG c))
sdbFromCncObj (SDualBi (Left1 c')) = SDualBi (Left1 (ConeG c'))

--------------------------------------------------------------------------------
-- Cone - Mlt -

instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (ConeG Cone Mlt p d t n m)) h (->) where
  amapG h = sdbFromCncObj . amapG h . sdbToCncObj

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConeG Cone Mlt p d t n m)) h (->)

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable h (->)
       (SDualBi (ConeG Cone Mlt p d t n m)) (SDualBi (ConeG Cone Mlt p d t n m))

instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => NaturalConic h Cone Mlt p d t n m

--------------------------------------------------------------------------------
-- NaturalConicDual -

-- | helper class to avoid undecidable instances.
class NaturalConic h c s (Dual p) d (Dual t) n m => NaturalConicDual h c s p d t n m

instance
  ( CategoryDisjunctive h
  , HomMultiplicativeDisjunctive h
  , FunctorialOriented h    
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => NaturalConicDual h Cone Mlt p Diagram t n m
  
--------------------------------------------------------------------------------
-- NaturalConicBi -

type NaturalConicBi h c s p d t n m =
  ( NaturalConic h c s p d t n m
  , NaturalConicDual h c s p d t n m
  )
  
-}
