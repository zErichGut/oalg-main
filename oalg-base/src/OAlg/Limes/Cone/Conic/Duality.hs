
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

{-# LANGUAGE UndecidableInstances #-}
-- see comment for UndecidableInstances in OAlg.Limes.Cone.Duality

-- |
-- Module      : OAlg.Limes.Cone.Conic.Duality
-- Description : duality for conic objects.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- duality for conic objects.
module OAlg.Limes.Cone.Conic.Duality
  (
    -- * Duality
    NaturalConicBi

    -- * Map
  , sdbToCncObj, sdbFromCncObj
    
  ) where

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.NaturalTransformable

import OAlg.Data.Either

import OAlg.Entity.Diagram

import OAlg.Structure.Multiplicative

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone.Definition

import OAlg.Limes.Cone.Conic.Core

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

{-
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
-}

--------------------------------------------------------------------------------
-- NaturalConicBi -

type NaturalConicBi h c s p d t n m =
  ( NaturalConic h c s p d t n m
  , NaturalConic h c s (Dual p) d (Dual t) n m
  )
  
