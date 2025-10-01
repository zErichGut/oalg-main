
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE UndecidableInstances #-}
-- see comment for UndecidableInstances in OAlg.Limes.Cone.Duality

-- |
-- Module      : OAlg.Limes.Limits.Duality
-- Description : duality for limits.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- duality for 'LimitsG'.
module OAlg.Limes.Limits.Duality
  (
    -- * Mapp
    lmsMapS, lmsMapCov, lmsMapCnt
  ) where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Variant
import OAlg.Data.Either

import OAlg.Entity.Diagram

import OAlg.Limes.Cone

import OAlg.Limes.Limits.Core

--------------------------------------------------------------------------------
-- LimitsG - Dual -

type instance Dual1 (LimitsG c s p d t n m) = LimitsG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- lmsMapCov -

lmsMapCov :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> LimitsG c s p d t n m x -> LimitsG c s p d t n m y
lmsMapCov (Covariant2 i) (LimitsG u) = LimitsG u' where
  u' d' = l where
    SDualBi (Right1 l)            = amapF i (SDualBi (Right1 (u d)))
    SDualBi (Right1 (DiagramG d)) = amapF (inv2 i) (SDualBi (Right1 (DiagramG d')))

--------------------------------------------------------------------------------
-- lmsMapCnt -

lmsMapCnt :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> LimitsG c s p d t n m x -> Dual1 (LimitsG c s p d t n m) y
lmsMapCnt (Contravariant2 i) (LimitsG u) = LimitsG u' where
  u' d' = l where
    SDualBi (Left1 l)            = amapF i (SDualBi (Right1 (u d)))
    SDualBi (Left1 (DiagramG d)) = amapF (inv2 i) (SDualBi (Right1 (DiagramG d')))

--------------------------------------------------------------------------------
-- lmsMapS -

lmsMapS :: NaturalConicBi (Inv2 h) c s p d t n m
  => Inv2 h x y -> SDualBi (LimitsG c s p d t n m) x -> SDualBi (LimitsG c s p d t n m) y
lmsMapS = vmapBi lmsMapCov lmsMapCov lmsMapCnt lmsMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance NaturalConicBi (Inv2 h) c s p d t n m
  => ApplicativeG (SDualBi (LimitsG c s p d t n m)) (Inv2 h) (->) where
  amapG = lmsMapS

instance NaturalConicBi (Inv2 h) c s p d t n m
  => FunctorialG (SDualBi (LimitsG c s p d t n m)) (Inv2 h) (->)


