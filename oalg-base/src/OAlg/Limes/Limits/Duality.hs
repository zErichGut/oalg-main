
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
import OAlg.Limes.Definition

import OAlg.Limes.Limits.Core

--------------------------------------------------------------------------------
-- LimitsG - Dual -

type instance Dual1 (LimitsG c s p d t n m) = LimitsG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- lmsMapCov -

lmsMapCov :: NaturalConic h c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> LimitsG c s p d t n m x -> LimitsG c s p d t n m y
lmsMapCov i@(Covariant2 (Inv2 _ f)) (LimitsG u) = LimitsG u' where
  u' d' = lmMapCov i (u d) where
    SDualBi (Right1 (DiagramG d)) = amapF f (SDualBi (Right1 (DiagramG d'))) 

--------------------------------------------------------------------------------
-- lmsMapCnt -

lmsMapCnt :: NaturalConic h c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> LimitsG c s p d t n m x -> Dual1 (LimitsG c s p d t n m) y
lmsMapCnt i@(Contravariant2 (Inv2 _ f)) (LimitsG u) = LimitsG u' where
  u' d' = lmMapCnt i (u d) where
    SDualBi (Right1 (DiagramG d)) = amapF f (SDualBi (Left1 (DiagramG d'))) 

--------------------------------------------------------------------------------
-- lmsMapS -

lmsMapS ::
  ( NaturalConic h c s p d t n m
  , NaturalConic h c s (Dual p) d (Dual t) n m
  )
  => Inv2 h x y -> SDualBi (LimitsG c s p d t n m) x -> SDualBi (LimitsG c s p d t n m) y
lmsMapS = vmapBi lmsMapCov lmsMapCov lmsMapCnt lmsMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance NaturalConicBi h c s p d t n m
  => ApplicativeG (SDualBi (LimitsG c s p d t n m)) (Inv2 h) (->) where
  amapG = lmsMapS

instance NaturalConicBi h c s p d t n m
  => FunctorialG (SDualBi (LimitsG c s p d t n m)) (Inv2 h) (->)

