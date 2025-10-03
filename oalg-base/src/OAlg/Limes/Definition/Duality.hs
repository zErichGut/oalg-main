
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE UndecidableInstances #-}
-- see comment for UndecidableInstances in OAlg.Limes.Cone.Duality

-- |
-- Module      : OAlg.Limes.Definition.Duality
-- Description : duality for a limes over a digrammatic object.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- duality of a 'Limes' over a 'OAlg.Entity.Diagram.Diagrammatic.Diagrammatic' object yielding
-- a 'Conic' object.
module OAlg.Limes.Definition.Duality
  (
    -- * Mapping
    lmMapS, lmMapCov, lmMapCnt

  ) where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Limes.Cone

import OAlg.Limes.Definition.Core

--------------------------------------------------------------------------------
-- LimesG - Dual -

type instance Dual1 (LimesG c s p d t n m) = LimesG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- lmMapCov -

-- | covariant mapping of 'LimesG'
lmMapCov :: NaturalConic (Inv2 h) c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> LimesG c s p d t n m x -> LimesG c s p d t n m y
lmMapCov (Covariant2 i) (LimesProjective uc uf)
  = LimesProjective uc' uf' where
  SDualBi (Right1 (ConeG uc')) = amapF i (SDualBi (Right1 (ConeG uc)))  
  uf' c' = amapf i (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF (inv2 i) (SDualBi (Right1 (ConeG c')))
lmMapCov (Covariant2 i) (LimesInjective uc uf)
  = LimesInjective uc' uf' where
  SDualBi (Right1 (ConeG uc')) = amapF i (SDualBi (Right1 (ConeG uc)))  
  uf' c' = amapf i (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF (inv2 i) (SDualBi (Right1 (ConeG c')))

--------------------------------------------------------------------------------
-- lmMapCnt -

-- | contravariant mapping of 'LimesG'
lmMapCnt :: NaturalConic (Inv2 h) c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> LimesG c s p d t n m x -> LimesG c s (Dual p) d (Dual t) n m y
lmMapCnt (Contravariant2 i) (LimesProjective uc uf)
  = LimesInjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amapF i (SDualBi (Right1 (ConeG uc)))
  uf' c' = amapf i (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF (inv2 i) (SDualBi (Left1 (ConeG c')))

lmMapCnt (Contravariant2 i) (LimesInjective uc uf)
  = LimesProjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amapF i (SDualBi (Right1 (ConeG uc)))
  uf' c' = amapf i (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF (inv2 i) (SDualBi (Left1 (ConeG c')))


--------------------------------------------------------------------------------
-- lmMapS -

-- | mapping of 'LimesG'
lmMapS :: NaturalConicBi (Inv2 h) c s p d t n m
  => Inv2 h x y -> SDualBi (LimesG c s p d t n m) x -> SDualBi (LimesG c s p d t n m) y
lmMapS = vmapBi lmMapCov lmMapCov lmMapCnt lmMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance NaturalConicBi (Inv2 h) c s p d t n m
  => ApplicativeG (SDualBi (LimesG c s p d t n m)) (Inv2 h) (->) where
  amapG = lmMapS

instance NaturalConicBi (Inv2 h) c s p d t n m
  => FunctorialG (SDualBi (LimesG c s p d t n m)) (Inv2 h) (->)
