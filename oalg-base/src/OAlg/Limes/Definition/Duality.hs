
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

{-# LANGUAGE UndecidableInstances #-}
-- see comment for UndecidableInstances in OAlg.Limes.Cone.Duality

-- |
-- Module      : OAlg.Limes.Definition.Duality
-- Description : duality for a limes over a digrammatic object.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- duality of a 'Limes' over a 'Diagrammatic' object yielding a 'Conic' object.
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

lmMapCov :: NaturalConic h c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> LimesG c s p d t n m x -> LimesG c s p d t n m y
lmMapCov (Covariant2 (Inv2 t f)) (LimesProjective uc uf)
  = LimesProjective uc' uf' where
  SDualBi (Right1 (ConeG uc')) = amapF t (SDualBi (Right1 (ConeG uc)))  
  uf' c' = amap t (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF f (SDualBi (Right1 (ConeG c')))
lmMapCov (Covariant2 (Inv2 t f)) (LimesInjective uc uf)
  = LimesInjective uc' uf' where
  SDualBi (Right1 (ConeG uc')) = amapF t (SDualBi (Right1 (ConeG uc)))  
  uf' c' = amap t (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF f (SDualBi (Right1 (ConeG c')))

--------------------------------------------------------------------------------
-- lmMapCnt

lmMapCnt :: NaturalConic h c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> LimesG c s p d t n m x -> Dual1 (LimesG c s p d t n m) y
lmMapCnt (Contravariant2 (Inv2 t f)) (LimesProjective uc uf)
  = LimesInjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amap1 t (SDualBi (Right1 (ConeG uc)))
  uf' c' = amap t (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF f (SDualBi (Left1 (ConeG c')))
lmMapCnt (Contravariant2 (Inv2 t f)) (LimesInjective uc uf)
  = LimesProjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amapF t (SDualBi (Right1 (ConeG uc)))
  uf' c' = amap t (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF f (SDualBi (Left1 (ConeG c')))

--------------------------------------------------------------------------------
-- lmMapS -

lmMapS :: NaturalConicBi h c s p d t n m
  => Inv2 h x y -> SDualBi (LimesG c s p d t n m) x -> SDualBi (LimesG c s p d t n m) y
lmMapS = vmapBi lmMapCov lmMapCov lmMapCnt lmMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance NaturalConicBi h c s p d t n m
  => ApplicativeG (SDualBi (LimesG c s p d t n m)) (Inv2 h) (->) where
  amapG = lmMapS

instance NaturalConicBi h c s p d t n m
  => FunctorialG (SDualBi (LimesG c s p d t n m)) (Inv2 h) (->)
