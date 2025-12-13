
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
-- Module      : OAlg.Limes.Cone.ZeroHead.Duality
-- Description : duality for zero head cones.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- duality for 'ConeZeroHead'. 
module OAlg.Limes.Cone.ZeroHead.Duality
  (
    -- * Mapp
    czMapS, czMapCov, czMapCnt
  ) where

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
import OAlg.Category.SDuality

import OAlg.Entity.Diagram

import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Distributive

import OAlg.Limes.Cone.Definition
import OAlg.Limes.Cone.Conic

import OAlg.Limes.Cone.ZeroHead.Core

--------------------------------------------------------------------------------
-- ConeZeroHead - Dual -

type instance Dual1 (ConeZeroHead s p d t n m)  = ConeZeroHead s (Dual p) d (Dual t) n m 

--------------------------------------------------------------------------------
-- czMapS -

czMapMltCovStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Struct Dst y
  -> Variant2 Covariant h x y -> ConeZeroHead Mlt p d t n m x -> ConeZeroHead Mlt p d t n m y
czMapMltCovStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapMltCov h c)

czMapMltCov :: 
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> ConeZeroHead Mlt p d t n m x -> ConeZeroHead Mlt p d t n m y
czMapMltCov h = czMapMltCovStruct (tau (range h)) h

czMapDstCovStruct :: 
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Struct Dst y
  -> Variant2 Covariant h x y -> ConeZeroHead Dst p d t n m x -> ConeZeroHead Dst p d t n m y
czMapDstCovStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapDstCov h c)

czMapDstCov ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> ConeZeroHead Dst p d t n m x -> ConeZeroHead Dst p d t n m y
czMapDstCov h = czMapDstCovStruct (tau (range h)) h

-- | covariant mapping of 'ConeZeroHead'
czMapCov ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> ConeZeroHead s p d t n m x -> ConeZeroHead s p d t n m y
czMapCov h cz@(ConeZeroHead c) = case c of
  ConeProjective _ _ _        -> czMapMltCov h cz
  ConeInjective _ _ _         -> czMapMltCov h cz
  ConeKernel _ _              -> czMapDstCov h cz
  ConeCokernel _ _            -> czMapDstCov h cz
  
czMapMltCntStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Struct Dst y
  -> Variant2 Contravariant h x y
  -> ConeZeroHead Mlt p d t n m x -> Dual1 (ConeZeroHead Mlt p d t n m) y
czMapMltCntStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapMltCnt h c)

czMapMltCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Contravariant h x y
  -> ConeZeroHead Mlt p d t n m x -> Dual1 (ConeZeroHead Mlt p d t n m) y  
czMapMltCnt h = czMapMltCntStruct (tau (range h)) h

czMapDstCntStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Struct Dst y
  -> Variant2 Contravariant h x y
  -> ConeZeroHead Dst p d t n m x -> Dual1 (ConeZeroHead Dst p d t n m) y
czMapDstCntStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapDstCnt h c)

czMapDstCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Contravariant h x y
  -> ConeZeroHead Dst p d t n m x -> Dual1 (ConeZeroHead Dst p d t n m) y  
czMapDstCnt h = czMapDstCntStruct (tau (range h)) h

-- | contravariant mapping of 'ConeZeroHead'
czMapCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Contravariant h x y
  -> ConeZeroHead s p d t n m x -> Dual1 (ConeZeroHead s p d t n m) y
czMapCnt h cz@(ConeZeroHead c) = case c of
  ConeProjective _ _ _        -> czMapMltCnt h cz
  ConeInjective _ _ _         -> czMapMltCnt h cz
  ConeKernel _ _              -> czMapDstCnt h cz
  ConeCokernel _ _            -> czMapDstCnt h cz

-- | mapping of 'ConeZeroHead'  
czMapS ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  , NaturalDiagrammatic h d (Dual t) n m
  , p ~ Dual (Dual p)
  )
  => h x y -> SDualBi (ConeZeroHead s p d t n m) x -> SDualBi (ConeZeroHead s p d t n m) y
czMapS = vmapBi czMapCov czMapCov czMapCnt czMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeZeroHead s p d t n m)) h (->) where
  amapG = czMapS

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (ConeZeroHead s p d t n m)) h (->)

--------------------------------------------------------------------------------
-- NaturalConic -

instance
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeG ConeZeroHead s p d t n m)) h (->) where
  amapG h = sdbFromCncObj . amapG h . sdbToCncObj

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (ConeG ConeZeroHead s p d t n m)) h (->) 

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable h (->)
       (SDualBi (ConeG ConeZeroHead Mlt p d t n m))
       (SDualBi (ConeG Cone Mlt p d t n m))

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => NaturalConic h ConeZeroHead Mlt p d t n m

