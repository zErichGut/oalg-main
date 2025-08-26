
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

{-# LANGUAGE UndecidableInstances #-}
-- we allow undecidable instances to use NaturalConicBi as constraint for
-- the functorial property for cones! As such we separated this
-- declaration in a separate module.
--
-- the problem in the constraint is NaturalDiagrammatic h d (Dual t) n m,
-- but the kind of the type t is DiagramType and as such this should not
-- cause prblems...hopfully.

-- |
-- Module      : OAlg.Limes.Cone.Duality
-- Description : definition of duality of cones.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of duality for 'Cone's over 'Diagrammatic' objects.
module OAlg.Limes.Cone.Duality
  (
    -- * Map
    cnMapS  
    -- ** Covariant
  , cnMapCov, cnMapMltCov, cnMapDstCov
  , cnMap, cnMapMlt, cnMapDst

    -- ** Contravariant
  , cnMapCnt, cnMapMltCnt, cnMapDstCnt
  ) where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either

import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive
import OAlg.Hom.Definition

import OAlg.Limes.Cone.Core

--------------------------------------------------------------------------------
-- Cone - Duality -

type instance Dual1 (Cone s p d t n m) = Cone s (Dual p) d (Dual t) n m

instance (Show x, ShowPoint x) => ShowDual1 (Cone s p Diagram t n m) x
instance (Eq x, EqPoint x) => EqDual1 (Cone s p Diagram t n m) x

--------------------------------------------------------------------------------
-- cnMapCov -

-- | mapping of a cone under a 'Multiplicative' covariant homomorphism.
cnMapMltCov ::
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> Cone Mlt p d t n m x -> Cone Mlt p d t n m y
cnMapMltCov (Covariant2 h) c            = case tauMlt (range h) of
  Struct                  -> case c of
    ConeProjective d t as -> ConeProjective d' (pmap h t) (amap1 (amap h) as) where
      SDualBi (Right1 (DiagramG d')) = amapF h (SDualBi (Right1 (DiagramG d)))
    ConeInjective d t as  -> ConeInjective d' (pmap h t) (amap1 (amap h) as) where
      SDualBi (Right1 (DiagramG d')) = amapF h (SDualBi (Right1 (DiagramG d)))

-- | mapping of a cone under a 'Distributive' covariant homomorphism.
cnMapDstCov ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> Cone Dst p d t n m x -> Cone Dst p d t n m y
cnMapDstCov (Covariant2 h) c = case tauDst (range h) of
  Struct                    -> case c of
    ConeKernel d a          -> ConeKernel d' (amap h a) where
      SDualBi (Right1 (DiagramG d')) = amapF h (SDualBi (Right1 (DiagramG d)))
    ConeCokernel d a        -> ConeCokernel d' (amap h a) where
      SDualBi (Right1 (DiagramG d')) = amapF h (SDualBi (Right1 (DiagramG d)))

cnMapCov ::
  ( HomD s h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> Cone s p d t n m x -> Cone s p d t n m y
cnMapCov h c = case c of
  ConeProjective _ _ _ -> cnMapMltCov h c
  ConeInjective _ _ _  -> cnMapMltCov h c
  ConeKernel _ _       -> cnMapDstCov h c
  ConeCokernel _ _     -> cnMapDstCov h c
  
--------------------------------------------------------------------------------
-- cnMap -

-- | mapping of a cone under a 'Multiplicative' homomorphism.
cnMapMlt ::
  ( HomMultiplicative h
  , t ~ Dual (Dual t)
  )
  => h x y -> Cone Mlt p Diagram t n m x -> Cone Mlt p Diagram t n m y
cnMapMlt h = cnMapMltCov (hCov h) where
    hCov :: HomMultiplicative h => h x y -> Variant2 Covariant (HomDisj Mlt Op h) x y
    hCov = homDisj

-- | mapping of a cone under a 'Distributive' homomorphism.
cnMapDst ::
  ( HomDistributive h
  , t ~ Dual (Dual t)
  )
  => h x y -> Cone Dst p Diagram t n m x -> Cone Dst p Diagram t n m y
cnMapDst h = cnMapDstCov (hCov h) where
    hCov :: HomDistributive h => h x y -> Variant2 Covariant (HomDisj Dst Op h) x y
    hCov = homDisj

-- | mapping of a cone under a @__s__@ homomorphism.
cnMap ::
  ( Hom s h
  , t ~ Dual (Dual t)
  )
  => h x y -> Cone s p Diagram t n m x -> Cone s p Diagram t n m y
cnMap h c = case c of
  ConeProjective _ _ _ -> cnMapMlt h c
  ConeInjective _ _ _  -> cnMapMlt h c
  ConeKernel _ _       -> cnMapDst h c
  ConeCokernel _ _     -> cnMapDst h c
  
--------------------------------------------------------------------------------
-- cnMapCnt -

-- | mapping of a cone under a 'Multiplicative' contravariant homomorphism.
cnMapMltCnt ::
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Contravariant h x y
  -> Cone Mlt p d t n m x -> Dual1 (Cone Mlt p d t n m) y
cnMapMltCnt (Contravariant2 h) c = case tauMlt (range h) of
  Struct                        -> case c of
    ConeProjective d t as       -> ConeInjective d' (pmap h t) (amap1 (amap h) as) where
      SDualBi (Left1 (DiagramG d')) = amapF h (SDualBi (Right1 (DiagramG d)))
    ConeInjective d t as        -> ConeProjective d' (pmap h t) (amap1 (amap h) as) where
      SDualBi (Left1 (DiagramG d')) = amapF h (SDualBi (Right1 (DiagramG d)))

-- | mapping of a cone under a 'Distributive' contravariant homomorphism.
cnMapDstCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Contravariant h x y
  -> Cone Dst p d t n m x -> Dual1 (Cone Dst p d t n m) y
cnMapDstCnt (Contravariant2 h) c = case tauDst (range h) of
  Struct                        -> case c of
    ConeKernel d a              -> ConeCokernel d' (amap h a) where
      SDualBi (Left1 (DiagramG d')) = amapF h (SDualBi (Right1 (DiagramG d)))
    ConeCokernel d a            -> ConeKernel  d' (amap h a) where
      SDualBi (Left1 (DiagramG d')) = amapF h (SDualBi (Right1 (DiagramG d)))

-- | mapping of a cone under a contravariant homomorphism.
cnMapCnt :: (HomD s h, NaturalDiagrammatic h d t n m)
  => Variant2 Contravariant h x y
  -> Cone s p d t n m x -> Dual1 (Cone s p d t n m) y
cnMapCnt h c = case c of
  ConeProjective _ _ _ -> cnMapMltCnt h c
  ConeInjective _ _ _  -> cnMapMltCnt h c
  ConeKernel _ _       -> cnMapDstCnt h c
  ConeCokernel _ _     -> cnMapDstCnt h c

--------------------------------------------------------------------------------
-- cnMapS -

cnMapS ::
  ( HomD s h
  , NaturalDiagrammatic h d t n m
  , NaturalDiagrammatic h d (Dual t) n m
  , p ~ Dual (Dual p)
  )
  => h x y -> SDualBi (Cone s p d t n m) x -> SDualBi (Cone s p d t n m) y
cnMapS = vmapBi cnMapCov cnMapCov cnMapCnt cnMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

-- it is not possible to use the constraint HomD s h to make the declaration more generic!
instance
  ( HomMultiplicativeDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (Cone Mlt p d t n m)) h (->) where
  amapG = cnMapS
  
instance
  ( HomMultiplicativeDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (Cone Mlt p d t n m)) h (->)
  
instance
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (Cone Dst p d t n m)) h (->) where
  amapG = cnMapS
  
instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (Cone Dst p d t n m)) h (->)

