
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Definition
-- Description : homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homology.
module OAlg.Homology.Definition
  (

    -- * Homology
    homology, Homology
  , homologyGroups
  , hmgCycles, hmgClassGenerators

  , homologyClass, boundary
    
    -- * Homomorphism
  , homologyHom, HomologyHom
  , homologyGroupsHom


  ) where

import Control.Monad

import Data.Foldable (toList)

import OAlg.Prelude

import OAlg.Data.FinitelyPresentable

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Operational

import OAlg.Entity.Diagram hiding (Chain)
import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Slice
import OAlg.Entity.Slice.Liftable
import OAlg.Entity.Matrix

import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.Free

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex

import OAlg.Homology.Eval.Core


--------------------------------------------------------------------------------
-- Homology -

-- | homology.
type Homology n = VarianceFreeLiftable To n AbHom

--------------------------------------------------------------------------------
-- homology -

-- | the induced homology of a complex.
homology :: Simplical s x => ChainComplex t Z s n x -> Homology n
homology ds = varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree
            $ toFree
            $ ccxRepMatrix ds where
  
  toFree :: ConsecutiveZero To n (Matrix Z) -> ConsecutiveZeroFree To n AbHom
  toFree ds = ConsecutiveZeroFree ds' fs where
    ds' = cnzMapCov (homDisjOpDst FreeAbHom) ds
    fs  = amap1 (fromJust . abgSomeFree) $ tail $ dgPoints $ cnzDiagram ds'
    
--------------------------------------------------------------------------------
-- homologyGroups -

-- | the homology groups.
homologyGroups :: Attestable n => Homology n -> Deviation (n+1) AbHom
homologyGroups = deviationsTo

--------------------------------------------------------------------------------
-- HomologyHom -

-- | homomorphism between homologies.
type HomologyHom n = VarianceFreeLiftableHom To n AbHom

--------------------------------------------------------------------------------
-- homologyHom -

-- | the induced homomorphism between homologies.
homologyHom :: Homological s x y => ChainComplexHom t Z s n x y -> HomologyHom n
homologyHom h@(ChainComplexHom a b _) = VarianceHomG a' b' fs' where
  a' = homology a
  b' = homology b
  ConsecutiveZeroHom (DiagramTrafo _ _ ts) = ccxRepMatrixHom h
  fs' = amap1 (amap FreeAbHom) ts

--------------------------------------------------------------------------------
-- hmgGroupsHom -

-- | homomorphism between the homology groups.
homologyGroupsHom :: Attestable n => HomologyHom n -> DeviationHom (n+1) AbHom
homologyGroupsHom = deviationHomG (Struct :: Struct (Dst,SldFr) AbHom)

--------------------------------------------------------------------------------
-- hmgCycles -

-- | list of cycles generating the sub group of cycles for the head homology.  
hmgCycles :: Homology n -> [AbElement]
hmgCycles (VarianceG _ ((ker,_):|_)) = case universalCone ker of
  ConicFreeTip _ cn -> amap1 (k*>) $ abges $ start k where k = kernelFactor cn

--------------------------------------------------------------------------------
-- hmgClassGenerators -

-- | list of cycles genrating the homology group for the head homology.
hmgClassGenerators :: Homology n -> [AbElement]
hmgClassGenerators (VarianceG _ ((ker,coker):|_))
  = case finitePresentation abgFinPres (tip $ cone cCn) of
      GeneratorTo (DiagramChainTo _ (g:|_)) k'@(Free a) _ _ _ _
        -> toList $ amap1 AbElement $ split abhSplitable $ (k*>)
         $ lift (liftFree cLft a) (SliceFrom k' g)
  where
    ConeCokernelLiftable cCn cLft = universalCone coker
    k = kernelFactor $ universalCone ker

--------------------------------------------------------------------------------
-- hmgBoundaryOperator -

-- | the boundary operators of the head homology.
hmgBoundaryOperator :: Homology n -> ConsecutiveZero To N0 AbHom
hmgBoundaryOperator (VarianceG cs _) = cnzHead cs

--------------------------------------------------------------------------------
-- hmgChain -

-- | the abelian group of chains for the head homology.
hmgChain :: Homology n -> AbGroup
hmgChain (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) _) = start d

--------------------------------------------------------------------------------
-- homologyClass -

-- | the homology class of a cycle in the head homology.
homologyClass :: Homology n -> AbElement -> Eval AbElement
homologyClass (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) ((ker,coker):|_)) e
  | start d /= end e      = failure $ NotEligible "homologyClass"
  | not (isZero (d *> e)) = failure $ NotCycle "homologyClass"
  | otherwise = return (c *> e')

  where
    AbElement (SliceFrom k1 eh) = e
    c   = cokernelFactor $ universalCone coker
    eh' = universalFactor ker (ConeKernel (universalDiagram ker) eh)
    e'  = AbElement (SliceFrom k1 eh')

--------------------------------------------------------------------------------
-- boundary -

boundary :: Homology n -> AbElement -> Eval AbElement
boundary (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) _) e
  | start d /= end e  = failure $ NotEligible "boundary"
  | otherwise         = return (d *> e)
