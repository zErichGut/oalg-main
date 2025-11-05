
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
  , abhCnzf, abhCnzfHomology

  , homologyClass, boundary, boundaryInv
    
    -- * Homomorphism
  , homologyHom, HomologyHom
  , homologyGroupsHom
  , abhCnzfh, abhCnzfhHomologyHom

  , ConsecutiveZeroFreeHom(..)

  ) where

import Control.Monad

import Data.Typeable

import Data.Foldable (toList)
import Data.List as L (zip,filter, (++))

import OAlg.Prelude

import OAlg.Data.FinitelyPresentable

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential
import OAlg.Structure.Distributive
import OAlg.Structure.Operational

import OAlg.Entity.Diagram as D 
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Slice
import OAlg.Entity.Slice.Liftable
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence.PSequence

import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels
import OAlg.AbelianGroup.Liftable
import OAlg.AbelianGroup.ZMod hiding (NotEligible)

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

import OAlg.Adjunction.Definition

--------------------------------------------------------------------------------
-- Homology -

-- | homology.
type Homology n = VarianceFreeLiftable To n AbHom

--------------------------------------------------------------------------------
-- abhCnzf -

abhCnzf :: Simplical s x => ChainComplex t Z s n x -> ConsecutiveZeroFree To n AbHom
abhCnzf = toFree . ccxRepMatrix where
  
  toFree :: ConsecutiveZero To n (Matrix Z) -> ConsecutiveZeroFree To n AbHom
  toFree ds = ConsecutiveZeroFree ds' fs where
    ds' = cnzMapCov (homDisjOpDst FreeAbHom) ds
    fs  = amap1 (fromJust . abgSomeFree) $ tail $ dgPoints $ cnzDiagram ds'

--------------------------------------------------------------------------------
-- abhCnzfHomology -

abhCnzfHomology :: ConsecutiveZeroFree To n AbHom -> Homology n
abhCnzfHomology = varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree

--------------------------------------------------------------------------------
-- homology -

-- | the induced homology of a complex.
homology :: Simplical s x => ChainComplex t Z s n x -> Homology n
homology = abhCnzfHomology . abhCnzf

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
-- abhCnzfh -

abhCnzfh :: Homological s x y => ChainComplexHom t Z s n x y -> ConsecutiveZeroFreeHom To n AbHom
abhCnzfh h@(ChainComplexHom a b _) = ConsecutiveZeroFreeHom a' b' fs' where
  a'  = abhCnzf a
  b'  = abhCnzf b
  ConsecutiveZeroHom (DiagramTrafo _ _ ts) = ccxRepMatrixHom h
  fs' = amap1 (amap FreeAbHom) ts

--------------------------------------------------------------------------------
-- cnzfhHomologyHom -

abhCnzfhHomologyHom :: ConsecutiveZeroFreeHom To n AbHom -> HomologyHom n
abhCnzfhHomologyHom (ConsecutiveZeroFreeHom a b fs) = VarianceHomG a' b' fs where
  a' = abhCnzfHomology a
  b' = abhCnzfHomology b

--------------------------------------------------------------------------------
-- homologyHom -

-- | the induced homomorphism between homologies.
homologyHom :: Homological s x y => ChainComplexHom t Z s n x y -> HomologyHom n
homologyHom = abhCnzfhHomologyHom . abhCnzfh

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

-- | the boundary of an abelian element.
boundary :: Homology n -> AbElement -> Eval AbElement
boundary (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) _) e
  | start d /= end e  = failure $ NotEligible "boundary"
  | otherwise         = return (d *> e)

--------------------------------------------------------------------------------
-- boundaryInv -

-- | determines the bounary of a given cycle with zero homology class.
boundaryInv :: Homology n -> AbElement -> Eval AbElement
boundaryInv hmg e = do
  h <- homologyClass hmg e
  case isZero h of
    True               -> case universalCone ker of
      ConicFreeTip k _ -> case abhLift (SliceTo k e'' :> SliceTo k d'') of
        Just e'''      -> return $ AbElement $ SliceFrom k1 $ slfFactor e'''
        Nothing        -> failure $ EvalFailure "implementation error!"
                          -- as h is zero, e' should be liftable!
    False -> failure $ NonZeroHomologyClass h

  where
    VarianceG (ConsecutiveZero (DiagramChainTo _ (_:|d':|_))) ((ker,_):|_) = hmg
    AbElement e'   = e
    SliceFrom k1 _ = e'

    e'' = universalFactor ker (ConeKernel (universalDiagram ker) (slice e'))
    d'' = universalFactor ker (ConeKernel (universalDiagram ker) d')

    
