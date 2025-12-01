
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
  
    -- * Homomorphism
  , homologyHom, HomologyHom
  , homologyGroupsHom

    -- * Homological
  , Homological(..)

    -- * Abelian
  , cnzFreeAbl, cnzFreeHomAbl
  ) where

import Control.Monad

import Data.Foldable (toList)

import OAlg.Prelude

import OAlg.Data.FinitelyPresentable

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Operational

import OAlg.Entity.Diagram as D 
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Slice
import OAlg.Entity.Slice.Liftable
import OAlg.Entity.Matrix

import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels
import OAlg.AbelianGroup.Liftable

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.Free

import OAlg.Homology.ChainComplex

import OAlg.Homology.Eval.Core


--------------------------------------------------------------------------------
-- Homology -

type Homology = VarianceFreeLiftable To

--------------------------------------------------------------------------------
-- Homological -

class (Distributive h, SlicedFree h) => Homological h where
  kernelsSomeFreeTip        :: KernelsSomeFreeFreeTip h
  cokernelsLiftableSomeFree :: CokernelsG ConeLiftable SomeFreeSliceDiagram N1 h

instance Homological AbHom where
  kernelsSomeFreeTip        = abhKernelsSomeFreeFreeTip
  cokernelsLiftableSomeFree = abhCokernelsLiftableSomeFree

--------------------------------------------------------------------------------
-- homology -

homology :: Homological h => ConsecutiveZeroFree To n h -> Homology n h
homology = varianceFreeTo kernelsSomeFreeTip cokernelsLiftableSomeFree

--------------------------------------------------------------------------------
-- homologyGroups -

-- | the homology groups.
homologyGroups :: (Attestable n, Distributive h) => Homology n h -> Deviation (n+1) h
homologyGroups = deviationsTo

--------------------------------------------------------------------------------
-- cnzFreeAbl -

cnzFreeAbl :: ConsecutiveZero To n (Matrix Z) -> ConsecutiveZeroFree To n AbHom
cnzFreeAbl ds = ConsecutiveZeroFree ds' fs where
  ds' = cnzMapCov (homDisjOpDst FreeAbHom) ds
  fs  = amap1 (fromJust . abgSomeFree) $ tail $ dgPoints $ cnzDiagram ds'

--------------------------------------------------------------------------------
-- HomologyHom -

type HomologyHom = VarianceFreeLiftableHom To

--------------------------------------------------------------------------------
-- homologyHom -

homologyHom :: Homological h => ConsecutiveZeroFreeHom To n h -> HomologyHom n h
homologyHom (ConsecutiveZeroFreeHom a b fs) = VarianceHomG a' b' fs where
  a' = homology a
  b' = homology b

--------------------------------------------------------------------------------
-- homologyGroupsHom -

homologyGroupsHom :: (Distributive h, SlicedFree h, Attestable n)
  => HomologyHom n h -> DeviationHom (n+1) h
homologyGroupsHom h = deviationHomG (sld h) h where
  sld :: (Distributive h, SlicedFree h) => p h -> Struct (Dst,SldFr) h
  sld _ = Struct

--------------------------------------------------------------------------------
-- cnzFreeHomAbl -

cnzFreeHomAbl :: (Attestable n)
  => ConsecutiveZeroHom To n (Matrix Z) -> ConsecutiveZeroFreeHom To n AbHom
cnzFreeHomAbl h = ConsecutiveZeroFreeHom a' b' fs' where
  a'  = cnzFreeAbl $ start h
  b'  = cnzFreeAbl $ end h
  fs' = amap1 (amap FreeAbHom) $ cnzHomArrows h


{-
--------------------------------------------------------------------------------
-- ccxCnzFreeAbl -

ccxCnzFreeAbl :: ChainComplex Z n -> ConsecutiveZeroFree To n AbHom
ccxCnzFreeAbl = cnzFreeAbl . ccxConsecutiveZero where
  
--------------------------------------------------------------------------------
-- cnzFreeAblHomology -

cnzFreeAblHomology :: ConsecutiveZeroFree To n AbHom -> Homology n
cnzFreeAblHomology = varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree

--------------------------------------------------------------------------------
-- HomologyHom -

-- | homomorphism between homologies.
type HomologyHom n = HomologyHomG n AbHom

--------------------------------------------------------------------------------
-- ccxCnzFreeHomAbl -

ccxCnzFreeHomAbl :: ChainComplexHom Z n -> ConsecutiveZeroFreeHom To n AbHom
ccxCnzFreeHomAbl h = ConsecutiveZeroFreeHom a' b' fs' where
  ConsecutiveZeroHom (DiagramTrafo a b fs) = ccxConsecutiveZeroHom h
  a'  = cnzFreeAbl $ (ConsecutiveZero a)
  b'  = cnzFreeAbl $ (ConsecutiveZero b)
  fs' = amap1 (amap FreeAbHom) fs

--------------------------------------------------------------------------------
-- cnzfhHomologyHom -

cnzFreeHomAblHomologyHom :: ConsecutiveZeroFreeHom To n AbHom -> HomologyHom n
cnzFreeHomAblHomologyHom (ConsecutiveZeroFreeHom a b fs) = VarianceHomG a' b' fs where
  a' = cnzFreeAblHomology a
  b' = cnzFreeAblHomology b


cnzFreeHomHomologyHom :: Homological h => ConsecutiveZeroFreeHom To n h -> HomologyHomG n h
cnzFreeHomHomologyHom (ConsecutiveZeroFreeHom a b fs) = VarianceHomG a' b' fs where
  a' = homologyG a
  b' = homologyG b
  
--------------------------------------------------------------------------------
-- homologyHom -

-- | the induced homomorphism between homologies.
homologyHom :: ChainComplexHom Z n -> HomologyHom n
homologyHom = cnzFreeHomAblHomologyHom . ccxCnzFreeHomAbl

--------------------------------------------------------------------------------
-- hmgGroupsHom -

-- | homomorphism between the homology groups.
homologyGroupsHom :: Attestable n => HomologyHom n -> DeviationHom (n+1) AbHom
homologyGroupsHom = deviationHomG (Struct :: Struct (Dst,SldFr) AbHom)

ff :: (Distributive h, SlicedFree h) => HomologyHomG n h -> Struct (Dst,SldFr) h
ff _ = Struct
{-
hhg :: (Attestable n, Distributive h) => HomologyHomG n h -> DeviationHom (n+1) h
hhg h = deviationHomG (ff h) h
-}
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

    
-}
