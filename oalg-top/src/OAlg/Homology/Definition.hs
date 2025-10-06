
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
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Slice.Free
import OAlg.Entity.Sequence.Set

import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.Free

import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator
import OAlg.Homology.ChainComplex


import OAlg.Category.NaturalTransformable
import OAlg.Category.SDuality
import OAlg.Structure.Oriented
import OAlg.Structure.Distributive
import OAlg.Hom.Definition
import OAlg.Limes.Cone

{-
instance ApplicativeG
           (SDualBi (DiagramG SomeFreeSliceDiagram (Parallel t) N2 N1))
           (IsoO Dst Op)
           (->)

instance FunctorialG
           (SDualBi (DiagramG SomeFreeSliceDiagram (Parallel t) N2 N1))
           (IsoO Dst Op)
           (->)

instance NaturalTransformable (IsoO Dst Op) (->)
           (SDualBi (DiagramG SomeFreeSliceDiagram (Parallel LeftToRight) N2 N1))
           (SDualBi (DiagramG Diagram (Parallel LeftToRight) N2 N1))
instance NaturalTransformable (IsoO Dst Op) (->)
           (SDualBi (DiagramG SomeFreeSliceDiagram (Parallel RightToLeft) N2 N1))
           (SDualBi (DiagramG Diagram (Parallel RightToLeft) N2 N1))

instance NaturalDiagrammatic (IsoO Dst Op) SomeFreeSliceDiagram (Parallel LeftToRight) N2 N1
instance NaturalDiagrammatic (IsoO Dst Op) SomeFreeSliceDiagram (Parallel RightToLeft) N2 N1

instance ApplicativeG 
           (SDualBi (ConeG (ConicFreeTip Cone) Dst Projective
                     SomeFreeSliceDiagram (Parallel LeftToRight) N2 N1)
           )
           (IsoO Dst Op) (->)

instance FunctorialG 
           (SDualBi (ConeG (ConicFreeTip Cone) Dst Projective
                     SomeFreeSliceDiagram (Parallel LeftToRight) N2 N1)
           )
           (IsoO Dst Op) (->)
           
instance NaturalTransformable (IsoO Dst Op) (->)
           (SDualBi (ConeG (ConicFreeTip Cone) Dst Projective
                     SomeFreeSliceDiagram (Parallel LeftToRight) N2 N1)
           )
           (SDualBi (ConeG Cone Dst Projective
                     SomeFreeSliceDiagram (Parallel LeftToRight) N2 N1)
           )  

instance NaturalConic
  (IsoO Dst Op) (ConicFreeTip Cone) Dst Projective SomeFreeSliceDiagram (Parallel LeftToRight) N2 N1
-}
--------------------------------------------------------------------------------
-- abgSomeFree -

abgSomeFree :: AbGroup -> Maybe (SomeFree AbHom)
abgSomeFree g | g == abg 0 ^ k = Just $ case someNatural k of SomeNatural k' -> SomeFree $ Free k' 
              | otherwise       = Nothing
  where k = lengthN g

--------------------------------------------------------------------------------
-- ChainComplexFree

type ChainComplexFree = ConsecutiveZeroFree To

--------------------------------------------------------------------------------
-- ccpConsecutiveZeroFree -

ccpConsecutiveZeroFree :: Typeable s => ChainComplex n (ChainOperator Z s) -> ChainComplexFree n AbHom
ccpConsecutiveZeroFree cos = ConsecutiveZeroFree cf fs where
  cf = cnzMapCov (homDisjOpDst FreeAbHom) $ ccpRepMatrix cos
  fs = amap1 (fromJust . abgSomeFree) $ tail $ dgPoints $ cnzDiagram cf 

--------------------------------------------------------------------------------
-- ccpfVaraince -

ccpfVariance :: ChainComplexFree n AbHom -> VarianceFreeLiftable To n AbHom
ccpfVariance = varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree

--------------------------------------------------------------------------------

c   = complex [Set [0..3]] :: Complex N
cos = bndZAsc Extended (attest :: Any N7) c
cf  = ccpConsecutiveZeroFree cos
v   = ccpfVariance cf
