
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
    Homology()
    
    -- * Chain Complex Free
  , ChainComplexFree()
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential

import OAlg.Entity.Diagram hiding (Chain)
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

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator
import OAlg.Homology.ChainComplex


import OAlg.Category.NaturalTransformable
import OAlg.Category.SDuality
import OAlg.Structure.Oriented
import OAlg.Structure.Distributive
import OAlg.Hom.Definition
import OAlg.Limes.Cone

--------------------------------------------------------------------------------
-- abgSomeFree -

abgSomeFree :: AbGroup -> Maybe (SomeFree AbHom)
abgSomeFree g | g == abg 0 ^ k = Just $ case someNatural k of SomeNatural k' -> SomeFree $ Free k' 
              | otherwise       = Nothing
  where k = lengthN g

--------------------------------------------------------------------------------
-- ChainComplexFree

data ChainComplexFree s n x where
  ChainComplexFree :: Typeable x
    => ChainComplex n (ChainOperator Z s)
    -> ConsecutiveZeroFree To n AbHom
    -> ChainComplexFree s n x

--------------------------------------------------------------------------------
-- chainComplexFree -

chainComplexFree :: Simplical s x
  => Regular -> Any n -> Complex x -> ChainComplexFree s n x
chainComplexFree r n c = ChainComplexFree cos (ccpOpsZSet cos) where
  cos = chainComplexOperators Struct r n c
  
  ccpOpsZSet ::Typeable s
    => ChainComplex n (ChainOperator Z s) -> ConsecutiveZeroFree To n AbHom
  ccpOpsZSet cos = ConsecutiveZeroFree cf fs where
    cf = cnzMapCov (homDisjOpDst FreeAbHom) $ ccpRepMatrix cos
    fs = amap1 (fromJust . abgSomeFree) $ tail $ dgPoints $ cnzDiagram cf 

chainComplexFree' :: Simplical s x
  => q s -> Regular -> Any n -> Complex x -> ChainComplexFree s n x
chainComplexFree' _ = chainComplexFree


--------------------------------------------------------------------------------
-- Homology -

data Homology s n x where
  Homology :: Typeable x
    => ChainComplex n (ChainOperator Z s)
    -> VarianceFreeLiftable To n AbHom
    -> Homology s n x

--------------------------------------------------------------------------------
-- homology -

homology :: ChainComplexFree s n x -> Homology s n x
homology (ChainComplexFree cos cf)
  = Homology cos (varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree cf)

--------------------------------------------------------------------------------
-- hmgTail -

hmgTail :: Typeable s => Homology s (n+1) x -> Homology s n x
hmgTail (Homology cos vf) = Homology (cnzTail cos) (vrcTail vf)

--------------------------------------------------------------------------------
-- hmgGroups -

hmgGroups :: Attestable n => Homology s n x -> Deviation (n+1) AbHom
hmgGroups (Homology _ vfs) = deviationsTo vfs

--------------------------------------------------------------------------------
-- hmgGroup -

hmgGroup :: Attestable n => Homology s n x -> AbGroup
hmgGroup = head . dgPoints . hmgGroups

--------------------------------------------------------------------------------
-- hmgSimplices -

hmgSimplices :: Typeable s => Homology s n x -> Set (s x)
hmgSimplices h@(Homology cos _) = case cos of
  ConsecutiveZero cs         -> case cs of
    DiagramChainTo _ (d:|_)  -> case start d of
      SimplexSet ssx         -> case eqType h ssx of
        Just Refl            -> ssx
        Nothing              -> throw $ ImplementationError "hmgSimplices"
  where
    eqType :: (Typeable x, Typeable y) => q x -> Set (s y) -> Maybe (x :~: y)
    eqType _ _ = eqT

-----------------------------------------------------------------------------------------
-- Chain -

type Chain x = ChainG Z Set x

--------------------------------------------------------------------------------
-- hmgChains -

-- hmgChains :: Homology n AbHom -> [Chain AbHom]

--------------------------------------------------------------------------------

c   = complex [Set [0..5]] :: Complex N
h   = homology $ chainComplexFree' (Proxy :: Proxy [])  Regular (attest :: Any N5) c


