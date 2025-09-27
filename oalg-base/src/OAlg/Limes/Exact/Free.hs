
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.Free
-- Description : deviation for free chains.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- deviation for free chains-
module OAlg.Limes.Exact.Free
  (
  ) where

import OAlg.Prelude

import Data.Typeable


import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList


import OAlg.Entity.Slice

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsecutiveZero

import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
{-
--------------------------------------------------------------------------------
-- ConsecutiveZeroFree -

-- | consecutive zero chain, where the tail of the points are free.
--
-- __Property__ Let @'ConsecutiveZeroFree' c fs@ be in @'ConsecutiveZeroFree' __t n x__@, then holds:
--
-- (1) @'sfrPoint' f '==' p@ for all @(f,p)@ in @'zip fs ('tail' '$' 'cnzPoints')@.
data ConsecutiveZeroFree t n x where
  ConsecutiveZeroFree
    :: ConsecutiveZero t n x
    -> FinList (n+2) (SomeFree x)
    -> ConsecutiveZeroFree t n x

--------------------------------------------------------------------------------
-- SomeFreeSliceDiagram -

-- | some free slice for kernel and cokernel diagrams.
data SomeFreeSliceDiagram t n m x where
  SomeFreeSliceKernel
    :: (Attestable k, Sliced (Free k) x)
    => Slice From (Free k) x
    -> SomeFreeSliceDiagram (Parallel LeftToRight) N2 N1 x
  SomeFreeSliceCokernel
    :: (Attestable k, Sliced (Free k) x)
    => Slice To (Free k) x
    -> SomeFreeSliceDiagram (Parallel RightToLeft) N2 N1 x

instance Diagrammatic SomeFreeSliceDiagram where
  diagram (SomeFreeSliceKernel (SliceFrom _ x)) = DiagramParallelLR (start x) (end x) (x:|Nil)
  diagram (SomeFreeSliceCokernel (SliceTo _ x)) = DiagramParallelRL (end x) (start x) (x:|Nil)

--------------------------------------------------------------------------------
-- VarianceFree -

-- | variance where the tail of the points for the top and bottom chain are free.
--
-- __Property__ Let @'VarianceFree' v t b@ be in @'VarianceFree' __t k c d n x__@, then holds:
--
-- (1) @'ConsecutiveZeroFree' ('vrcTop' v) t@ is 'valid'.
--
-- (2) @'ConsecutiveZeroFree' ('vrcBottom' v) b@ is 'valid'.
data VarianceFree t k c d n x where
  VarianceFree
    :: Variance t k c d n x
    -> FinList (n+2) (SomeFree x)  -- top 
    -> FinList (n+2) (SomeFree x)  -- bottom
    -> VarianceFree t k c d n x
    
--------------------------------------------------------------------------------
-- varianceFree -

varianceFree :: (Distributive x)
   => KernelsG (ConicFreeTip Cone) SomeFreeSliceDiagram N1 x
   -> CokernelsG ConeLiftable SomeFreeSliceDiagram N1 x
   -> ConsecutiveZeroFree To n x
   -> VarianceFree To (ConicFreeTip Cone) ConeLiftable SomeFreeSliceDiagram n x
varianceFree kers cokers cfTo = VarianceFree (Variance trf ker coker) fsTop fsBot where
  trf = error "nyi"

  fsBot = error "nyi"

  ConsecutiveZeroFree (ConsecutiveZero (DiagramChainTo a (v:|w:|_))) fsTop@(fb:|_) = cfTo
  
  ker = case fb of SomeFree k -> limes kers (SomeFreeSliceKernel (SliceFrom k v))
  
  w'  = universalFactor ker (ConeKernel (universalDiagram ker) w)
  -- as top is consecutive zero, w' is well defined

  fb' = case universalCone ker of ConicFreeTip ft _ -> SomeFree ft
  
  coker = case fb' of SomeFree k' -> limes cokers (SomeFreeSliceCokernel (SliceTo k' w'))
-}
