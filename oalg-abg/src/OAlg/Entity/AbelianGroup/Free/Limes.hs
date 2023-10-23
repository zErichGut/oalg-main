
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      : OAlg.Entity.AbelianGroup.Free.Limes
-- Description : limits for matrices over integers.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- limits for 'Z'-matrices.
module OAlg.Entity.AbelianGroup.Free.Limes
  ( -- * Projective
    zmxKernels
  , zmxPullbacks
  ) where

import Data.List (filter)

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential

import OAlg.Entity.Natural
import OAlg.Entity.Diagram
import OAlg.Entity.FinList
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.PullbacksAndPushouts

import OAlg.Entity.AbelianGroup.Free.SmithNormalForm

--------------------------------------------------------------------------------
-- zmxKernel -

zmxKernel :: KernelDiagram N1 (Matrix Z) -> Kernel N1 (Matrix Z)
zmxKernel kDgm@(DiagramParallelLR _ _ (h:|Nil)) = LimesProjective lim univ where
  
  DiagonalForm d _ (ColTrafo t) = zmxDiagonalForm h
  -- d = (rt*>h)<*ct

  Inv b bInv = amap GLTGL t
  
  m = lengthN (start h)
  s = lengthN d
  r = m >- s

  k = mtxJoin $ matrixBlc [ds,dr] [dr] [(one dr,1,0)] where
    ds = dim () ^ s
    dr = dim () ^ r

  kPrj (Matrix _ c xs) = Matrix (start k) c xs' where
    xs' = Entries $ PSequence
        $ amap1 (\(x,i,j) -> (x,(i>-s,j)))
        $ filter (\(_,i,_) -> s <= i)
        $ etsxs xs

  lim = ConeKernel kDgm (b*k)
  
  univ (ConeKernel _ x) = kPrj (bInv * x)

--------------------------------------------------------------------------------
-- zmxKernels1 -

-- | 'N1'-kernels for 'Z'-matrices.
zmxKernels1 :: Kernels N1 (Matrix Z)
zmxKernels1 = Limits zmxKernel

--------------------------------------------------------------------------------
-- zmxKernels -

-- | kernels for 'Z'-matrices.
zmxKernels :: Kernels n (Matrix Z)
zmxKernels = kernels zmxKernels1

--------------------------------------------------------------------------------
-- zmxPullbacks2 -

-- | 'N2'-pullbacks for 'Z'-matrices.
zmxPullbacks2 :: Pullbacks N2 (Matrix Z)
zmxPullbacks2 = plbPrdEql2 mtxProducts (krnEqls zmxKernels1)

--------------------------------------------------------------------------------
-- zmxPullbacks -

-- | pullbacks for 'Z'-matrices.
zmxPullbacks :: Pullbacks n (Matrix Z)
zmxPullbacks = pullbacks zmxPullbacks2
