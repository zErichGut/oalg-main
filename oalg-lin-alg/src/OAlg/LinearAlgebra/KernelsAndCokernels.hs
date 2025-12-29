
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.LinearAlgebra.KernelsAndCokernels
-- Description : kernels and cokernels.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Kernels and cokernels for matrices over a field.
module OAlg.LinearAlgebra.KernelsAndCokernels
  ( mtxKernels
  ) where

import Control.Monad

import Data.List (zip)

import OAlg.Prelude

import OAlg.Data.Singleton
import OAlg.Data.Proxy

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Exponential

import OAlg.Entity.Sequence.Definition as S
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.Graph

import OAlg.Entity.Natural
import OAlg.Entity.FinList hiding (zip)
import OAlg.Entity.Diagram

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Entries

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.LinearAlgebra.StepMatrix

--------------------------------------------------------------------------------
-- mtxKernel -

-- | a kernel for the given matrix.
mtxKernel :: Field k => KernelDiagram N1 (Matrix k) -> Kernel N1 (Matrix k)
mtxKernel dg = LimesProjective cn uv where
  DiagramParallelLR _ _ (m@(Matrix _ cl _):|_) = dg
  
  sMtx  = fst $ stepMatrixPre m
  sGrph = stpGrph sMtx
  jMax  = lengthN cl
  krCls = jMax >- lengthN sGrph
  sis   = amap1 snd $ stgxs sGrph

  cn = ConeKernel dg kr
  kr = Matrix cl (dim unit ^ krCls) (rcets $ krMtx jMax sGrph sMtx)

  uv (ConeKernel _ (Matrix _ cf fijs)) = Matrix (start kr) cf f'ijs where
    f'ijs = crets $ elim sis $ etscr fijs

    -- eliminates the i-th row, given by sis
    elim :: i ~ N => [i] -> Col i (Row j x) -> Col i (Row j x)
    elim sis (Col (PSequence rws)) = Col (PSequence (erws 0 sis rws)) where
      erws d is@(i:is') rws@((rw,i'):rws') = case i `compare` i' of
        LT -> erws (d+1) is' rws
        EQ -> erws (d+1) is' rws'
        GT -> (rw,i'>-d):erws d is rws'
      erws d _ rws                         = amap1 (\(rw,i) -> (rw,i>-d)) rws
                                            
  -- the associated step graph
  -- pre: cls is in step form
  stpGrph :: i ~ N => Row j (Col i x) -> StepGraph i j
  stpGrph cls = StepGraph $ Graph $ stpg 0 (rowxs cls) where
    stpg _ []           = []
    stpg i ((cl,j):cls) | hi < It i = stpg i cls
                        | otherwise = (i,j):stpg (succ i) cls
      where
        hi = snd $ S.span (pi cl) cl 

    pi :: Col i x -> Proxy i
    pi _ = Proxy

  -- the kernel column
  -- pre: for all (_,i) in cl holds:
  --      - i < max i' where (i',_) in sg
  --      - si < j where (i',si) in sg and i' <= i 
  krCl :: (Ring x, i ~ N, j ~ N) => StepGraph i j -> Col i x -> j -> Col i x
  krCl (StepGraph (Graph sg)) (Col (PSequence xi)) j = Col $ PSequence $ krc sg xi where
    krc ((i,si):sg') xi@((x,i'):xi') | i < i'    = krc sg' xi
                                     | otherwise = (negate x,si) : krc sg' xi' -- i == i' 
    krc _ _                                      = [(rOne,j)]

  -- the kernel matrix in row col form.
  -- pre: sg is the step graph of cls
  krMtx :: (Ring x, i ~ N, j ~ N) => j -> StepGraph i j -> Row j (Col i x) -> Row j (Col i x)
  krMtx jMax sg cls = Row $ PSequence (kmx 0 (amap1 snd sis) (rowxs cls) `zip` [0..]) where
    StepGraph (Graph sis) = sg

    kmx j  _ _                | j >= jMax  = []
    kmx j  sis ((cl,j'):cls') | j == j'    = case sis of
      si:sis'                 | j == si   -> kmx (j+1) sis' cls'
      _                                   -> krCl sg cl j : kmx (j+1) sis cls'
    kmx j sis cls                          = krCl sg colEmpty j : kmx (j+1) sis cls

pp :: N -> Statement
pp nMax = Forall xQ (valid . universalCone . mtxKernel . kernelDiagram) where
  xQ :: X (Matrix Q)
  xQ = join $ amap1 (xoArrow xOM) xO where
    xOM@(XOrtOrientation xO _) = xMatrixTtl nMax 1 xStandard

mt :: (Ring r, i ~ N, j ~ N) => N -> N -> [([(r,j)],i)] -> Matrix r
mt r c xijs = matrixTtl r c xijs' where
  xijs' = join $ amap1 (\(xjs,i) -> amap1 (\(x,j) -> (x,i,j)) xjs) xijs


m :: Matrix Q
m = mt 4 6 ([ [2,4,6,0,2  ] `zip` [1..]
            , [1,2,3,3,0.5] `zip` [1..]
            , [3,6,7,1,2  ] `zip` [1..]
            , [1,2,5,3,4/3] `zip` [1..]
            ] `zip` [0..]
           )
    
kr = limes mtxKernels (kernelDiagram m)
cn = universalCone kr
--------------------------------------------------------------------------------
-- mtxKernels -

mtxKernels :: Field k => Kernels N1 (Matrix k)
mtxKernels = LimitsG mtxKernel

--------------------------------------------------------------------------------
-- prpMtxKernels -

xodQ :: XOrtOrientation Q
xodQ = xoTtl xStandard

xodMtxQ :: XOrtOrientation (Matrix Q)
xodMtxQ = xMatrixTtl 15 1 xStandard

instance XStandardOrtOrientation Q where xStandardOrtOrientation = xodQ

xecfMtxQ :: Kernel N1 (Matrix Q) -> X (KernelCone N1 (Matrix Q),Matrix Q)
xecfMtxQ kr = do
  f <- xf
  return (ConeKernel dg (k*f),f)
  
  where
    ConeKernel dg k = cone $ universalCone kr
  
    xf = do
      n <- xoPoint xodMtxQ
      xoArrow xodMtxQ (n :> start k)

instance XStandardEligibleConeFactorG
           Cone Dst Projective Diagram (Parallel LeftToRight) N2 N1 (Matrix Q) where
  xStandardEligibleConeFactorG = XEligibleConeFactorG xecfMtxQ


instance XStandardEligibleConeG
           Cone Dst Projective Diagram (Parallel LeftToRight) N2 N1 (Matrix Q) where
  xStandardEligibleConeG = xecfEligibleCone xStandardEligibleConeFactorG


-- | validity of 'mtxKernels' for matrices over 'Q'.
prpMtxKernels :: Statement
prpMtxKernels = Prp "MtxKernels" :<=>: valid (mtxKernels :: Kernels N1 (Matrix Q))
