
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
  ( mtxKernels, mtxCokernels
  , rngKernelsSomeFreeFreeTip
  , fldCokernelsLiftableSomeFree
  , prpMtxKernelsQ
  ) where

import Data.List (zip)

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Variant
import OAlg.Data.Either
import OAlg.Data.Singleton
import OAlg.Data.Proxy

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Exponential
import OAlg.Structure.Operational

import OAlg.Entity.Sequence.Definition as S
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.Graph

import OAlg.Entity.Natural
import OAlg.Entity.FinList hiding (zip)
import OAlg.Entity.Diagram

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Transformation
import OAlg.Entity.Slice
import OAlg.Entity.Slice.Liftable
import OAlg.Entity.FactorM

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

{-
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
-}
--------------------------------------------------------------------------------
-- mtxKernels -

-- | kernels for matrices over a @'Field' __k__@.
mtxKernels :: Field k => Kernels N1 (Matrix k)
mtxKernels = LimitsG mtxKernel

--------------------------------------------------------------------------------
-- mtxCokernels -

mtxCokernels :: Field k => Cokernels N1 (Matrix k)
mtxCokernels = ckrs where
  Contravariant2 i     = isoCoMatrixOp
  SDualBi (Left1 ckrs) = amapF (inv2 i) (SDualBi (Right1 mtxKernels))


--------------------------------------------------------------------------------
-- rngKernelsSomeFreeFreeTip -

rngKernelSomeFreeFreeTip :: Ring x
  => Kernels N1 (Matrix x)
  -> KernelDiagrammatic SomeFreeSliceDiagram N1 (Matrix x)
  -> KernelSomeFreeFreeTip (Matrix x)
rngKernelSomeFreeFreeTip krs d@(SomeFreeSliceKernel (SliceFrom _ _)) = LimesProjective cn uv where
  kr  = limes krs (diagram d)
  cn' = universalCone kr
  
  cn = case someNatural $ lengthN $ tip $ cn' of
    SomeNatural k -> ConicFreeTip (Free k) (ConeKernel d $ kernelFactor cn')

  uv (ConeKernel d f) = universalFactor kr (ConeKernel (diagram d) f)


rngKernelsSomeFreeFreeTip :: Ring x => Kernels N1 (Matrix x) -> KernelsSomeFreeFreeTip (Matrix x)
rngKernelsSomeFreeFreeTip = LimitsG . rngKernelSomeFreeFreeTip

--------------------------------------------------------------------------------
-- fldLiftableFreeEpi -

-- | the induced injective liftable.
fldLiftableFreeEpi :: Field x => FactorM Epimorph (Matrix x) -> LiftableFree Injective (Matrix x)
fldLiftableFreeEpi p = LiftableFree (lft p) where
  lft :: Field x => FactorM Epimorph (Matrix x) -> Any k -> Liftable Injective (Free k) (Matrix x)
  lft (Epi p) k = case ats k of
    Ats -> LiftableInjective p lfts where
      lfts (SliceFrom i f) | end p /= end f = throw NotLiftable
                           | otherwise      = SliceFrom i rf'c
        where rf   = r *> f
              rf'  = Matrix (end rf) (start f) $ mtxxs rf
              rf'c = rf' <* c
    where DiagonalForm _ r c = mtxDiagonalForm p
          -- as x is a field, the diagonal contains only ones and has the same length as (end f)  

--------------------------------------------------------------------------------
-- fldCokernelsLiftableSomeFree -

fldCokernelLiftableSomeFree :: Field x
  => CokernelDiagrammatic SomeFreeSliceDiagram N1 (Matrix x)
  -> CokernelG ConeLiftable SomeFreeSliceDiagram N1 (Matrix x)
fldCokernelLiftableSomeFree d@(SomeFreeSliceCokernel (SliceTo _ _)) = LimesInjective cn uv where
  ck = limes mtxCokernels (diagram d)
  
  cn = ConeCokernelLiftable cn' lf' where
    cn' = ConeCokernel d $ cokernelFactor $ universalCone ck
    lf' = fldLiftableFreeEpi $ cokernelFactorEpi ck

  uv (ConeCokernel d f) = universalFactor ck (ConeCokernel (diagram d) f)


fldCokernelsLiftableSomeFree :: Field x => CokernelsG ConeLiftable SomeFreeSliceDiagram N1 (Matrix x)
fldCokernelsLiftableSomeFree = LimitsG fldCokernelLiftableSomeFree

--------------------------------------------------------------------------------
-- prpMtxKernels -

-- xecfMtxQ :: Kernel N1 (Matrix Q) -> X (KernelCone N1 (Matrix Q),Matrix Q)
xecfMtxQ :: XEligibleConeFactorG
              Cone Dst Projective Diagram (Parallel LeftToRight) N2 N1 (Matrix Q)
xecfMtxQ = xecfOrtSite $ xoTo xStandardOrtOrientation
{-
xecfMtxQ kr = do
  f <- xf
  return (ConeKernel dg (k*f),f)
  
  where
    xodMtxQ = xStandardOrtOrientation
    
    ConeKernel dg k = cone $ universalCone kr
  
    xf = do
      n <- xoPoint xodMtxQ
      xoArrow xodMtxQ (n :> start k)

-}

-- | validity of 'mtxKernels' for matrices over 'Q'.
prpMtxKernelsQ :: Statement
prpMtxKernelsQ = Prp "MtxKernelsQ" :<=>: valid (mtxKernels :: Kernels N1 (Matrix Q))


