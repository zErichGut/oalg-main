
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
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
-- deviation for free chains.
module OAlg.Limes.Exact.Free
  (
    -- * Variance
    varianceFreeTo, VarianceFreeLiftable
    
    -- * Free Consecutive Zero
  , ConsecutiveZeroFree(..)
  
    -- ** Duality
  , cnzFreeMapS, cnzFreeMapCov, cnzFreeMapCnt
  
    -- * Proposition
  , prpConsecutiveZeroFree
  ) where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Entity.Slice

import OAlg.Hom.Oriented
import OAlg.Hom.Distributive

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation


--------------------------------------------------------------------------------
-- ConsecutiveZeroFree -

-- | consecutive zero chain, where the tail of the points are free.
--
-- __Property__ Let @'ConsecutiveZeroFree' c fs@ be in @'ConsecutiveZeroFree' __t n x__@, then holds:
--
-- (1) @'sfrPoint' f '==' p@ for all @(f,p)@ in @fs '`zip`' 'tail' ('cnzPoints' c)@.
data ConsecutiveZeroFree t n x where
  ConsecutiveZeroFree
    :: ConsecutiveZero t n x
    -> FinList (n+2) (SomeFree x)
    -> ConsecutiveZeroFree t n x

deriving instance (Show x, ShowPoint x) => Show (ConsecutiveZeroFree t n x)
deriving instance (Eq x, EqPoint x) => Eq (ConsecutiveZeroFree t n x)

--------------------------------------------------------------------------------
-- prpConsecutiveZeroFree -

relConsecutiveZeroFree :: Distributive x => ConsecutiveZeroFree t n x -> Statement
relConsecutiveZeroFree (ConsecutiveZeroFree c fs)
  = And [ valid c
        , valid fs
        , Label "1" :<=>: vld 1 fs (tail $ cnzPoints c)
        ]
  where

    vld :: Distributive x => N -> FinList n (SomeFree x) -> FinList n (Point x) -> Statement
    vld _ Nil _ = SValid
    vld i (f:|fs) (p:|ps)
      = And [ (sfrPoint f == p) :?> Params ["i":=show i, "f":=show f, "p":=show p]
            , vld (succ i) fs ps
            ]

-- | validity according to 'ConsecutiveZeroFree'.
prpConsecutiveZeroFree :: Distributive x => ConsecutiveZeroFree t n x -> Statement
prpConsecutiveZeroFree cf = Prp "ConsecutiveZeroFree" :<=>: relConsecutiveZeroFree cf
 
instance Distributive x => Validable (ConsecutiveZeroFree t n x) where
  valid = prpConsecutiveZeroFree
  
--------------------------------------------------------------------------------
-- cnzFreeMapCov -

-- | covairaint mapping of 'ConsecutiveZeroFree'.
cnzFreeMapCov ::
  ( HomDistributiveDisjunctive h
  , HomOrientedSlicedFree h
  )
  => Variant2 Covariant h x y -> ConsecutiveZeroFree t n x -> ConsecutiveZeroFree t n y
cnzFreeMapCov h (ConsecutiveZeroFree c fs) = ConsecutiveZeroFree c' fs' where
  c'  = cnzMapCov h c
  fs' = amap1 (sfrMap h) fs
  
--------------------------------------------------------------------------------
-- cnzFreeMapCnt -

-- | contravaraint mapping of 'ConsecutiveZeroFree'.
cnzFreeMapCnt ::
  ( HomDistributiveDisjunctive h
  , HomOrientedSlicedFree h
  )
  => Variant2 Contravariant h x y -> ConsecutiveZeroFree t n x -> ConsecutiveZeroFree (Dual t) n y
cnzFreeMapCnt h (ConsecutiveZeroFree c fs) = ConsecutiveZeroFree c' fs' where
  c'  = cnzMapCnt h c
  fs' = amap1 (sfrMap h) fs

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (ConsecutiveZeroFree t n) = ConsecutiveZeroFree (Dual t) n

--------------------------------------------------------------------------------
-- cnzFreeMapS -

-- | mapping of 'ConsecutiveZeroFree'.
cnzFreeMapS ::
  ( HomDistributiveDisjunctive h
  , HomOrientedSlicedFree h
  , t ~ Dual (Dual t)
  )
  => h x y -> SDualBi (ConsecutiveZeroFree t n) x -> SDualBi (ConsecutiveZeroFree t n ) y
cnzFreeMapS = vmapBi cnzFreeMapCov cnzFreeMapCov cnzFreeMapCnt cnzFreeMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance
  ( HomDistributiveDisjunctive h
  , HomOrientedSlicedFree h
  , t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (ConsecutiveZeroFree t n)) h (->) where
  amapG = cnzFreeMapS

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , HomOrientedSlicedFree h
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConsecutiveZeroFree t n)) h (->)

--------------------------------------------------------------------------------
-- VarianceFreeLiftable -

-- | variance according to the conic objects @'ConicFreeTip' 'Cone'@, 'ConeLiftable' over the
-- diagrammatic object 'SomeFreeSliceDiagram'.
type VarianceFreeLiftable t = VarianceG t (ConicFreeTip Cone) ConeLiftable SomeFreeSliceDiagram

--------------------------------------------------------------------------------
-- varianceFreeTo -

-- | variance according to 'KernelsSomeFreeFreeTip' and 'CokernelsLiftableSomeFree'. 
varianceFreeTo :: Distributive x
  => KernelsSomeFreeFreeTip x
  -> CokernelsLiftableSomeFree x
  -> ConsecutiveZeroFree To n x -> VarianceFreeLiftable To n x
varianceFreeTo kers cokers (ConsecutiveZeroFree c fs) = VarianceG c (kcs kers cokers c fs) where

  kc :: Distributive x
    => KernelsG (ConicFreeTip Cone) SomeFreeSliceDiagram N1 x
    -> CokernelsG ConeLiftable SomeFreeSliceDiagram N1 x
    -> ConsecutiveZero To n x -> SomeFree x
    -> (KernelSomeFreeFreeTip x,CokernelLiftableSomeFree x)
  kc kers cokers (ConsecutiveZero (DiagramChainTo _ (v:|w:|_))) (SomeFree f) = (k,c) where
    k  = limes kers (SomeFreeSliceKernel (SliceFrom f v))
    w' = universalFactor k (ConeKernel (universalDiagram k) w)
    c  = case universalCone k of
      ConicFreeTip f' _ -> limes cokers (SomeFreeSliceCokernel (SliceTo f' w'))

  kcs :: Distributive x
    => KernelsG (ConicFreeTip Cone) SomeFreeSliceDiagram N1 x
    -> CokernelsG ConeLiftable SomeFreeSliceDiagram N1 x
    -> ConsecutiveZero To n x -> FinList (n+2) (SomeFree x)
    -> FinList (n+1) (KernelSomeFreeFreeTip x,CokernelLiftableSomeFree x)
  kcs kers cokers c (f:|fs) = kc kers cokers c f :| case fs of
    _ :| Nil    -> Nil
    _ :| _ :| _ -> kcs kers cokers (cnzTail c) fs 
