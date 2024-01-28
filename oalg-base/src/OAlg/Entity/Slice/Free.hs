
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
-- |
-- Module      : OAlg.Entity.Slice.Free
-- Description : slicing by free points.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- sliced structures with an assigned /free/ 'Point' of some given /dimension/ and
-- with /specialized/ limits.
module OAlg.Entity.Slice.Free
  (
    -- * Free
    Free(..), freeN, castFree, isFree
  , SomeFree(..), SomeFreeSlice(..)

    -- * Limes
  , LimesFree(..), limesFree
  , DiagramFree(..),dgfDiagram
  , KernelSliceFromSomeFreeTip(..), ksfKernel

    -- ** Kernel
  , KernelFree, KernelDiagramFree
  
    -- ** Cokernel
  , CokernelDiagramFree
  , CokernelLiftableFree(..), clfCokernel, clfLiftableFree

    -- ** Pullback
  , PullbackFree, PullbackDiagramFree  
  
  ) where

import Control.Monad (join)

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.KernelsAndCokernels

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding ((++))
import OAlg.Entity.Diagram
import OAlg.Entity.Slice.Definition


--------------------------------------------------------------------------------
-- Free -

-- | index for free points within a 'Multiplicative' structure @__c__@.
--
-- >>> lengthN (Free attest :: Free N3 c)
-- 3
newtype Free k c = Free (Any k) deriving (Show,Eq,Validable,Entity)

instance Attestable k => Singleton1 (Free k) where
  unit1 = Free attest

instance Show1 (Free k)
instance Eq1 (Free k)
instance Validable1 (Free k)
instance Typeable k => Entity1 (Free k)

--------------------------------------------------------------------------------
-- freeN -

-- | the underlying natural number.
freeN :: Free k c -> N
freeN (Free k) = lengthN k

--------------------------------------------------------------------------------
-- castFree -

-- | casting between 'Free' types.
castFree :: Free k x -> Free k y
castFree (Free k) = Free k

--------------------------------------------------------------------------------
-- isFree -

-- | check for being a free point, i.e. if it is equal to 'slicePoint'.
--
-- __Definition__ Let @n@ be in @'Free' __n__ __c__@ and @p@ in @'Point' __c__@ then
-- we call @p@ of __/order/__ @n@ if and only if @'slicePoint' i '==' p@.
isFree :: (Eq (Point c), Sliced (Free k) c) => Free k c -> Point c -> Bool
isFree i p = slicePoint i == p

--------------------------------------------------------------------------------
-- SomeFree -

-- | some free attest.
data SomeFree c where
  SomeFree :: (Attestable k, Sliced (Free k) c) => Free k c -> SomeFree c

deriving instance Show (SomeFree c)

instance Validable (SomeFree c) where
  valid (SomeFree k) = Label "SomeFree" :<=>: valid k
--------------------------------------------------------------------------------
-- SomeFreeSlice -

-- | some free point within a 'Multiplicative' structure @__c__@.
data SomeFreeSlice s c where
  SomeFreeSlice :: (Attestable k, Sliced (Free k) c)
    => Slice s (Free k) c -> SomeFreeSlice s c
    
deriving instance Show c => Show (SomeFreeSlice s c)

instance Oriented c => Validable (SomeFreeSlice s c) where
  valid (SomeFreeSlice s) = Label "SomeFreeSlice" :<=>: valid s

--------------------------------------------------------------------------------
-- XStandardSomeFreeSliceFrom -

class XStandardSomeFreeSliceFrom c where
  xStandardSomeFreeSliceFrom :: X (SomeFreeSlice From c)
  
--------------------------------------------------------------------------------
-- LimesFree -

-- | predicate for a limes with a /free/ tip of its universal cone.
--
-- __Property__ Let @'LimesFree' k l@ be in
-- @'LimesFree' __s__ __p__ __t__ __n__ __m__ __a__@ and
-- then holds: @'slicePoint' k '==' t@ where @t = 'tip' ('universalCone' l)@. 
data LimesFree s p t n m a where
  LimesFree :: (Attestable k, Sliced (Free k) a)
    => Free k a -> Limes s p t n m a -> LimesFree s p t n m a

deriving instance Oriented a => Show (LimesFree s p t n m a)

instance ( Distributive a, XStandardOrtPerspective p a
         , Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Validable (LimesFree Dst p t n m a) where
  valid (LimesFree k l) = Label "LimesFree" :<=>:
    And [ valid k
        , valid l
        , (slicePoint k == t):?>Params["(k,t)":=show (k,t)]  
        ] where t = tip $ universalCone l

--------------------------------------------------------------------------------
-- limesFree -

-- | the underlying free limes.
limesFree :: LimesFree s p t n m a -> Limes s p t n m a
limesFree (LimesFree _ l) = l

--------------------------------------------------------------------------------
-- KernelSliceFromSomeFreeTip -

-- | predicate for a kernel with a start point of its diagram given by the slice index and
-- a free universal tip.
--
-- __Property__ Let @'KernelSliceFromSomeFreeTip' k' i ker@ be in
-- @'KernelSliceFromSomeFreeTip' __n__ __c__@, then holds:
--
-- (1) @'slicePoint' i '==' s@ where @'DiagramParallelLR' s _ _ = 'diagram' ker@.
--
-- (2) @'slicePoint' k' '==' 'tip' ('universalCone' ker)@.
data KernelSliceFromSomeFreeTip n i c where
  KernelSliceFromSomeFreeTip :: (Attestable k', Sliced (Free k') c)
    => Free k' c -> i c -> Kernel n c -> KernelSliceFromSomeFreeTip n i c

instance (Oriented c, Sliced i c) => Show (KernelSliceFromSomeFreeTip n i c) where
  show (KernelSliceFromSomeFreeTip k i ker)
    = "KernelSliceFromSomeFreeTip[" ++ show1 k ++ "," ++ show1 i ++ "] ("
    ++ show ker ++ ")" 

instance (Distributive c, Sliced i c, XStandardOrtSiteTo c, Typeable n)
  => Validable (KernelSliceFromSomeFreeTip n i c) where
  valid (KernelSliceFromSomeFreeTip k' i ker) = Label "KernelSliceFromSomeFreeTip" :<=>:
    And [ valid1 k'
        , valid ker
        , Label "1" :<=>: let DiagramParallelLR s _ _ = diagram ker in
            (slicePoint i == s) :?> Params ["i":=show1 i,"s":= show s]
        , Label "2" :<=>: (slicePoint k' == tip (universalCone ker))
            :?> Params ["k'":=show1 k',"ker":=show ker]
        ]

--------------------------------------------------------------------------------
-- ksfKernel -

-- | the underlying kernel.
ksfKernel :: KernelSliceFromSomeFreeTip n i c -> Kernel n c
ksfKernel (KernelSliceFromSomeFreeTip _ _ ker) = ker

--------------------------------------------------------------------------------
-- DiagramFree -

-- | predicate for diagrams with free points.
data DiagramFree t n m a = DiagramFree (FinList n (SomeFree a)) (Diagram t n m a)
  deriving (Show)

instance Oriented a => Validable (DiagramFree t n m a) where
  valid (DiagramFree sfs d) = Label "DiagramFree"
    :<=>: valid (sfs,d) && vld 0 sfs (dgPoints d) where
    vld :: Oriented a => N -> FinList n (SomeFree a) -> FinList n (Point a) -> Statement
    vld _ Nil Nil = SValid
    vld i (SomeFree k:|sfs) (p:|ps)
      = And [ isFree k p :?> Params ["i":=show i,"k":=show k,"p":=show p]
            , vld (succ i) sfs ps
            ] 

--------------------------------------------------------------------------------
-- dgfDiagram -

-- | the underlying diagram.
dgfDiagram :: DiagramFree t n m a -> Diagram t n m a
dgfDiagram (DiagramFree _ d) = d

--------------------------------------------------------------------------------
-- KernelFree -

-- | kerne diagram with free points. 
type KernelDiagramFree = DiagramFree (Parallel LeftToRight) N2

-- | kernel of a diagram with free points.
type KernelFree = LimesFree Dst Projective (Parallel LeftToRight) N2

--------------------------------------------------------------------------------
-- CokernelFree -

-- | cokernel diagrams with free points.
type CokernelDiagramFree = DiagramFree (Parallel RightToLeft) N2

--------------------------------------------------------------------------------
-- PullbackFree -

-- | pullback diagram with free points.
type PullbackDiagramFree n c = DiagramFree (Star To) (n+1) n c

-- | pullback of a diagram with free points.
type PullbackFree n c = LimesFree Mlt Projective (Star To) (n+1) n c

--------------------------------------------------------------------------------
-- CokernelLiftableFree -

-- | predicate for a liftable cokernel.
--
-- __Property__ Let @'CokernelLiftableFree' c l@ be in @'CokernelLiftableFree' __c__@ for a
-- 'Distributive' structure @__c__@, then holds:
-- For any @k@ in @'Any' __k__@ holds:
-- @'cokernelFactor' ('universalCone' c) '==' 'liftBase' (l k)@.
data CokernelLiftableFree c
  = CokernelLiftableFree (Cokernel N1 c) (forall (k :: N') . Any k -> Liftable From (Free k) c)

instance Oriented c => Show (CokernelLiftableFree c) where
  show (CokernelLiftableFree c _) = join ["CokernelLiftableFree (", show c, ")"]


instance (Distributive c, XStandardOrtSiteFrom c, XStandardOrtOrientation c)
  => Validable (CokernelLiftableFree c) where
  valid (CokernelLiftableFree c l) = Label "CokernelLiftable" :<=>:
    And [ Label "c" :<=>: valid c
        , Forall xk (\(SomeNatural k) -> vldLftFree k cf (l k))  
        ]
    where xk = amap1 someNatural $ xNB 0 30
          cf = cokernelFactor $ universalCone c
          
          vldLftFree :: (Distributive c, XStandardOrtOrientation c)
            => Any k -> c -> Liftable From (Free k) c -> Statement
          vldLftFree k cf lk 
            = And [ Label "l k" :<=>: valid lk
                  , (cf == liftBase lk)
                    :?> Params [ "k":=show k
                               , "cokernelFactor (universalCone c)":=show cf
                               , "l k":=show lk
                               ]
                  ]

--------------------------------------------------------------------------------
-- clfCokernel -

-- | the underlying cokernel.
clfCokernel :: CokernelLiftableFree c -> Cokernel N1 c
clfCokernel (CokernelLiftableFree c _) = c

--------------------------------------------------------------------------------
-- clfLiftableFree -

-- | the induced liftable.
clfLiftableFree :: CokernelLiftableFree c -> Any k -> Liftable From (Free k) c
clfLiftableFree (CokernelLiftableFree _ l) = l

