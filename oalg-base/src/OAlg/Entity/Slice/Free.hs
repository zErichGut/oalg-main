
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

    -- ** Liftable Cokernel
  , CokernelDiagramFree
  , CokernelLiftableFree(..)
  , clfCokernel, clfLiftableFree

    -- *** Liftable Cokernels
  , clfLimes, ClfCokernels(..)

    -- ** Pullback
  , PullbackFree, PullbackDiagramFree

    -- * New
    -- * Cone Liftable
  , ConeLiftable(..), cnLiftable, cnlMapS

    -- ** Liftable Free
  , LiftableFree(..), liftFree
  , SlicedFree(..), SldFr
  , HomFree, lftFrMapSMlt, lftFrMapSDst
  , toDualOpFreeDst

  ) where

import Control.Monad (join)

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Singleton
import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Definition
import OAlg.Hom.Distributive

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.KernelsAndCokernels

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding ((++))
import OAlg.Entity.Diagram
import OAlg.Entity.Slice.Definition
import OAlg.Entity.Slice.Sliced
import OAlg.Entity.Slice.Liftable

--------------------------------------------------------------------------------
-- Free -

-- | index for free points within a 'Multiplicative' structure @__c__@.
--
-- >>> lengthN (Free attest :: Free N3 c)
-- 3
newtype Free k c = Free (Any k) deriving (Show,Eq,Validable)

instance Attestable k => Singleton1 (Free k) where
  unit1 = Free attest

instance Show1 (Free k)
instance Eq1 (Free k)
instance Validable1 (Free k)
-- instance Typeable k => Entity1 (Free k)

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
isFree :: Sliced (Free k) c => Free k c -> Point c -> Bool
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

instance Validable (SomeFreeSlice s c) where
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

instance ( Distributive a
         , XStandardEligibleCone Dst p t n m a
         , XStandardEligibleConeFactor Dst p t n m a
         , Typeable t, Typeable n, Typeable m
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

instance
  ( Distributive c, Sliced i c
  , XStandardEligibleConeKernel n c
  , XStandardEligibleConeFactorKernel n c
  , Typeable n
  )
  => Validable (KernelSliceFromSomeFreeTip n i c) where
  valid (KernelSliceFromSomeFreeTip k' i ker) = Label "KernelSliceFromSomeFreeTip" :<=>:
    And [ valid1 k'
        , valid ker
        , Label "1" :<=>: let DiagramParallelLR s _ _
                                = diagrammaticObject $ cone $ universalCone ker
                           in
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

instance Diagrammatic DiagramFree where diagram = dgfDiagram


--------------------------------------------------------------------------------
-- KernelFree -

-- | kernel diagram with free points. 
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
  = CokernelLiftableFree (Cokernel N1 c) (forall (k :: N') . Any k -> Liftable Injective (Free k) c)

instance Oriented c => Show (CokernelLiftableFree c) where
  show (CokernelLiftableFree c _) = join ["CokernelLiftableFree (", show c, ")"]

instance
  ( Distributive c
  , XStandardEligibleConeCokernel1 c
  , XStandardEligibleConeFactorCokernel1 c
  , XStandardOrtOrientation c
  )
  => Validable (CokernelLiftableFree c) where
  valid (CokernelLiftableFree c l) = Label "CokernelLiftable" :<=>:
    And [ Label "c" :<=>: valid c
        , Forall xk (\(SomeNatural k) -> vldLftFree k cf (l k))  
        ]
    where xk = amap1 someNatural $ xNB 0 30
          cf = cokernelFactor $ universalCone c
          
          vldLftFree :: (Distributive c, XStandardOrtOrientation c)
            => Any k -> c -> Liftable Injective (Free k) c -> Statement
          vldLftFree k cf lk 
            = And [ Label "l k" :<=>: valid lk
                  , (cf == lftbBase lk)
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
clfLiftableFree :: CokernelLiftableFree c -> Any k -> Liftable Injective (Free k) c
clfLiftableFree (CokernelLiftableFree _ l) = l

--------------------------------------------------------------------------------
-- ClfCokernels -

-- | predicate for liftable free cokernels where for each cokernel diagram @d@ in
--   @'CokernelDiagram' __n__ __d__@ ther is an associated @'CokernelLifatbleFree' __d__@ such
--   that its underlying diagram is equal to @d@.
newtype ClfCokernels n d = ClfCokernels (CokernelDiagram n d -> CokernelLiftableFree d)

-- | the limes of the given diagram.
clfLimes :: ClfCokernels n d -> CokernelDiagram n d -> CokernelLiftableFree d
clfLimes (ClfCokernels l) = l


--------------------------------------------------------------------------------
-- LiftableFree -

-- | liftable according to a free slice.
data LiftableFree p x where
  LiftableFree :: (forall k . Any k -> Liftable p (Free k) x) -> LiftableFree p x

--------------------------------------------------------------------------------
-- liftFree -

-- | lifting a free slice.
liftFree :: LiftableFree p x -> Any k -> Liftable p (Free k) x
liftFree (LiftableFree l) = l

--------------------------------------------------------------------------------
-- SliceFree -

-- | attest for @__k__@-free sliced structures.
class SlicedFree x where
  slicedFree :: Struct (Sld (Free k)) x

--------------------------------------------------------------------------------
-- tauSldFrTuple -

tauSldFrTuple :: SlicedFree x => Struct s x -> Struct (s,Sld (Free k)) x
tauSldFrTuple s = tauTuple s slicedFree

--------------------------------------------------------------------------------
-- tauSldFreeOp -

tauSldFreeOp :: Struct (Sld (Free k)) x -> Struct (Sld (Free k)) (Op x)
tauSldFreeOp Struct = Struct 

instance SlicedFree x => SlicedFree (Op x) where slicedFree = tauSldFreeOp slicedFree

--------------------------------------------------------------------------------
-- SdlFr -

-- | 'SlicedFree' structures. 
data SldFr

type instance Structure SldFr x = SlicedFree x

instance Transformable s Ort    => Transformable (s,SldFr) Ort    where tau = tau . tauFst
instance Transformable s Mlt    => Transformable (s,SldFr) Mlt    where tau = tau . tauFst
instance Transformable s Fbr    => Transformable (s,SldFr) Fbr    where tau = tau . tauFst
instance Transformable s Add    => Transformable (s,SldFr) Add    where tau = tau . tauFst
instance Transformable s FbrOrt => Transformable (s,SldFr) FbrOrt where tau = tau . tauFst
instance Transformable s Dst    => Transformable (s,SldFr) Dst    where tau = tau . tauFst

instance TransformableOrt s    => TransformableOrt (s,SldFr)
instance TransformableMlt s    => TransformableMlt (s,SldFr)
instance TransformableFbr s    => TransformableFbr (s,SldFr)
instance TransformableAdd s    => TransformableAdd (s,SldFr)
instance TransformableFbrOrt s => TransformableFbrOrt (s,SldFr)
instance TransformableDst s    => TransformableDst (s,SldFr) 

instance TransformableObjectClass (Mlt,SldFr) (HomDisj Mlt Op (HomEmpty Mlt))
instance TransformableObjectClass (Dst,SldFr) (HomDisj Dst Op (HomEmpty Dst))

--------------------------------------------------------------------------------
-- lftFrSub -

lftFrSub :: q k
   -> Struct (s,Sld (Free k)) x -> Struct (s,Sld (Free k)) y
   -> Variant2 v (IsoO s Op) x y
   -> Variant2 v (Inv2 (Sub (s,Sld (Free k)) (HomDisjEmpty s Op))) x y
lftFrSub _ sx sy = amapVariant2 (\(Inv2 t f) -> Inv2 (sub' (sx:>:sy) t) (sub' (sy:>:sx) f))

--------------------------------------------------------------------------------
-- lftFrMapIsoOpCov -

lftFrMapIsoOpCovStruct ::
  ( TransformableType s
  , TransformableOp s
  , TransformableMlt s
  , Transformable (s,Sld (Free k)) s
  , SlicedFree x
  , SlicedFree y
  )
  => Struct s x -> Struct s y
  -> Variant2 Covariant (IsoO s Op) x y -> LiftableFree p x -> Any k -> Liftable p (Free k) y
lftFrMapIsoOpCovStruct sx sy i lf k = lftMapCov (lftFrSub k sfx sfy i) (liftFree lf k) where
  sfx = tauSldFrTuple sx
  sfy = tauSldFrTuple sy

lftFrMapIsoOpMltCov ::
  ( s ~ Mlt
  , SlicedFree x
  , SlicedFree y
  )
  => Variant2 Covariant (IsoO s Op) x y -> LiftableFree p x -> LiftableFree p y
lftFrMapIsoOpMltCov i lf = LiftableFree (lftFrMapIsoOpCovStruct (domain i) (range i) i lf)

lftFrMapIsoOpDstCov ::
  ( s ~ Dst
  , SlicedFree x
  , SlicedFree y
  )
  => Variant2 Covariant (IsoO s Op) x y -> LiftableFree p x -> LiftableFree p y
lftFrMapIsoOpDstCov i lf = LiftableFree (lftFrMapIsoOpCovStruct (domain i) (range i) i lf)

--------------------------------------------------------------------------------
-- lftFrMapIsoOpCnt -

lftFrMapIsoOpCntStruct ::
  ( TransformableType s
  , TransformableOp s
  , TransformableMlt s
  , Transformable (s,Sld (Free k)) s
  , SlicedFree x
  , SlicedFree y
  )
  => Struct s x -> Struct s y
  -> Variant2 Contravariant (IsoO s Op) x y -> LiftableFree p x
  -> Any k -> Liftable (Dual p) (Free k) y
lftFrMapIsoOpCntStruct sx sy i lf k = lftMapCnt (lftFrSub k sfx sfy i) (liftFree lf k) where
  sfx = tauSldFrTuple sx
  sfy = tauSldFrTuple sy

lftFrMapIsoOpMltCnt ::
  ( s ~ Mlt
  , SlicedFree x
  , SlicedFree y
  )
  => Variant2 Contravariant (IsoO s Op) x y -> LiftableFree p x -> LiftableFree (Dual p) y
lftFrMapIsoOpMltCnt i lf = LiftableFree (lftFrMapIsoOpCntStruct (domain i) (range i) i lf)

lftFrMapIsoOpDstCnt ::
  ( s ~ Dst
  , SlicedFree x
  , SlicedFree y
  )
  => Variant2 Contravariant (IsoO s Op) x y -> LiftableFree p x -> LiftableFree (Dual p) y
lftFrMapIsoOpDstCnt i lf = LiftableFree (lftFrMapIsoOpCntStruct (domain i) (range i) i lf)

--------------------------------------------------------------------------------
-- HomFree -

type HomFree s = Sub (s,SldFr) (HomDisjEmpty s Op)

--------------------------------------------------------------------------------
-- lftFrMapCov -

lftFrMapMltCov :: Variant2 Covariant (Inv2 (HomFree Mlt)) x y -> LiftableFree p x -> LiftableFree p y
lftFrMapMltCov (Covariant2 i) = case (tauSnd (domain i),tauSnd (range i)) of
  (Struct,Struct) -> lftFrMapIsoOpMltCov (Covariant2 (inv2Forget i))

lftFrMapDstCov :: Variant2 Covariant (Inv2 (HomFree Dst)) x y -> LiftableFree p x -> LiftableFree p y
lftFrMapDstCov (Covariant2 i) = case (tauSnd (domain i),tauSnd (range i)) of
  (Struct,Struct) -> lftFrMapIsoOpDstCov (Covariant2 (inv2Forget i))

lftFrMapMltCnt :: Variant2 Contravariant (Inv2 (HomFree Mlt)) x y
  -> LiftableFree p x -> LiftableFree (Dual p) y
lftFrMapMltCnt (Contravariant2 i) = case (tauSnd (domain i),tauSnd (range i)) of
  (Struct,Struct) -> lftFrMapIsoOpMltCnt (Contravariant2 (inv2Forget i))

lftFrMapDstCnt :: Variant2 Contravariant (Inv2 (HomFree Dst)) x y
  -> LiftableFree p x -> LiftableFree (Dual p) y
lftFrMapDstCnt (Contravariant2 i) = case (tauSnd (domain i),tauSnd (range i)) of
  (Struct,Struct) -> lftFrMapIsoOpDstCnt (Contravariant2 (inv2Forget i))

--------------------------------------------------------------------------------
-- Duality - LiftableFree -

type instance Dual1 (LiftableFree p) = LiftableFree (Dual p)

--------------------------------------------------------------------------------
-- lftFrMapS -

lftFrMapSMlt :: p ~ Dual (Dual p)
  => Inv2 (HomFree Mlt) x y -> SDualBi (LiftableFree p) x -> SDualBi (LiftableFree p) y
lftFrMapSMlt = vmapBi lftFrMapMltCov lftFrMapMltCov lftFrMapMltCnt lftFrMapMltCnt

lftFrMapSDst :: p ~ Dual (Dual p)
  => Inv2 (HomFree Dst) x y -> SDualBi (LiftableFree p) x -> SDualBi (LiftableFree p) y
lftFrMapSDst = vmapBi lftFrMapDstCov lftFrMapDstCov lftFrMapDstCnt lftFrMapDstCnt

instance p ~ Dual (Dual p) => ApplicativeG (SDualBi (LiftableFree p)) (Inv2 (HomFree Mlt)) (->) where
  amapG = lftFrMapSMlt

instance p ~ Dual (Dual p) => FunctorialG (SDualBi (LiftableFree p)) (Inv2 (HomFree Mlt)) (->)

instance p ~ Dual (Dual p) => ApplicativeG (SDualBi (LiftableFree p)) (Inv2 (HomFree Dst)) (->) where
  amapG = lftFrMapSDst

instance p ~ Dual (Dual p) => FunctorialG (SDualBi (LiftableFree p)) (Inv2 (HomFree Dst)) (->)

--------------------------------------------------------------------------------
-- ConeLiftable -

-- | predicate for a liftable conic object.
--
-- __Property__ Let @cl@ be in @'ConeLiftable' __s p d t n m x__@, then holds:
--
-- (1) If @cl@ matches @'ConeKernelLiftableFree' c ('LiftableFree' l)@, then
-- for any @k@ in @'Any' __k__@ holds:
-- @'lftbBase' (l k)' '==' 'kernelFactor' c@.
--
-- (2) If @cl@ matches @'ConeCokernelLiftableFree' c ('LiftableFree' l)@, then
-- for any @k@ in @'Any' __k__@ holds:
-- @'lftbBase' (l k)' '==' 'cokernelFactor' c@.
data ConeLiftable s p d t n m x where
  ConeKernelLiftable
    :: KernelConic Cone d N1 x
    -> LiftableFree Projective x
    -> ConeLiftable Dst Projective d (Parallel LeftToRight) N2 N1 x
  ConeCokernelLiftable
    :: CokernelConic Cone d N1 x
    -> LiftableFree Injective x
    -> ConeLiftable Dst Injective d (Parallel RightToLeft) N2 N1 x

instance Conic ConeLiftable where
  cone (ConeKernelLiftable c _)   = c
  cone (ConeCokernelLiftable c _) = c


instance Show (d t n m x) => Show (ConeLiftable s p d t n m x) where
  show (ConeKernelLiftable k _) = "ConeKernelLiftable (" ++ show k ++ ") lftb"
  show (ConeCokernelLiftable k _) = "ConeCokernelLiftable (" ++ show k ++ ") lftb"
  
--------------------------------------------------------------------------------
-- cnLiftable -

-- | the underlying liftable.
cnLiftable :: ConeLiftable s p d t n m x -> LiftableFree p x
cnLiftable (ConeKernelLiftable _ lft)   = lft
cnLiftable (ConeCokernelLiftable _ lft) = lft

--------------------------------------------------------------------------------
-- cnlMapCov -

cnlMapCov ::
  ( NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Covariant (Inv2 (HomFree s)) x y
  -> ConeLiftable s p d t n m x -> ConeLiftable s p d t n m y
cnlMapCov (Covariant2 i) (ConeKernelLiftable k l) = ConeKernelLiftable k' l' where
  SDualBi (Right1 k') = amapG i (SDualBi (Right1 k))
  SDualBi (Right1 l') = amapG i (SDualBi (Right1 l))
cnlMapCov (Covariant2 i) (ConeCokernelLiftable k l) = ConeCokernelLiftable k' l' where
  SDualBi (Right1 k') = amapG i (SDualBi (Right1 k))
  SDualBi (Right1 l') = amapG i (SDualBi (Right1 l))

--------------------------------------------------------------------------------
-- cnlMapCnt -

cnlMapCnt ::
  ( NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Contravariant (Inv2 (HomFree s)) x y
  -> ConeLiftable s p d t n m x -> ConeLiftable s (Dual p) d (Dual t) n m y
cnlMapCnt (Contravariant2 i) (ConeKernelLiftable k l) = ConeCokernelLiftable k' l' where
  SDualBi (Left1 k') = amapG i (SDualBi (Right1 k))
  SDualBi (Left1 l') = amapG i (SDualBi (Right1 l))
cnlMapCnt (Contravariant2 i) (ConeCokernelLiftable k l) = ConeKernelLiftable k' l' where
  SDualBi (Left1 k') = amapG i (SDualBi (Right1 k))
  SDualBi (Left1 l') = amapG i (SDualBi (Right1 l))

--------------------------------------------------------------------------------
-- ConeLiftable - Dual -

type instance Dual1 (ConeLiftable s p d t n m) = ConeLiftable s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- cnlMapS -

cnlMapS ::
  ( NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel RightToLeft) N2 N1
  , p ~ Dual (Dual p)
  , t ~ Dual (Dual t)
  )
  => Inv2 (HomFree s) x y
  -> SDualBi (ConeLiftable s p d t n m) x -> SDualBi (ConeLiftable s p d t n m) y
cnlMapS = vmapBi cnlMapCov cnlMapCov cnlMapCnt cnlMapCnt

instance
  ( NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel RightToLeft) N2 N1
  , p ~ Dual (Dual p)
  , t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (ConeLiftable s p d t n m)) (Inv2 (HomFree s)) (->) where
  amapG = cnlMapS

instance
  ( NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel RightToLeft) N2 N1
  , p ~ Dual (Dual p)
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConeLiftable s p d t n m)) (Inv2 (HomFree s)) (->)

--------------------------------------------------------------------------------
-- toDualOpFree -

toDualOpFreeDst :: (Distributive x, SlicedFree x)
  => Variant2 Contravariant (Inv2 (HomFree Dst)) x (Op x)
toDualOpFreeDst = Contravariant2 (Inv2 (Sub t) (Sub f)) where
  Contravariant2 (Inv2 t f) = toDualOpDst

--------------------------------------------------------------------------------
-- prpConeLiftable -

relConeKernelLiftable ::
  ( Diagrammatic d
  , Show (d (Parallel LeftToRight) n m x)
  , Validable (d (Parallel LeftToRight) n m x)
  , Distributive x
  , XStandardOrtOrientation x
  )
  => N -> ConeLiftable s Projective d (Parallel LeftToRight) n m x -> Statement
relConeKernelLiftable kMax (ConeKernelLiftable c (LiftableFree l)) =
  And [ valid c
      , Forall (xNB 0 kMax)
          (\k -> case someNatural k of
              SomeNatural k' -> And [ valid (l k')
                                    , (lftbBase (l k') == kernelFactor c)
                                        :?> Params [ "k":=show k
                                                   , "c":=show c
                                                   ]
                                    ]
          )
      ]

-- | validity according to 'ConeLiftable'.
relConeLiftable ::
  ( Show (d (Parallel LeftToRight) n m x), Show (d (Parallel LeftToRight) n m (Op x))
  , Validable (d (Parallel LeftToRight) n m x), Validable (d (Parallel LeftToRight) n m (Op x))
  , Distributive x
  , SlicedFree x
  , XStandardOrtOrientation x
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel LeftToRight) n m
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel RightToLeft) n m
  , n ~ N2, m ~ N1
  )
  => N -> ConeLiftable s p d t n m x -> Statement
relConeLiftable kMax c@(ConeKernelLiftable _ _)   = relConeKernelLiftable kMax c
relConeLiftable kMax c@(ConeCokernelLiftable _ _) = relConeKernelLiftable kMax c' where
  Contravariant2 i   = toDualOpFreeDst 
  SDualBi (Left1 c') = amapG i (SDualBi (Right1 c))


-- | validity according to 'ConeLiftable'.
prpConeLiftable ::
  ( Show (d (Parallel LeftToRight) n m x), Show (d (Parallel LeftToRight) n m (Op x))
  , Validable (d (Parallel LeftToRight) n m x), Validable (d (Parallel LeftToRight) n m (Op x))
  , Distributive x
  , SlicedFree x
  , XStandardOrtOrientation x
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel LeftToRight) n m
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel RightToLeft) n m
  , n ~ N2, m ~ N1
  )
  => N -> ConeLiftable s p d t n m x -> Statement
prpConeLiftable kMax c = Prp "ConeLiftable" :<=>: relConeLiftable kMax c

--------------------------------------------------------------------------------
-- NaturalDiagrammaticFree -

-- | helper class to avoid undecidable instances.
class
  ( NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel LeftToRight) n m
  , NaturalDiagrammatic (Inv2 (HomFree s)) d (Parallel RightToLeft) n m

  )
  => NaturalDiagrammaticFree s d n m

instance
  ( Show (d (Parallel LeftToRight) n m x), Show (d (Parallel LeftToRight) n m (Op x))
  , Validable (d (Parallel LeftToRight) n m x), Validable (d (Parallel LeftToRight) n m (Op x))
  , Distributive x
  , SlicedFree x
  , XStandardOrtOrientation x
  , NaturalDiagrammaticFree s d n m
  , n ~ N2, m ~ N1
  )
  => Validable (ConeLiftable s p d t n m x) where
  valid = prpConeLiftable 12


