
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
-- sliced structures with assigned /free/ 'Point's of some given /dimension/.
module OAlg.Entity.Slice.Free
  (

    -- * Free
    Free(..), free', freeN, castFree, isFree
  , SomeFree(..), sfrPoint, sfrMap

    -- * Sliced Free
  , SlicedFree(..), SldFr, HomOrientedSlicedFree
  , prpHomOrientedSlicedFree
  , SomeFreeSlice(..), slicedFree'
  
    -- * Diagram Free
  , DiagramFree(..),dgfDiagram
  , dgfMapS, dgfMapCov, dgfMapCnt
  
    -- * Some Free Slice Diagram
  , SomeFreeSliceDiagram(..)
  
    -- ** Duality
  , sfsdMapS, sfsdMapCov, sfsdMapCnt

    -- * Cone Liftable
  , ConeLiftable(..), cnLiftable, cnlMapS
    
    -- * Liftable Free
  , LiftableFree(..), liftFree
  , HomFreeOp
  , lftFrMapS, lftFrMapCov, lftFrMapCnt
  , NaturalDiagrammaticFree

  , CokernelsLiftableSomeFree, CokernelLiftableSomeFree
  
    -- * Free Tip
  , ConicFreeTip(..)
  , KernelsSomeFreeFreeTip, KernelSomeFreeFreeTip
  , KernelSliceFromSomeFreeTip(..)

    -- * Duality
  , toDualOpFreeDst

  ) where

import Data.Kind
import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
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
import OAlg.Hom.Oriented
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

--------------------------------------------------------------------------------
-- free' -

-- | @__k__@-'Free' of @__x__@, given by the proxy @__q x__@.
free' :: q x -> Any k -> Free k x
free' _ = Free

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

instance Eq (SomeFree c) where
  SomeFree (Free k) == SomeFree (Free k') = case k `cmpW` k' of
    EQ -> True
    _  -> False

instance Validable (SomeFree c) where
  valid (SomeFree k) = Label "SomeFree" :<=>: valid k

--------------------------------------------------------------------------------
-- sfrPoint -

-- | the given slice point.
sfrPoint :: SomeFree x -> Point x
sfrPoint (SomeFree f) = slicePoint f

--------------------------------------------------------------------------------
-- SliceFree -

-- | attest for @__k__@-free sliced structures.
class SlicedFree x where
  slicedFree :: Attestable k => Struct (Sld (Free k)) x

-- | attest for @__k__@-free sliced structures according to the given proxy type.
slicedFree' :: (SlicedFree x, Attestable k) => q x -> Any k -> Struct (Sld (Free k)) x
slicedFree' _ _ = slicedFree

{-
--------------------------------------------------------------------------------
-- tauSldFrTuple -

-- | decorating the @__s__@ structure with @__k__@ sliced free.
tauSldFrTuple :: (SlicedFree x, Attestable k) => Struct s x -> Struct (s,Sld (Free k)) x
tauSldFrTuple s = tauTuple s slicedFree
-}
--------------------------------------------------------------------------------
-- tauSldFreeOp -

-- | propagating to 'Op'
tauSldFreeOp :: Struct (Sld (Free k)) x -> Struct (Sld (Free k)) (Op x)
tauSldFreeOp Struct = Struct 

instance SlicedFree x => SlicedFree (Op x) where slicedFree = tauSldFreeOp slicedFree

--------------------------------------------------------------------------------
-- SldFr -

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

-- instance TransformableObjectClass (Mlt,SldFr) (HomDisj Mlt Op (HomEmpty Mlt))
-- instance TransformableObjectClass (Dst,SldFr) (HomDisj Dst Op (HomEmpty Dst))

-- instance FunctorialOriented (Sub (Mlt,SldFr) (HomDisjEmpty Mlt Op))
-- instance FunctorialOriented (Sub (Dst,SldFr) (HomDisjEmpty Dst Op))

instance Attestable k => Transformable (s,SldFr) (Sld (Free k)) where
  tau s = case tauSnd s of Struct -> slicedFree
  
--------------------------------------------------------------------------------
-- DiagramFree -

-- | predicate for diagrams with free points.
data DiagramFree t n m a = DiagramFree (FinList n (SomeFree a)) (Diagram t n m a)
  deriving (Show,Eq)

instance Oriented a => Validable (DiagramFree t n m a) where
  valid (DiagramFree sfs d) = Label "DiagramFree"
    :<=>: valid (sfs,d) && vld 0 sfs (dgPoints d) where
    vld :: Oriented a => N -> FinList n (SomeFree a) -> FinList n (Point a) -> Statement
    vld _ Nil Nil = SValid
    vld i (SomeFree k:|sfs) (p:|ps)
      = And [ (slicePoint k == p) :?> Params ["i":=show i,"k":=show k,"p":=show p]
            , vld (succ i) sfs ps
            ] 

--------------------------------------------------------------------------------
-- dgfDiagram -

-- | the underlying diagram.
dgfDiagram :: DiagramFree t n m a -> Diagram t n m a
dgfDiagram (DiagramFree _ d) = d

instance Diagrammatic DiagramFree where diagram = dgfDiagram

--------------------------------------------------------------------------------
-- HomOrientedSlicedFree -

-- | homomorphisms between 'SlicedFree' structures, i.e. homomorphisms between 'Oriented' structures
-- where 'pmap' preserves the @__k__@-parameterized slice points.
--
-- __Property__ Let @'HomOrientedSlicedFree' __h__@, then
-- for all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
--
-- (1) For all @__k__@ holds:
-- @'pmap' h ('slicePoint' '$' 'free'' qx k) '==' ('slicePoint' '$' 'free'' qy k)@ where
-- @k@ is in @'Free' __k x__@ and @qx@ is any proxy in @__q x__@
-- and @qy@ is any proxy in @__q y__@. 
class (HomOrientedDisjunctive h, Transformable (ObjectClass h) SldFr) => HomOrientedSlicedFree h

--------------------------------------------------------------------------------
-- prpHomOrientedSlicedFree -

relHomOrientedSlicedFreeStruct :: (HomOrientedSlicedFree h, Show2 h)
  => Struct Ort x -> Struct Ort y
  -> Struct SldFr x -> Struct SldFr y
  -> h x y -> Any k -> Statement
relHomOrientedSlicedFreeStruct sx@Struct sy@Struct Struct Struct h k = case ats k of
  Ats               -> case (slicedFree' sx k,slicedFree' sy k) of
    (Struct,Struct) -> (  pmap h (slicePoint $ free' sx k)
                       == (slicePoint $ free' sy k)
                       ) :?> Params [ "h":=show2 h
                                    , "k":=show k
                                    ]

relHomOrientedSlicedFree :: (HomOrientedSlicedFree h, Show2 h)
  => h x y -> Any k -> Statement
relHomOrientedSlicedFree h k
  = relHomOrientedSlicedFreeStruct
      (tau $ domain h) (tau $ range h) (tau $ domain h) (tau $ range h) h k

-- | validity according to 'HomOrientedSlicedFree'.
prpHomOrientedSlicedFree :: (HomOrientedSlicedFree h, Show2 h)
  => h x y -> Any k -> Statement
prpHomOrientedSlicedFree h k = Prp "HomOrientedSlicedFree" :<=>: relHomOrientedSlicedFree h k

--------------------------------------------------------------------------------
-- sfrMap -

sfrMapStruct :: Struct SldFr y -> Variant2 v h x y -> SomeFree x -> SomeFree y
sfrMapStruct Struct h (SomeFree (Free k)) = case slicedFree' h k of Struct -> SomeFree (Free k)

-- | mapping of 'SomeFree'.
sfrMap :: HomOrientedSlicedFree h => Variant2 v h x y -> SomeFree x -> SomeFree y
sfrMap h@(Covariant2 hCov)     = sfrMapStruct (tau $ range hCov) h
sfrMap h@(Contravariant2 hCnt) = sfrMapStruct (tau $ range hCnt) h

--------------------------------------------------------------------------------
-- dgfMapCov -

-- | covariant mapping of 'DiagramFree'.
dgfMapCov :: HomOrientedSlicedFree h
  => Variant2 Covariant h x y -> DiagramFree t n m x -> DiagramFree t n m y
dgfMapCov h (DiagramFree fs d) = DiagramFree fs' d' where
  fs' = amap1 (sfrMap h) fs
  d'  = dgMapCov h d

--------------------------------------------------------------------------------
-- dgfMapCnt -

-- | contravariant mapping of 'DiagramFree'.
dgfMapCnt :: HomOrientedSlicedFree h
  => Variant2 Contravariant h x y -> DiagramFree t n m x -> DiagramFree (Dual t) n m y
dgfMapCnt h (DiagramFree fs d) = DiagramFree fs' d' where
  fs' = amap1 (sfrMap h) fs
  d'  = dgMapCnt h d

--------------------------------------------------------------------------------
-- DiagramFree - Dual -

type instance Dual1 (DiagramFree t n m) = DiagramFree (Dual t) n m

--------------------------------------------------------------------------------
-- dgfMapS -

-- | mapping of 'DiagramFree'.
dgfMapS :: (HomOrientedSlicedFree h, t ~ Dual (Dual t))
  => h x y -> SDualBi (DiagramFree t n m) x -> SDualBi (DiagramFree t n m) y
dgfMapS = vmapBi dgfMapCov dgfMapCov dgfMapCnt dgfMapCnt

instance (HomOrientedSlicedFree h, t ~ Dual (Dual t))
  => ApplicativeG (SDualBi (DiagramFree t n m)) h (->) where
  amapG = dgfMapS

instance
  ( HomOrientedSlicedFree h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (DiagramFree t n m)) h (->)

--------------------------------------------------------------------------------
-- DiagramFree - NaturalDiagrammatic -

instance
  ( HomOrientedSlicedFree h
  , t ~ Dual (Dual t)
  )
  =>  ApplicativeG (SDualBi (DiagramG DiagramFree t n m)) h (->) where
  amapG h = sdbFromDgmObj . amapG h . sdbToDgmObj

instance
  ( HomOrientedSlicedFree h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  =>  FunctorialG (SDualBi (DiagramG DiagramFree t n m)) h (->)
  
instance
  ( HomOrientedSlicedFree h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => NaturalTransformable h (->)
       (SDualBi (DiagramG DiagramFree t n m)) (SDualBi (DiagramG Diagram t n m))
instance
  ( CategoryDisjunctive h
  , HomOrientedSlicedFree h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammatic h DiagramFree t n m

--------------------------------------------------------------------------------
-- SomeFreeSliceDiagram -

-- | some free slice diagram for kernels and cokernels diagrams.
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
-- sfsdMapCov -

sfsdMapCovStruct :: HomOrientedSlicedFree h
  => Struct SldFr y -> Variant2 Covariant h x y
  -> SomeFreeSliceDiagram t n m x -> SomeFreeSliceDiagram t n m y
sfsdMapCovStruct Struct h (SomeFreeSliceKernel (SliceFrom (Free k) f))
  = case slicedFree' h k of Struct -> SomeFreeSliceKernel (SliceFrom (Free k) (amap h f))
sfsdMapCovStruct Struct h (SomeFreeSliceCokernel (SliceTo (Free k) f))
  = case slicedFree' h k of Struct -> SomeFreeSliceCokernel (SliceTo (Free k) (amap h f))

-- | covariant mapping of 'SomeFreeSliceDiagram'.
sfsdMapCov ::HomOrientedSlicedFree h
  => Variant2 Covariant h x y
  -> SomeFreeSliceDiagram t n m x -> SomeFreeSliceDiagram t n m y
sfsdMapCov h = sfsdMapCovStruct (tau $ range h) h
  
--------------------------------------------------------------------------------
-- sfsdMapCnt -

sfsdMapCntStruct :: HomOrientedSlicedFree h
  => Struct SldFr y -> Variant2 Contravariant h x y
  -> SomeFreeSliceDiagram t n m x -> SomeFreeSliceDiagram (Dual t) n m y
sfsdMapCntStruct Struct h (SomeFreeSliceKernel (SliceFrom (Free k) f))
  = case slicedFree' h k of Struct -> SomeFreeSliceCokernel (SliceTo (Free k) (amap h f))
sfsdMapCntStruct Struct h (SomeFreeSliceCokernel (SliceTo (Free k) f))
  = case slicedFree' h k of Struct -> SomeFreeSliceKernel (SliceFrom (Free k) (amap h f))

-- | contravariant mapping of 'SomeFreeSliceDiagram'.
sfsdMapCnt ::HomOrientedSlicedFree h
  => Variant2 Contravariant h x y
  -> SomeFreeSliceDiagram t n m x -> SomeFreeSliceDiagram (Dual t) n m y
sfsdMapCnt h = sfsdMapCntStruct (tau $ range h) h

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (SomeFreeSliceDiagram t n m) = SomeFreeSliceDiagram (Dual t) n m

--------------------------------------------------------------------------------
-- sfsdMapS -

-- | mapping of 'SomeFreeSliceDiagram'.
sfsdMapS :: (HomOrientedSlicedFree h, t ~ Dual (Dual t))
  => h x y -> SDualBi (SomeFreeSliceDiagram t n m) x -> SDualBi (SomeFreeSliceDiagram t n m) y
sfsdMapS = vmapBi sfsdMapCov sfsdMapCov sfsdMapCnt sfsdMapCnt 

--------------------------------------------------------------------------------
-- FunctorialG -

instance (HomOrientedSlicedFree h, t ~ Dual (Dual t))
  => ApplicativeG (SDualBi (SomeFreeSliceDiagram t n m)) h (->) where
  amapG = sfsdMapS

instance (HomOrientedSlicedFree h, FunctorialOriented h, t ~ Dual (Dual t))
  => FunctorialG (SDualBi (SomeFreeSliceDiagram t n m)) h (->)

instance (HomOrientedSlicedFree h, FunctorialOriented h, t ~ Dual (Dual t))
  => ApplicativeG (SDualBi (DiagramG SomeFreeSliceDiagram t n m)) h (->) where
  amapG h = sdbFromDgmObj . amapG h . sdbToDgmObj
  
instance (HomOrientedSlicedFree h, FunctorialOriented h, t ~ Dual (Dual t))
  => FunctorialG (SDualBi (DiagramG SomeFreeSliceDiagram t n m)) h (->)

instance (HomOrientedSlicedFree h, FunctorialOriented h, t ~ Dual (Dual t))
  => NaturalTransformable h (->)
       (SDualBi (DiagramG SomeFreeSliceDiagram t n m))
       (SDualBi (DiagramG Diagram t n m))

instance
  ( CategoryDisjunctive h
  , HomOrientedSlicedFree h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammatic h SomeFreeSliceDiagram t n m

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
-- HomFreeOp -

-- | homomorphism between free sliced structures.
type HomFreeOp s = HomDisjEmpty (s,SldFr) Op

instance Transformable (s,SldFr) Type where tau _ = Struct
instance TransformableType (s,SldFr)

instance Transformable (s,SldFr) SldFr where tau = tauSnd

instance TransformableG Op SldFr SldFr where tauG Struct = Struct

instance TransformableG Op s s => TransformableG Op (s,SldFr) s where tauG = tauG . tauFst
instance TransformableOp s => TransformableOp (s,SldFr)

instance TransformableG Op (s,SldFr) SldFr where tauG = tauG . tauSnd

instance
  ( TransformableOrt s
  , TransformableOp s
  )
  => HomOrientedSlicedFree (HomFreeOp s)

instance
  ( TransformableOrt s
  , TransformableOp s
  )
  => HomOrientedSlicedFree (Inv2 (HomFreeOp s))

instance
  ( TransformableOrt s
  , TransformableOp s
  , Attestable k
  )
  => HomOrientedSliced (Free k) (HomFreeOp s)

--------------------------------------------------------------------------------
-- lftFrMapCov -

lftFrMapCovk ::
  ( TransformableOp s
  , TransformableMlt s
  )
  => Variant2 Covariant (Inv2 (HomFreeOp s)) x y -> LiftableFree p x -> Any k -> Liftable p (Free k) y
lftFrMapCovk i lf k = case ats k of Ats -> lftMapCov i (liftFree lf k) 

lftFrMapCov ::
  ( TransformableOp s
  , TransformableMlt s
  )
  => Variant2 Covariant (Inv2 (HomFreeOp s)) x y -> LiftableFree p x -> LiftableFree p y
lftFrMapCov i lf = LiftableFree (lftFrMapCovk i lf)

--------------------------------------------------------------------------------
-- lftFrMapCnt -

lftFrMapCntk ::
  ( TransformableOp s
  , TransformableMlt s
  )
  => Variant2 Contravariant (Inv2 (HomFreeOp s)) x y
  -> LiftableFree p x -> Any k -> Liftable (Dual p) (Free k) y
lftFrMapCntk i lf k = case ats k of Ats -> lftMapCnt i (liftFree lf k) 

lftFrMapCnt ::
  ( TransformableOp s
  , TransformableMlt s
  )
  => Variant2 Contravariant (Inv2 (HomFreeOp s)) x y -> LiftableFree p x -> LiftableFree (Dual p) y
lftFrMapCnt i lf = LiftableFree (lftFrMapCntk i lf)

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (LiftableFree p) = LiftableFree (Dual p)

--------------------------------------------------------------------------------
-- lftFrMapS -

lftFrMapS ::
  ( TransformableOp s
  , TransformableMlt s
  , p ~ Dual (Dual p)
  )
  => Inv2 (HomFreeOp s) x y -> SDualBi (LiftableFree p) x -> SDualBi (LiftableFree p) y
lftFrMapS = vmapBi lftFrMapCov lftFrMapCov lftFrMapCnt lftFrMapCnt

instance
  ( TransformableOp s
  , TransformableMlt s
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (LiftableFree p)) (Inv2 (HomFreeOp s)) (->) where
  amapG = lftFrMapS

instance
  ( TransformableOp s
  , TransformableMlt s
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (LiftableFree p)) (Inv2 (HomFreeOp s)) (->)

--------------------------------------------------------------------------------
-- ConeLiftable -

-- | predicate for a liftable conic object.
--
-- __Property__ Let @cl@ be in @'ConeLiftable' __s p d t n m x__@, then holds:
--
-- (1) If @cl@ matches @'ConeKernelLiftable' c ('LiftableFree' l)@, then
-- for any @k@ in @'Any' __k__@ holds:
-- @'lftbBase' (l k)' '==' 'kernelFactor' c@.
--
-- (2) If @cl@ matches @'ConeCokernelLiftable' c ('LiftableFree' l)@, then
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

-- | covariant mapping of 'ConeLiftable'.
cnlMapCov ::
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Covariant (Inv2 (HomFreeOp s)) x y
  -> ConeLiftable s p d t n m x -> ConeLiftable s p d t n m y
cnlMapCov (Covariant2 i) (ConeKernelLiftable k l) = ConeKernelLiftable k' l' where
  SDualBi (Right1 k') = amapG i (SDualBi (Right1 k))
  SDualBi (Right1 l') = amapG i (SDualBi (Right1 l))
cnlMapCov (Covariant2 i) (ConeCokernelLiftable k l) = ConeCokernelLiftable k' l' where
  SDualBi (Right1 k') = amapG i (SDualBi (Right1 k))
  SDualBi (Right1 l') = amapG i (SDualBi (Right1 l))

--------------------------------------------------------------------------------
-- cnlMapCnt -

-- | contravariant mapping of 'ConeLiftable'.
cnlMapCnt ::
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Contravariant (Inv2 (HomFreeOp s)) x y
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

-- | mapping of 'ConeLiftable'.
cnlMapS ::
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , p ~ Dual (Dual p)
  , t ~ Dual (Dual t)
  )
  => Inv2 (HomFreeOp s) x y
  -> SDualBi (ConeLiftable s p d t n m) x -> SDualBi (ConeLiftable s p d t n m) y
cnlMapS = vmapBi cnlMapCov cnlMapCov cnlMapCnt cnlMapCnt

instance
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , p ~ Dual (Dual p)
  , t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (ConeLiftable s p d (Parallel t) n m)) (Inv2 (HomFreeOp s)) (->) where
  amapG = cnlMapS

instance
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , p ~ Dual (Dual p)
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConeLiftable s p d (Parallel t) n m)) (Inv2 (HomFreeOp s)) (->)

instance
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , p ~ Dual (Dual p)
  , t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (ConeG ConeLiftable s p d (Parallel t) n m)) (Inv2 (HomFreeOp s)) (->) where
  amapG h = sdbFromCncObj . amapG h . sdbToCncObj

instance
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , p ~ Dual (Dual p)
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConeG ConeLiftable s p d (Parallel t) n m)) (Inv2 (HomFreeOp s)) (->)

instance
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , s ~ Dst
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable (Inv2 (HomFreeOp s)) (->)
           (SDualBi (ConeG ConeLiftable s p d (Parallel LeftToRight) N2 N1))
           (SDualBi (ConeG Cone s p d (Parallel LeftToRight) N2 N1))

instance
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , s ~ Dst
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable (Inv2 (HomFreeOp s)) (->)
           (SDualBi (ConeG ConeLiftable s p d (Parallel RightToLeft) N2 N1))
           (SDualBi (ConeG Cone s p d (Parallel RightToLeft) N2 N1))

instance
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , s ~ Dst
  , p ~ Dual (Dual p)
  )
  => NaturalConic (Inv2 (HomFreeOp s)) ConeLiftable s p d (Parallel RightToLeft) N2 N1

instance
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) N2 N1
  , s ~ Dst
  , p ~ Dual (Dual p)
  )
  => NaturalConic (Inv2 (HomFreeOp s)) ConeLiftable s p d (Parallel LeftToRight) N2 N1

--------------------------------------------------------------------------------
-- CokernelLiftableSomeFree -

-- | liftable cokernels for some free slice diagram
type CokernelLiftableSomeFree  = CokernelG ConeLiftable SomeFreeSliceDiagram N1

-- | liftable cokernels for some free slice diagram
type CokernelsLiftableSomeFree = CokernelsG ConeLiftable SomeFreeSliceDiagram N1

--------------------------------------------------------------------------------
-- toDualOpFree -

instance TransformableGRefl Op s => TransformableGRefl Op (s,SldFr)

-- | to dual operator.
toDualOpFreeDst :: (Distributive x, SlicedFree x)
  => Variant2 Contravariant (Inv2 (HomFreeOp Dst)) x (Op x)
toDualOpFreeDst = toDualO Struct

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
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) n m
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) n m
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
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) n m
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) n m
  , n ~ N2, m ~ N1
  )
  => N -> ConeLiftable s p d t n m x -> Statement
prpConeLiftable kMax c = Prp "ConeLiftable" :<=>: relConeLiftable kMax c

--------------------------------------------------------------------------------
-- NaturalDiagrammaticFree -

-- | helper class to avoid undecidable instances.
class
  ( NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel LeftToRight) n m
  , NaturalDiagrammatic (Inv2 (HomFreeOp s)) d (Parallel RightToLeft) n m

  )
  => NaturalDiagrammaticFree s d n m

instance NaturalDiagrammaticFree Dst DiagramFree n m
instance NaturalDiagrammaticFree Dst Diagram n m

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


--------------------------------------------------------------------------------
-- ConicFreeTip -

-- | predicate for a 'Conic' object with a free 'tip'.
--
-- __Property__ Let @c@ be in @'ConicFreeTip' __c s p d t n m x__@, then holds:
--
-- (1) @'slicePoint' k '==' 'tip' ('cone' c)@.
data ConicFreeTip c s
       (p :: Perspective)
       (d :: DiagramType -> N' -> N' -> Type -> Type)
       (t :: DiagramType)
       (n :: N') (m :: N') x where
  ConicFreeTip :: (Attestable k, Sliced (Free k) x)
    => Free k x -> c s p d t n m x
    -> ConicFreeTip c s p d t n m x

instance Conic c => Conic (ConicFreeTip c) where
  cone (ConicFreeTip _ c) = cone c

deriving instance Show (c s p d t n m x) => Show (ConicFreeTip c s p d t n m x)

--------------------------------------------------------------------------------
-- KernelSomeFreeFreeTip -

-- | kernel with a free 'tip'.
type KernelSomeFreeFreeTip  = KernelG (ConicFreeTip Cone) SomeFreeSliceDiagram N1

-- | kernels with a free 'tip'.
type KernelsSomeFreeFreeTip = KernelsG (ConicFreeTip Cone) SomeFreeSliceDiagram N1

--------------------------------------------------------------------------------
-- prpConicFreeTip -

relConicFreeTip ::
  ( Conic c
  , Show (c s p d t n m x)
  , Validable (c s p d t n m x)
  )
  => ConicFreeTip c s p d t n m x -> Statement
relConicFreeTip (ConicFreeTip k c)
  = And [ valid k
        , valid c
        , (slicePoint k == tip (cone c))
            :?> Params [ "k":= show k
                       , "c":= show c
                       ]
        ]

-- | validity according to 'ConicFreeTip'.
prpConicFreeTip ::
  ( Conic c
  , Show (c s p d t n m x)
  , Validable (c s p d t n m x)
  )
  => ConicFreeTip c s p d t n m x -> Statement
prpConicFreeTip c = Prp "ConicFreeTip" :<=>: relConicFreeTip c

instance
  ( Conic c
  , Show (c s p d t n m x)
  , Validable (c s p d t n m x)
  )
  => Validable (ConicFreeTip c s p d t n m x) where
  valid = prpConicFreeTip

--------------------------------------------------------------------------------
-- cnftConeMapCov -

cnftConeMapDstCovStruct ::
  ( NaturalDiagrammatic h d t n m
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  )
  => Struct SldFr y
  -> Variant2 Covariant h x y
  -> ConicFreeTip Cone Dst p d t n m x
  -> ConicFreeTip Cone Dst p d t n m y
cnftConeMapDstCovStruct Struct h (ConicFreeTip (Free k) c)
  = case slicedFree' h k of Struct -> ConicFreeTip (Free k) (cnMapDstCov h c)

cnftConeMapDstCov ::
  ( NaturalDiagrammatic h d t n m
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  )
  => Variant2 Covariant h x y
  -> ConicFreeTip Cone Dst p d t n m x
  -> ConicFreeTip Cone Dst p d t n m y
cnftConeMapDstCov h = cnftConeMapDstCovStruct (tau $ range h) h

--------------------------------------------------------------------------------
-- cnftConeMapCnt -

cnftConeMapDstCntStruct ::
  ( NaturalDiagrammatic h d t n m
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  )
  => Struct SldFr y
  -> Variant2 Contravariant h x y
  -> ConicFreeTip Cone Dst p d t n m x
  -> ConicFreeTip Cone Dst (Dual p) d (Dual t) n m y
cnftConeMapDstCntStruct Struct h (ConicFreeTip (Free k) c)
  = case slicedFree' h k of Struct -> ConicFreeTip (Free k) (cnMapDstCnt h c)

cnftConeMapDstCnt ::
  ( NaturalDiagrammatic h d t n m
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  )
  => Variant2 Contravariant h x y
  -> ConicFreeTip Cone Dst p d t n m x
  -> ConicFreeTip Cone Dst (Dual p) d (Dual t) n m y
cnftConeMapDstCnt h = cnftConeMapDstCntStruct (tau $ range h) h

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (ConicFreeTip c s p d t n m) = ConicFreeTip c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- cnftConeMapDstS -

cnftConeMapDstS ::
  ( NaturalDiagrammaticBi h d t n m
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  , p ~ Dual (Dual p)
  )
  => h x y
  -> SDualBi (ConicFreeTip Cone Dst p d t n m) x -> SDualBi (ConicFreeTip Cone Dst p d t n m) y
cnftConeMapDstS = vmapBi cnftConeMapDstCov cnftConeMapDstCov cnftConeMapDstCnt cnftConeMapDstCnt

instance
  ( CategoryDisjunctive h
  , FunctorialOriented h
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (ConicFreeTip Cone Dst p SomeFreeSliceDiagram t n m)) h (->)
  where amapG = cnftConeMapDstS 

instance
  ( CategoryDisjunctive h
  , FunctorialOriented h
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConicFreeTip Cone Dst p SomeFreeSliceDiagram t n m)) h (->)

instance
  ( CategoryDisjunctive h
  , FunctorialOriented h
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (ConeG (ConicFreeTip Cone) Dst p SomeFreeSliceDiagram t n m)) h (->)
  where amapG h = sdbFromCncObj . amapG h . sdbToCncObj

instance
  ( CategoryDisjunctive h
  , FunctorialOriented h
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConeG (ConicFreeTip Cone) Dst p SomeFreeSliceDiagram t n m)) h (->)

instance
  ( CategoryDisjunctive h
  , FunctorialOriented h
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => NaturalTransformable h (->)
           (SDualBi (ConeG (ConicFreeTip Cone) Dst p SomeFreeSliceDiagram t n m))
           (SDualBi (ConeG Cone Dst p SomeFreeSliceDiagram t n m))

instance
  ( CategoryDisjunctive h
  , FunctorialOriented h
  , HomOrientedSlicedFree h
  , HomDistributiveDisjunctive h
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => NaturalConic h (ConicFreeTip Cone) Dst p SomeFreeSliceDiagram t n m
  
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


