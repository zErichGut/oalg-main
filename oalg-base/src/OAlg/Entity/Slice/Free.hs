
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
  , ConeLiftable(..), cnLiftable

  ) where

import Control.Monad (join)

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.Dualisable

import OAlg.Data.Singleton
import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Fibred
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.FibredOriented
import OAlg.Hom.Additive
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
-- ConeLiftable -

-- | predicate for a liftable conic object.
--
-- __Property__ Let @cl@ be in @'ConeLiftable' __s p d t n m x__@, then holds:
--
-- (1) If @cl@ matches @'ConeKernelLiftableFree' c l@, then for any @k@ in @'Any' __k__@ holds:
-- @'lftbBase' (l k)' '==' 'kernelFactor' ('universalCone' c)@.
--
-- (2) If @cl@ matches @'ConeCokernelLiftableFree' c l@, then for any @k@ in @'Any' __k__@ holds:
-- @'lftbBase' (l k)' '==' 'cokernelFactor' c@.
data ConeLiftable s p d t n m x where
  ConeKernelLiftable
    :: (KernelConic Cone d N1 x)
    -> (forall (k :: N') . Any k -> Liftable Projective (Free k) x)
    -> ConeLiftable Dst Projective d (Parallel LeftToRight) N2 N1 x
  ConeCokernelLiftable
    :: (CokernelConic Cone d N1 x)
    -> (forall (k :: N') . Any k -> Liftable Injective (Free k) x)
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
cnLiftable :: ConeLiftable s p d t n m x -> Any k -> Liftable p (Free k) x
cnLiftable (ConeKernelLiftable _ lft)   = lft
cnLiftable (ConeCokernelLiftable _ lft) = lft

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
-- tauSldFreeOp -
{-
-- | transforming 'SlicedFree' @__s__@-structures to 'Op'.
tauSldFreeOp :: TransformableG Op s s => Struct (s,Sld (Free k)) x -> Struct (s,Sld (Free k)) (Op x)
tauSldFreeOp s@Struct = case tauOp (tauFst s) of Struct -> Struct
-}

tauSldFreeOp :: Struct (Sld (Free k)) x -> Struct (Sld (Free k)) (Op x)
tauSldFreeOp Struct = Struct 

instance SlicedFree x => SlicedFree (Op x) where slicedFree = tauSldFreeOp slicedFree

{-
--------------------------------------------------------------------------------
-- HomFree -

-- | homomorphism between free sliced @__s__@-structures.
data HomFree s x y where
  HomFree :: (SlicedFree s x, SlicedFree s y)
          => (forall k . HomDisjEmpty (s,Sld (Free k)) Op x y)
          -> HomFree s x y

instance Disjunctive2 (HomFree s) where
  variant2 (HomFree h) = variant2 h


--------------------------------------------------------------------------------
-- SdlFr -

-- | 'SlicedFree' structures. 
data SldFr

type instance Structure SldFr x = SlicedFree x


--------------------------------------------------------------------------------
-- tauSldFre -

-- | transforming 'SlicedFree' @__s__@ structures to @(__s__,'Sld' ('Free' __k__)@-structures.
tauSldFr :: Struct (SldFr s) x -> Struct (s,Sld (Free k)) x
tauSldFr Struct = slicedFree

instance Transformable s Ort => Transformable (SldFr s) Ort where tau = tau . tauFst . tauSldFr
instance Transformable s Mlt => Transformable (SldFr s) Mlt where tau = tau . tauFst . tauSldFr
-}

--------------------------------------------------------------------------------
-- lftFrMapCov -

lftFrSub :: q k
   -> Struct (s,Sld (Free k)) x -> Struct (s,Sld (Free k)) y
   -> Variant2 v (IsoO s Op) x y
   -> Variant2 v (Inv2 (Sub (s,Sld (Free k)) (HomDisjEmpty s Op))) x y
lftFrSub _ sx sy (Covariant2 (Inv2 t f))
  = Covariant2 (Inv2 (sub' (sx:>:sy) t) (sub' (sy:>:sx) f))
lftFrSub _ sx sy (Contravariant2 (Inv2 t f))
  = Contravariant2 (Inv2 (sub' (sx:>:sy) t) (sub' (sy:>:sx) f))


instance Transformable (s,Sld i) s
  => TransformableObjectClass (s,Sld i) (HomDisjEmpty s Op)

tauSldFrTuple :: SlicedFree x => Struct s x -> Struct (s,Sld (Free k)) x
tauSldFrTuple s = tauTuple s slicedFree

lftFrMapCovStruct ::
  ( TransformableType s
  , TransformableOp s
  , TransformableMlt s
  , Transformable (s,Sld (Free k)) s
  , SlicedFree x
  , SlicedFree y
  )
  => Struct s x -> Struct s y
  -> Variant2 Covariant (IsoO s Op) x y -> LiftableFree p x -> Any k -> Liftable p (Free k) y
lftFrMapCovStruct sx sy i lf k = lftMapCov (lftFrSub k sfx sfy i) (liftFree lf k) where
  sfx = tauSldFrTuple sx
  sfy = tauSldFrTuple sy


hh ::
  ( TransformableType s
  , TransformableOp s
  , TransformableMlt s
  , Transformable (s,Sld (Free k)) s
  , SlicedFree x
  , SlicedFree y
  )
  => Variant2 Covariant (IsoO s Op) x y -> LiftableFree p x -> Any k -> Liftable p (Free k) y
hh i lf = lftFrMapCovStruct (domain i) (range i) i lf

hhDst ::
  ( s ~ Mlt
  , SlicedFree x
  , SlicedFree y
  )
  => Variant2 Covariant (IsoO s Op) x y -> LiftableFree p x -> LiftableFree p y
hhDst i lf = LiftableFree (hh i lf)



{-
lftFrMapCovHomFree :: Variant2 Covariant (Inv2 (HomFree Dst)) x y
      -> LiftableFree p x -> Any k -> Liftable p (Free k) y
lftFrMapCovHomFree h = lftFrMapCovIsoO (isoHomFrIsoOp h)

-- | mapping free liftables according a covariant 'HomFree'
lftFrMapCov :: Variant2 Covariant (Inv2 (HomFree Dst)) x y -> LiftableFree p x -> LiftableFree p y
lftFrMapCov h lf = LiftableFree (lftFrMapCovHomFree h lf)
-}





{-  
data HomSliceFree s k h where
  HomSliceFreeDst :: (CategoryDisjunctive h, HomSlicedDistributive (Free k) h) => HomSliceFree Dst k h 

data HomFree s h where
  HomFreeDst :: (forall k . Any k -> HomSliceFree Dst k h) -> HomFree Dst h

gg :: HomFree Dst h
    -> Variant2 Covariant (Inv2 h) x y -> LiftableFree p x -> Any k -> Liftable p (Free k) y
gg (HomFreeDst f) i lf k = case f k of HomSliceFreeDst -> ff i lf k

gg' :: HomFree Dst h
    -> Variant2 Covariant (Inv2 h) x y -> LiftableFree p x -> LiftableFree p y
gg' hf i lf = LiftableFree (gg hf i lf)

class CC s h where
  cc :: HomFree s h


gg'' :: CC Dst h => Variant2 Covariant (Inv2 h) x y -> LiftableFree p x -> LiftableFree p y
gg'' = gg' cc


cc' :: HomSliceFree Dst k (HomDisjEmpty (Dst,Sld (Free k)) Op)
cc' = HomSliceFreeDst
-}

{-
hh :: CC Dst h => Variant2 Covariant (Inv2 h) x y -> LiftableFree p x -> Any k -> Liftable p (Free k) y
hh h lf k = case cc k of HomSliceFreeDst -> ff h lf k
-}

{-
instance ApplicativeG Id (HomFree Dst h) (->) where
  amapG (HomFreeDst h) = amapG h
-}

{-
ff :: Variant2 Covariant (Inv2 (HomFree Dst h)) x y -> LiftableFree p x -> LiftableFree p y
ff (Covariant2 (Inv2 (HomFreeDst t) (HomFreeDst f))) l = l' error "nyi"
-}


{-
-1-------------------------------------------------------------------------------
-- HomSliceFree -

data HomSliceFree s k h where
  HomSliceFreeDst :: HomSlicedDistributive (Free k) h => HomSliceFree Dst k h 

data HomConeLiftable s h x y where
  HomConeLiftableDst
    :: h x y -> (forall k . Any k -> HomSliceFree Dst k h) -> HomConeLiftable Dst h x y

instance ApplicativeG Id h (->) => ApplicativeG Id (HomConeLiftable s h) (->) where
  amapG (HomConeLiftableDst h _) = amapG h

instance ApplicativeG Pnt h (->) => ApplicativeG Pnt (HomConeLiftable s h) (->) where
  amapG (HomConeLiftableDst h _) = amapG h

instance ApplicativeG Rt h (->) => ApplicativeG Rt (HomConeLiftable s h) (->) where
  amapG (HomConeLiftableDst h _) = amapG h

instance Morphism h => Morphism (HomConeLiftable s h) where
  type ObjectClass (HomConeLiftable s h) = ObjectClass h
  homomorphous (HomConeLiftableDst h _) = homomorphous h

class CC s h where
  cc :: Any k -> HomSliceFree s k h

{-
instance CC Dst (HomDisjEmpty (Dst,Sld (Free k)) Op) where
  cc _ = HomSliceFreeDst
-}  
instance (Category h, CC Dst h) => Category (HomConeLiftable Dst h) where
  cOne s = HomConeLiftableDst (cOne s) cc
  HomConeLiftableDst f lf . HomConeLiftableDst g _ = HomConeLiftableDst (f.g) lf
  
instance Disjunctive2 h => Disjunctive2 (HomConeLiftable s h) where
  variant2 (HomConeLiftableDst h _) = variant2 h

instance (CategoryDisjunctive h, CC Dst h) => CategoryDisjunctive (HomConeLiftable Dst h)

instance HomOrientedDisjunctive h => HomOrientedDisjunctive (HomConeLiftable s h)
instance HomMultiplicativeDisjunctive h => HomMultiplicativeDisjunctive (HomConeLiftable s h)
instance HomFibred h => HomFibred (HomConeLiftable s h)
instance HomAdditive h => HomAdditive (HomConeLiftable s h)
instance HomFibredOrientedDisjunctive h => HomFibredOrientedDisjunctive (HomConeLiftable s h)
instance HomDistributiveDisjunctive h => HomDistributiveDisjunctive (HomConeLiftable s h)

instance HomSlicedOriented (Free k) h => HomSlicedOriented (Free k) (HomConeLiftable Dst h)
  
--------------------------------------------------------------------------------
-- cnlMapDstCov -

cnlMapDstCov ::
  ( CategoryDisjunctive h
  , CC Dst h
  , HomDistributiveDisjunctive h
  , NaturalDiagrammatic (Inv2 (HomConeLiftable Dst h)) d (Parallel LeftToRight) N2 N1
  , NaturalDiagrammatic (Inv2 (HomConeLiftable Dst h)) d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Covariant (Inv2 (HomConeLiftable Dst h)) x y
  -> ConeLiftable Dst p d t n m x -> ConeLiftable Dst p d t n m y
cnlMapDstCov i@(Covariant2 i') (ConeKernelLiftable c l) = ConeKernelLiftable c' (lft' i l) where
  SDualBi (Right1 c') = amapG i' (SDualBi (Right1 c))
  
  lft' ::
     ( CategoryDisjunctive h
     , CC Dst h
     )
     => Variant2 Covariant (Inv2 (HomConeLiftable Dst h)) x y
     ->  (Any k -> Liftable Projective (Free k) x)
     -> Any k -> Liftable Projective (Free k) y
  lft' (Covariant2 i) l k = case i of
    Inv2 (HomConeLiftableDst _ w) _ -> case w k of
      HomSliceFreeDst -> l' where
        SDualBi (Right1 l') = amapG i (SDualBi (Right1 (l k)))


relConeLiftable ::
  ( Diagrammatic d
  , Show (d t n m x)
  , Validable (d t n m x)
  , Distributive x
  , XStandardOrtOrientation x
  )
  => N -> ConeLiftable s p d t n m x -> Statement
relConeLiftable kMax (ConeKernelLiftable c l) =
  And [ valid c
      , Forall (xNB 0 kMax)
          (\k -> case someNatural k of
              SomeNatural k' -> And [ valid (l k')
                                    , (lftbBase (l k') == kernelFactor c)
                                        :?> Params ["k":=show k
                                                   , "c":=show c
                                                   ]
                                    ]
          )
      ]
  
-}
