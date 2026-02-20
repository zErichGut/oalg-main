
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}


{-# LANGUAGE UndecidableInstances #-}

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
{-    
    -- * Homology
    homology, Homology    
  , betti, Betti
  
    -- * Homomorphism
  , homologyHom, HomologyHom
  , bettiHom, BettiHom

    -- * Homological
  , Homological(..)

    -- * Abelian
  , cnzFreeAbl, cnzFreeHomAbl
-}
  ) where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Ring

import OAlg.Entity.Diagram as D 
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Slice
import OAlg.Entity.Matrix

import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels
import OAlg.AbelianGroup.Free.SmithNormalForm

import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.Free

import OAlg.LinearAlgebra.ConsecutiveZero

--------------------------------------------------------------------------------

import Data.Typeable

import OAlg.Structure.Exception
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive

import OAlg.Limes.Definition
import OAlg.Limes.Cone

--------------------------------------------------------------------------------
-- ConsecutiveZeroFreeHom - Distributive -

type instance Root (ConsecutiveZeroFreeHom t n x) = Orientation (ConsecutiveZeroFree t n x)

instance (Show x, ShowPoint x) => ShowRoot (ConsecutiveZeroFreeHom t n x)
instance (Eq x, EqPoint x) => EqRoot (ConsecutiveZeroFreeHom t n x)
instance (Distributive x, ValidablePoint x) => ValidableRoot (ConsecutiveZeroFreeHom t n x)
instance (Typeable x, Typeable t, Typeable n) => TypeableRoot (ConsecutiveZeroFreeHom t n x)

instance (Distributive x, Typeable t, Typeable n) => Fibred (ConsecutiveZeroFreeHom t n x)

instance (Distributive x, Typeable t, Typeable n) => Additive (ConsecutiveZeroFreeHom t n x) where
  zero (a:>b) = ConsecutiveZeroFreeHom a b fs where
    ConsecutiveZeroHom (DiagramTrafo _ _ fs) = zero (a':>b')
    ConsecutiveZeroFree a' _ = a
    ConsecutiveZeroFree b' _ = b

  ConsecutiveZeroFreeHom a b fs + ConsecutiveZeroFreeHom a' b' fs'
    | a :> b == a' :> b' = ConsecutiveZeroFreeHom a b (amap1 (uncurry (+)) (fs `zip` fs'))
    | otherwise          = throw NotAddable

  ntimes n (ConsecutiveZeroFreeHom a b fs) = ConsecutiveZeroFreeHom a b fs' where
    fs' = amap1 (ntimes n) fs 
    
instance (Distributive x, Abelian x, Typeable t, Typeable n)
  => Abelian (ConsecutiveZeroFreeHom t n x) where
  negate (ConsecutiveZeroFreeHom a b fs) = ConsecutiveZeroFreeHom a b (amap1 negate fs)

  ConsecutiveZeroFreeHom a b fs - ConsecutiveZeroFreeHom a' b' fs'
    | a :> b == a' :> b' = ConsecutiveZeroFreeHom a b (amap1 (uncurry (-)) (fs `zip` fs'))
    | otherwise          = throw NotAddable

  ztimes n (ConsecutiveZeroFreeHom a b fs) = ConsecutiveZeroFreeHom a b fs' where
    fs' = amap1 (ztimes n) fs 

instance (Distributive x, Typeable t, Typeable n) => FibredOriented (ConsecutiveZeroFreeHom t n x)
instance (Distributive x, Typeable t, Typeable n) => Distributive (ConsecutiveZeroFreeHom t n x)

--------------------------------------------------------------------------------
-- VarianceHomG - Distributive -

type instance Point (VarianceHomG t k c d n x) = VarianceG t k c d n x

class
  ( Conic k, Conic c
  , Show x, ShowPoint x
  , Show (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , Show (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  )
  => ShowVarianceG (t :: Site) k c d (n :: N') x

deriving instance ShowVarianceG t k c d n x => Show (VarianceG t k c d n x)
deriving instance ShowVarianceG t k c d n x => Show (VarianceHomG t k c d n x)

instance Eq (c s p d t n m x) => Eq (LimesG c s p d t n m x) where
  -- the universal property is uniquely determined by the universal cone!
  LimesProjective c _ == LimesProjective c' _ = c == c'
  LimesInjective c _ == LimesInjective c' _   = c == c'

class
  ( Conic k, Conic c
  , Eq x, EqPoint x
  , Eq (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , Eq (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  )
  => EqVarianceG (t :: Site) k c d (n :: N') x

deriving instance EqVarianceG t k c d n x => Eq (VarianceG t k c d n x)
deriving instance EqVarianceG t k c d n x => Eq (VarianceHomG t k c d n x)

instance ShowVarianceG t k c d n x => ShowPoint (VarianceHomG t k c d n x)
instance EqVarianceG t k c d n x => EqPoint (VarianceHomG t k c d n x)

instance
  ( Distributive x
  , Diagrammatic d
  , Conic k, Conic c
  , XStandardEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  , XStandardEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  , XStandardEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  , XStandardEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  , Show (d (Parallel LeftToRight) N2 N1 x)
  , Show (d (Parallel RightToLeft) N2 N1 x)
  , ShowVarianceG t k c d n x
  , Eq (d (Parallel LeftToRight) N2 N1 x)
  , Eq (d (Parallel RightToLeft) N2 N1 x)
  , Validable (d (Parallel LeftToRight) N2 N1 x)
  , Validable (d (Parallel RightToLeft) N2 N1 x)
  , Validable (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , Validable (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  , Typeable d
  )
  => Validable (VarianceG t k c d n x) where
  valid (VarianceG cz kcs) = Label "VarianceG" :<=>: valid cz && valid kcs
  
-- instance Validable (VarianceG t k c d n x) => ValidablePoint (VarianceHomG t k c d n x)

{-
instance
  (Typeable t, Typeable k, Typeable c, Typeable d, Typeable n, Typeable x)
  => TypeablePoint (VarianceHomG t k c d n x)
  
instance
  ( Show x, ShowPoint x
  , Show (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , Show (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  
  , EqPoint x, Eq x
  , Eq (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , Eq (c Dst Injective d (Parallel RightToLeft) N2 N1 x)

  , Validable (VarianceG t k c d n x)
  , Validable (VarianceHomG t k c d n x)
  , Typeable t, Typeable k, Typeable c, Typeable d, Typeable n, Typeable x
  )
  => Oriented (VarianceHomG t k c d n x) where
  orientation (VarianceHomG a b _) = a :> b
-}
--------------------------------------------------------------------------------
-- Homological -

-- | homological relation between a @'Galoisian' __r__@ and a @'Distributive' __h__@.
data Homological r h where
  HmlgZ :: Homological Z AbHom

hmlgDst :: Homological r h -> Struct Dst h
hmlgDst HmlgZ = Struct

--------------------------------------------------------------------------------
-- hmlgMonic -

hmlgMonic :: Homological r h -> Monic r
hmlgMonic HmlgZ = mncZ

--------------------------------------------------------------------------------
-- hmlgDiagonalizable -

hmlgDiagonalizable :: Homological r h -> Diagonalizable r
hmlgDiagonalizable HmlgZ = dgzZ

--------------------------------------------------------------------------------
-- hmlgInvDiagForm -

hmlgInvDiagForm :: Galoisian r => Homological r h -> Any n
  -> ConsecutiveZero To n (Matrix r) -> Inv (ConsecutiveZeroHom To n (Matrix r))
hmlgInvDiagForm h = invCnzNormalFormTo (hmlgMonic h) (hmlgDiagonalizable h)

--------------------------------------------------------------------------------
-- hmlgDiagForm -

hmlgDiagForm :: (Galoisian r, Attestable n)
  => Homological r h -> ConsecutiveZero To n (Matrix r) -> ConsecutiveZero To n (Matrix r)
hmlgDiagForm h = end . invFst . hmlgInvDiagForm h attest

--------------------------------------------------------------------------------
-- hmlgDiagFormHom -

hmlgDiagFormHom :: (Galoisian r, Attestable n)
  => Homological r h -> ConsecutiveZeroHom To n (Matrix r) -> ConsecutiveZeroHom To n (Matrix r)
hmlgDiagFormHom h ch = j * ch * i' where
  n        = attest
  Inv _ i' = hmlgInvDiagForm h n (start ch)
  Inv j _  = hmlgInvDiagForm h n (end ch)

--------------------------------------------------------------------------------
-- hmlgKernels -

hmlgKernels :: Homological r h -> KernelsSomeFreeFreeTip h
hmlgKernels HmlgZ = abhKernelsSomeFreeFreeTip

--------------------------------------------------------------------------------
-- hmlgCokernels -

hmlgCokernels :: Homological r h -> CokernelsG ConeLiftable SomeFreeSliceDiagram N1 h
hmlgCokernels HmlgZ = abhCokernelsLiftableSomeFree

--------------------------------------------------------------------------------
-- Homology -

type Homology = VarianceFreeLiftable To

--------------------------------------------------------------------------------
-- homology -

homologyStruct :: Struct Dst h -> Homological r h -> ConsecutiveZeroFree To n h -> Homology n h
homologyStruct Struct h = varianceFreeTo (hmlgKernels h) (hmlgCokernels h)

homology :: Homological r h -> ConsecutiveZeroFree To n h -> Homology n h
homology h = homologyStruct (hmlgDst h) h

--------------------------------------------------------------------------------
-- Betti -

type Betti n = Deviation (n+1)

--------------------------------------------------------------------------------
-- betti -

-- | the homology groups.
betti :: (Attestable n, Distributive h) => Homology n h -> Betti n h
betti = deviationsTo

--------------------------------------------------------------------------------
-- hmlgFreeZ -

hmlgFreeZ :: ConsecutiveZero To n (Matrix Z) -> ConsecutiveZeroFree To n AbHom
hmlgFreeZ ds = ConsecutiveZeroFree ds' fs where
  ds' = cnzMapCov (homDisjOpDst FreeAbHom) ds
  fs  = amap1 (fromJust . abgSomeFree) $ tail $ dgPoints $ cnzDiagram ds'

--------------------------------------------------------------------------------
-- hmlgFree -

hmlgFree :: Homological r h -> ConsecutiveZero To n (Matrix r) -> ConsecutiveZeroFree To n h
hmlgFree HmlgZ = hmlgFreeZ

--------------------------------------------------------------------------------
-- HomologyHom -

type HomologyHom = VarianceFreeLiftableHom To

--------------------------------------------------------------------------------
-- homologyHom -

homologyHom :: Homological r h -> ConsecutiveZeroFreeHom To n h -> HomologyHom n h
homologyHom h (ConsecutiveZeroFreeHom a b fs) = VarianceHomG a' b' fs where
  a' = homology h a
  b' = homology h b

--------------------------------------------------------------------------------
-- BettiHom -

type BettiHom n = DeviationHom (n+1)

--------------------------------------------------------------------------------
-- bettiHom -

bettiHom :: (Distributive h, SlicedFree h, Attestable n)
  => HomologyHom n h -> BettiHom n h
bettiHom h = deviationHomG (sld h) h where
  sld :: (Distributive h, SlicedFree h) => p h -> Struct (Dst,SldFr) h
  sld _ = Struct


--------------------------------------------------------------------------------
-- hmlgFreeHomZ -

hmlgFreeHomZ :: Attestable n
  => ConsecutiveZeroHom To n (Matrix Z) -> ConsecutiveZeroFreeHom To n AbHom
hmlgFreeHomZ h = ConsecutiveZeroFreeHom a' b' fs' where
  a'  = hmlgFreeZ $ start h
  b'  = hmlgFreeZ $ end h
  fs' = amap1 (amap FreeAbHom) $ cnzHomArrows h

--------------------------------------------------------------------------------
-- hmlgFreeHom -

hmlgFreeHom :: Attestable n
  => Homological r h -> ConsecutiveZeroHom To n (Matrix r) -> ConsecutiveZeroFreeHom To n h
hmlgFreeHom HmlgZ = hmlgFreeHomZ

--------------------------------------------------------------------------------
-- HomologyHom -

data HomologyApp r h n x y where
  HD :: (Galoisian r, Attestable n)
    => Homological r h
    -> HomologyApp r h n (ConsecutiveZeroHom To n (Matrix r)) (ConsecutiveZeroHom To n (Matrix r))
  HF :: (Galoisian r, Attestable n)
    => Homological r h
    -> HomologyApp r h n (ConsecutiveZeroHom To n (Matrix r)) (ConsecutiveZeroFreeHom To n h)
  H :: (Distributive h, Attestable n)
    => Homological r h
    -> HomologyApp r h n (ConsecutiveZeroFreeHom To n h) (HomologyHom n h)
  B :: (Attestable n)
    => Homological r h
    -> HomologyApp r h n (HomologyHom n h) (BettiHom n h)

instance Morphism (HomologyApp r h n) where
  type ObjectClass (HomologyApp r h n) = Dst
  domain (HD _) = Struct
  domain (HF _) = Struct
  domain (H _)  = Struct
  -- domain (B _)  = Struct


{-
--------------------------------------------------------------------------------
-- ccxCnzFreeAbl -

ccxCnzFreeAbl :: ChainComplex Z n -> ConsecutiveZeroFree To n AbHom
ccxCnzFreeAbl = cnzFreeAbl . ccxConsecutiveZero where
  
--------------------------------------------------------------------------------
-- cnzFreeAblHomology -

cnzFreeAblHomology :: ConsecutiveZeroFree To n AbHom -> Homology n
cnzFreeAblHomology = varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree

--------------------------------------------------------------------------------
-- HomologyHom -

-- | homomorphism between homologies.
type HomologyHom n = HomologyHomG n AbHom

--------------------------------------------------------------------------------
-- ccxCnzFreeHomAbl -

ccxCnzFreeHomAbl :: ChainComplexHom Z n -> ConsecutiveZeroFreeHom To n AbHom
ccxCnzFreeHomAbl h = ConsecutiveZeroFreeHom a' b' fs' where
  ConsecutiveZeroHom (DiagramTrafo a b fs) = ccxConsecutiveZeroHom h
  a'  = cnzFreeAbl $ (ConsecutiveZero a)
  b'  = cnzFreeAbl $ (ConsecutiveZero b)
  fs' = amap1 (amap FreeAbHom) fs

--------------------------------------------------------------------------------
-- cnzfhHomologyHom -

cnzFreeHomAblHomologyHom :: ConsecutiveZeroFreeHom To n AbHom -> HomologyHom n
cnzFreeHomAblHomologyHom (ConsecutiveZeroFreeHom a b fs) = VarianceHomG a' b' fs where
  a' = cnzFreeAblHomology a
  b' = cnzFreeAblHomology b


cnzFreeHomHomologyHom :: Homological h => ConsecutiveZeroFreeHom To n h -> HomologyHomG n h
cnzFreeHomHomologyHom (ConsecutiveZeroFreeHom a b fs) = VarianceHomG a' b' fs where
  a' = homologyG a
  b' = homologyG b
  
--------------------------------------------------------------------------------
-- homologyHom -

-- | the induced homomorphism between homologies.
homologyHom :: ChainComplexHom Z n -> HomologyHom n
homologyHom = cnzFreeHomAblHomologyHom . ccxCnzFreeHomAbl

--------------------------------------------------------------------------------
-- hmgGroupsHom -

-- | homomorphism between the homology groups.
homologyGroupsHom :: Attestable n => HomologyHom n -> DeviationHom (n+1) AbHom
homologyGroupsHom = deviationHomG (Struct :: Struct (Dst,SldFr) AbHom)

ff :: (Distributive h, SlicedFree h) => HomologyHomG n h -> Struct (Dst,SldFr) h
ff _ = Struct
{-
hhg :: (Attestable n, Distributive h) => HomologyHomG n h -> DeviationHom (n+1) h
hhg h = deviationHomG (ff h) h
-}
--------------------------------------------------------------------------------
-- hmgCycles -

-- | list of cycles generating the sub group of cycles for the head homology.  
hmgCycles :: Homology n -> [AbElement]
hmgCycles (VarianceG _ ((ker,_):|_)) = case universalCone ker of
  ConicFreeTip _ cn -> amap1 (k*>) $ abges $ start k where k = kernelFactor cn

--------------------------------------------------------------------------------
-- hmgClassGenerators -

-- | list of cycles genrating the homology group for the head homology.
hmgClassGenerators :: Homology n -> [AbElement]
hmgClassGenerators (VarianceG _ ((ker,coker):|_))
  = case finitePresentation abgFinPres (tip $ cone cCn) of
      GeneratorTo (DiagramChainTo _ (g:|_)) k'@(Free a) _ _ _ _
        -> toList $ amap1 AbElement $ split abhSplitable $ (k*>)
         $ lift (liftFree cLft a) (SliceFrom k' g)
  where
    ConeCokernelLiftable cCn cLft = universalCone coker
    k = kernelFactor $ universalCone ker

--------------------------------------------------------------------------------
-- hmgBoundaryOperator -

-- | the boundary operators of the head homology.
hmgBoundaryOperator :: Homology n -> ConsecutiveZero To N0 AbHom
hmgBoundaryOperator (VarianceG cs _) = cnzHead cs

--------------------------------------------------------------------------------
-- hmgChain -

-- | the abelian group of chains for the head homology.
hmgChain :: Homology n -> AbGroup
hmgChain (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) _) = start d

--------------------------------------------------------------------------------
-- homologyClass -

-- | the homology class of a cycle in the head homology.
homologyClass :: Homology n -> AbElement -> Eval AbElement
homologyClass (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) ((ker,coker):|_)) e
  | start d /= end e      = failure $ NotEligible "homologyClass"
  | not (isZero (d *> e)) = failure $ NotCycle "homologyClass"
  | otherwise = return (c *> e')

  where
    AbElement (SliceFrom k1 eh) = e
    c   = cokernelFactor $ universalCone coker
    eh' = universalFactor ker (ConeKernel (universalDiagram ker) eh)
    e'  = AbElement (SliceFrom k1 eh')

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary of an abelian element.
boundary :: Homology n -> AbElement -> Eval AbElement
boundary (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) _) e
  | start d /= end e  = failure $ NotEligible "boundary"
  | otherwise         = return (d *> e)

--------------------------------------------------------------------------------
-- boundaryInv -

-- | determines the bounary of a given cycle with zero homology class.
boundaryInv :: Homology n -> AbElement -> Eval AbElement
boundaryInv hmg e = do
  h <- homologyClass hmg e
  case isZero h of
    True               -> case universalCone ker of
      ConicFreeTip k _ -> case abhLift (SliceTo k e'' :> SliceTo k d'') of
        Just e'''      -> return $ AbElement $ SliceFrom k1 $ slfFactor e'''
        Nothing        -> failure $ EvalFailure "implementation error!"
                          -- as h is zero, e' should be liftable!
    False -> failure $ NonZeroHomologyClass h

  where
    VarianceG (ConsecutiveZero (DiagramChainTo _ (_:|d':|_))) ((ker,_):|_) = hmg
    AbElement e'   = e
    SliceFrom k1 _ = e'

    e'' = universalFactor ker (ConeKernel (universalDiagram ker) (slice e'))
    d'' = universalFactor ker (ConeKernel (universalDiagram ker) d')

    
-}
