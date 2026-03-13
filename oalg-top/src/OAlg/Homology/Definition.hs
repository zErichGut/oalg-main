
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}


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

    -- * Homological
    Homological(..), hmlgDst, hmlgMonic, hmlgDiagonalizable
  , hmlgKernels, hmlgCokernels

    -- * HomologyApp
  , HomologyApp(..)
  
    -- * Homology
  , homology, Homology    
  , betti, Betti
  
    -- * Homomorphism
  , homologyHom, HomologyHom
  , bettiHom, BettiHom

  ) where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Distributive
import OAlg.Structure.Ring

import OAlg.Entity.Diagram as D 
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Slice
import OAlg.Entity.Matrix

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.FibredOriented
import OAlg.Hom.Additive
import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels
import OAlg.AbelianGroup.Free.SmithNormalForm

import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.Free

import OAlg.LinearAlgebra.ConsecutiveZero
import OAlg.LinearAlgebra.StepMatrix



import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits

import OAlg.Data.Singleton
import OAlg.Structure.Exponential

--------------------------------------------------------------------------------
-- limesCone -

-- | the underlying concrete limes.
limesCone :: Conic c => LimesG c s p d t n m x -> LimesG Cone s p d t n m x
limesCone (LimesProjective c u) = LimesProjective (cone c) u
limesCone (LimesInjective c u)  = LimesInjective (cone c) u

--------------------------------------------------------------------------------
-- Matrix - Sliced (Free k) -

instance (Ring x, Attestable k) => Sliced (Free k) (Matrix x) where
  slicePoint (Free k) = dim unit ^ lengthN k
  
--------------------------------------------------------------------------------
-- fldKernelsSomeFreeFreeTip -

fldKernelSomeFreeFreeTip :: Field x
  => KernelDiagrammatic SomeFreeSliceDiagram N1 (Matrix x)
  -> KernelSomeFreeFreeTip (Matrix x)
fldKernelSomeFreeFreeTip = error "nyi"


fldKernelsSomeFreeFreeTip :: Field x => KernelsSomeFreeFreeTip (Matrix x)
fldKernelsSomeFreeFreeTip = LimitsG fldKernelSomeFreeFreeTip


--------------------------------------------------------------------------------
-- fldCokernelsLiftableSomeFree -

fldCokernelsLiftableSomeFree :: Field x => CokernelsG ConeLiftable SomeFreeSliceDiagram N1 (Matrix x)
fldCokernelsLiftableSomeFree = error "nyi"






--------------------------------------------------------------------------------
-- Homological -

-- | homological relation between a @'Galoisian' __r__@ and a @'Distributive' __h__@.
data Homological r h where
  HmlgZ :: Homological Z AbHom
  HmlgF :: Field x => Homological x (Matrix x)

hmlgDst :: Homological r h -> Struct Dst h
hmlgDst HmlgZ = Struct
hmlgDst HmlgF = Struct

--------------------------------------------------------------------------------
-- hmlgMonic -

hmlgMonic :: Homological r h -> Monic r
hmlgMonic HmlgZ = mncZ
hmlgMonic HmlgF = mncField

--------------------------------------------------------------------------------
-- hmlgDiagonalizable -

hmlgDiagonalizable :: Homological r h -> Diagonalizable r
hmlgDiagonalizable HmlgZ = dgzZ
hmlgDiagonalizable HmlgF = dgzField


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
hmlgKernels HmlgF = fldKernelsSomeFreeFreeTip

--------------------------------------------------------------------------------
-- hmlgCokernels -

hmlgCokernels :: Homological r h -> CokernelsG ConeLiftable SomeFreeSliceDiagram N1 h
hmlgCokernels HmlgZ = abhCokernelsLiftableSomeFree
hmlgCokernels HmlgF = fldCokernelsLiftableSomeFree

--------------------------------------------------------------------------------
-- Homology -

type Homology = VarianceFreeLiftable To

--------------------------------------------------------------------------------
-- homology -

homologyStruct :: Struct Dst h -> Homological r h -> ConsecutiveZeroFree To n h -> Homology n h
homologyStruct Struct h = varianceFreeLiftableTo (hmlgKernels h) (hmlgCokernels h)

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
-- hmlgFreeRing -

hmlgFreeRing :: Ring x => ConsecutiveZero To n (Matrix x) -> ConsecutiveZeroFree To n (Matrix x)
hmlgFreeRing = error "nyi"

--------------------------------------------------------------------------------
-- hmlgFree -

hmlgFree :: Homological r h -> ConsecutiveZero To n (Matrix r) -> ConsecutiveZeroFree To n h
hmlgFree HmlgZ = hmlgFreeZ
hmlgFree HmlgF = hmlgFreeRing

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
-- hmlgFreeHomRing -

hmlgFreeHomRing :: Ring x
  => ConsecutiveZeroHom To n (Matrix x) -> ConsecutiveZeroFreeHom To n (Matrix x)
hmlgFreeHomRing = error "nyi"

--------------------------------------------------------------------------------
-- hmlgFreeHom -

hmlgFreeHom :: Attestable n
  => Homological r h -> ConsecutiveZeroHom To n (Matrix r) -> ConsecutiveZeroFreeHom To n h
hmlgFreeHom HmlgZ = hmlgFreeHomZ
hmlgFreeHom HmlgF = hmlgFreeHomRing

--------------------------------------------------------------------------------
-- HomologyApp -

data HomologyApp r h n x y where
  -- | diagonalization.
  D :: Homological r h
    -> HomologyApp r h n (ConsecutiveZeroHom To n (Matrix r)) (ConsecutiveZeroHom To n (Matrix r))

  -- | embedding to 'Free'.
  F :: Homological r h
    -> HomologyApp r h n (ConsecutiveZeroHom To n (Matrix r)) (ConsecutiveZeroFreeHom To n h)

  -- | Betti numbers.
  B :: Homological r h
    -> HomologyApp r h n (ConsecutiveZeroFreeHom To n h) (BettiHom n h)

instance (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => Morphism (HomologyApp r h n) where
  type ObjectClass (HomologyApp r h n) = Dst
  homomorphous (D _) = Struct :>: Struct
  homomorphous (F _) = Struct :>: Struct
  homomorphous (B _) = Struct :>: Struct

instance (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => ApplicativeG Id (HomologyApp r h n) (->) where
  amapG (D h) = toIdG (hmlgDiagFormHom h)
  amapG (F h) = toIdG (hmlgFreeHom h)
  amapG (B h) = toIdG (bettiHom . homologyHom h)

instance (Galoisian r, Distributive h, Attestable n)
  => ApplicativeG Pnt (HomologyApp r h n) (->) where
  amapG (D h) = toPntG (hmlgDiagForm h)
  amapG (F h) = toPntG (hmlgFree h)
  amapG (B h) = toPntG (betti . homology h)

instance (Galoisian r, Distributive h, Attestable n)
  => ApplicativeG Rt (HomologyApp r h n) (->) where
  amapG h@(D _) = amapRt (omap h)
  amapG h@(F _) = amapRt (omap h)
  amapG h@(B _) = amapRt (omap h)

instance (Galoisian r, SlicedFree h, Distributive h, Attestable n) => HomOriented (HomologyApp r h n)
instance (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => HomMultiplicative (HomologyApp r h n)
instance (Galoisian r, SlicedFree h, Distributive h, Attestable n) => HomFibred (HomologyApp r h n)
instance (Galoisian r, SlicedFree h, Distributive h, Attestable n) => HomAdditive (HomologyApp r h n)
instance (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => HomFibredOriented (HomologyApp r h n)
instance (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => HomDistributive (HomologyApp r h n)






{-
--------------------------------------------------------------------------------
-- ccxCnzFreeAbl -

ccxCnzFreeAbl :: ChainComplex Z n -> ConsecutiveZeroFree To n AbHom
ccxCnzFreeAbl = cnzFreeAbl . ccxConsecutiveZero where
  
--------------------------------------------------------------------------------
-- cnzFreeAblHomology -

cnzFreeAblHomology :: ConsecutiveZeroFree To n AbHom -> Homology n
cnzFreeAblHomology = varianceFreeLiftableTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree

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
