
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

  -- , Mod(..)
  , F2(..)

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


import Control.Monad

import OAlg.Control.Solver
import OAlg.Category.SDuality

import OAlg.Data.Singleton
import OAlg.Data.Canonical
import OAlg.Data.Either
import OAlg.Data.Constructable

import OAlg.Entity.Slice.Liftable

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits

import OAlg.Structure.Exception
import OAlg.Structure.Additive
import OAlg.Structure.FibredOriented
import OAlg.Structure.Operational
import OAlg.Structure.Exponential
import OAlg.Structure.Number
import OAlg.Structure.Vectorial
import OAlg.Structure.Algebraic

import OAlg.LinearAlgebra.KernelsAndCokernels
import OAlg.AbelianGroup.Euclid

import GHC.TypeLits hiding (type (+),Mod)

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
-- cokernelFactorEpi -

-- | the epimorph factor of its universal shell.
cokernelFactorEpi :: Cokernel n x -> FactorM Epimorph x
cokernelFactorEpi = Epi . cokernelFactor . universalCone

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
-- rngSomeFree -

-- | the dimension of a matrix over a ring as a free point.
rngSomeFree :: Ring x => Dim' x -> SomeFree (Matrix x)
rngSomeFree n = case someNatural $ lengthN n of
    SomeNatural n' -> SomeFree $ Free n'


instance Field x => SlicedFree (Matrix x) where
  slicedFree = Struct
  
--------------------------------------------------------------------------------
-- Morphology -

-- | morphology of a 'FactorM', i.e. either mono- or epimorph
data Morphology = Monomorph | Epimorph deriving (Show,Read,Ord,Eq,Enum,Bounded)

type instance Dual Monomorph = Epimorph
type instance Dual Epimorph  = Monomorph

instance Validable Morphology where
  valid Monomorph = SValid
  valid _         = SValid

--------------------------------------------------------------------------------
-- FactorM -

-- | mono- and epimorphic arrows within a 'Multiplicative' structure.
--
-- __Property__ Let @m@ be in @'FactorM' __m x__@ where @__x__@ is a 'Multiplicative'
-- structure, then holds:
--
-- (1) If @m@ matches @'Mono' i@ for some @i@ in @__x__@ then holds:
-- For all parrallel @f@, @g@ in @__x__@ - i.e. @'orientation' f '==' 'orientation' g@ - with
-- @'end' f '==' 'start' i@ and @i '*' f '==' i '*' g@ follows that @f '==' g@.
--
-- (2) If @m@ matches @'Epi' p@ for some @p@ in @__x__@ then holds:
-- For all parrallel @f@, @g@ in @__x__@ - i.e. @'orientation' f '==' 'orientation' g@ - with
-- @'start' f '==' 'end' p@ and @f '*' p '==' g '*' p@ follows that @f '==' g@.
data FactorM m x where
  Mono :: x -> FactorM Monomorph x
  Epi  :: x -> FactorM Epimorph x

deriving instance Show x => Show (FactorM m x)
deriving instance Eq x => Eq (FactorM m x)
deriving instance Ord x => Ord (FactorM m x)

--------------------------------------------------------------------------------
-- fcmMapCov -

-- | covariant mapping of a 'FactorM'.
--
-- __Note__ We use isomorphisms to preserve monomorphic factors.
fcmMapCov :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h)
  => Variant2 Covariant (Inv2 h) x y -> FactorM m x -> FactorM m y
fcmMapCov (Covariant2 i) (Mono x) = Mono $ amap i x
fcmMapCov (Covariant2 i) (Epi x)  = Epi $ amap i x

--------------------------------------------------------------------------------
-- fcmMapCnt -

-- | contravariant mapping of a 'FactorM'.
--
-- __Note__ We use isomorphisms for mappings between  mono- and epimorphic factors.
fcmMapCnt :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h)
  => Variant2 Contravariant (Inv2 h) x y -> FactorM m x -> FactorM (Dual m) y
fcmMapCnt (Contravariant2 i) (Mono x) = Epi $ amap i x
fcmMapCnt (Contravariant2 i) (Epi x)  = Mono $ amap i x

--------------------------------------------------------------------------------
-- fcmMapS -

type instance Dual1 (FactorM m) = FactorM (Dual m)

-- | mapping of 'FactorM'.
fcmMapS :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => Inv2 h x y -> SDualBi (FactorM m) x -> SDualBi (FactorM m) y
fcmMapS = vmapBi fcmMapCov fcmMapCov fcmMapCnt fcmMapCnt

instance (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => ApplicativeG (SDualBi (FactorM m)) (Inv2 h) (->) where
  amapG = fcmMapS

instance (CategoryDisjunctive h, Functorial h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => FunctorialG (SDualBi (FactorM m)) (Inv2 h) (->)
  
--------------------------------------------------------------------------------
-- FactorMDiagram -

-- | diagram for validating 'FactorM'.
--
-- __Property__ Let @d@ be in @'FactorMDiagram' __m x__@ where @__x__@ is a 'Multiplicative' structure,
-- then holds:
--
--  (1) If @d@ matches @'FactorMDiagram' ('Mono' i) (f,g)@, then holds:
--
--      (1) @'orientation' f '==' 'orientation' g@.
--
--      (2) @'end' f '==' 'start' i@.
--
--  (2) If @d@ matches @'FactorMDiagram' ('Epi' i) (f,g)@, then holds:
--
--      (1) @'orientation' f '==' 'orientation' g@.
--
--      (2) @'start' f '==' 'end' i@.
data FactorMDiagram m x = FactorMDiagram (FactorM m x) (x,x) deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- mapping -

-- | covariant mapping of a 'FactorMDiagram'.
fmdMapCov :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => Variant2 Covariant (Inv2 h) x y -> FactorMDiagram m x -> FactorMDiagram m y
fmdMapCov (Covariant2 h) (FactorMDiagram i (f,g)) = FactorMDiagram i' (f',g') where
  SDualBi (Right1 i') = amapF h (SDualBi (Right1 i))
  f'                  = amap h f
  g'                  = amap h g

-- | contravariant mapping of a 'FactorMDiagram'.
fmdMapCnt :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => Variant2 Contravariant (Inv2 h) x y -> FactorMDiagram m x -> FactorMDiagram (Dual m) y
fmdMapCnt (Contravariant2 h) (FactorMDiagram i (f,g)) = FactorMDiagram i' (f',g') where
  SDualBi (Left1 i')  = amapF h (SDualBi (Right1 i))
  f'                  = amap h f
  g'                  = amap h g

type instance Dual1 (FactorMDiagram m) = FactorMDiagram (Dual m)

-- | mapping of a 'FactorMDiagram'.
fmdMapS :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => Inv2 h x y -> SDualBi (FactorMDiagram m) x -> SDualBi (FactorMDiagram m) y
fmdMapS = vmapBi fmdMapCov fmdMapCov fmdMapCnt fmdMapCnt

instance (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => ApplicativeG (SDualBi (FactorMDiagram m)) (Inv2 h) (->) where
  amapG = fmdMapS
  
instance (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => FunctorialG (SDualBi (FactorMDiagram m)) (Inv2 h) (->)

--------------------------------------------------------------------------------
-- xoFactorMDiagram -

xoFactorMDiagram :: Multiplicative x => XOrtOrientation x -> FactorM m x -> X (FactorMDiagram m x)
xoFactorMDiagram xo m@(Mono i) = do
  s <- xoPoint xo
  f <- xoArrow xo (s :> end i)
  g <- xoArrow xo (s :> end i)
  return (FactorMDiagram m (f,g))
xoFactorMDiagram xo m@(Epi _)
  = amap1 (fmdMapCnt $ Contravariant2 $ inv2 i) $ xoFactorMDiagram xo' m' where
  
    xo'                = coXOrtOrientation xo
    Contravariant2 i   = toDualOpMlt
    SDualBi (Left1 m') = amapF i (SDualBi (Right1 m))
  
--------------------------------------------------------------------------------
-- relFactroMDiagram -

relFactorMDiagram :: Multiplicative x => FactorMDiagram m x -> Statement
relFactorMDiagram (FactorMDiagram (Mono i) (f,g))
  = And [ Label "1.1" :<=>: (orientation f == orientation g) :?> Params ["(f,g)":=show (f,g)]
        , Label "1,2" :<=>: (start i == end f) :?> Params ["(i,f)":=show (i,f)]
        ]
relFactorMDiagram d@(FactorMDiagram (Epi _) _) = relFactorMDiagram d' where
  Contravariant2 i   = toDualOpMlt 
  SDualBi (Left1 d') = amapF i (SDualBi (Right1 d))

  
--------------------------------------------------------------------------------
-- relFactorM -

-- | validating a 'FactorM'.
relFactorM :: Multiplicative x => FactorMDiagram m x -> Statement
relFactorM (FactorMDiagram (Mono i) (f,g))
  = ((f /= g) :?> Params []) :=> (i * f /= i * g) :?> Params ["(f,g)":=show (f,g)]
  -- we use this condition to avoid a lot of denied permisses!
relFactorM fd@(FactorMDiagram (Epi _) _) = relFactorM fd' where
  Contravariant2 i    = toDualOpMlt 
  SDualBi (Left1 fd') = amapF i (SDualBi (Right1 fd))

instance (Multiplicative x, XStandardOrtOrientation x) => Validable (FactorM m x) where
  valid m = Label "FactorM" :<=>: Forall (xD m) relFactorM where
    xD = xoFactorMDiagram xStandardOrtOrientation


{-
--------------------------------------------------------------------------------
-- Mod -

newtype Mod (n :: Nat) = Mod Z deriving Show

mdzBase :: KnownNat n => Mod n -> N
mdzBase m@(Mod _) = prj $ natVal m

mdzRdc :: KnownNat n => Mod n -> Mod n
mdzRdc m@(Mod n) = Mod (mod0 n (mdzBase m))

instance Exposable (Mod n) where
  type Form (Mod n) = Z
  form (Mod n) = n

instance KnownNat n => Constructable (Mod n) where
  make n = mdzRdc (Mod n) 


instance KnownNat n => Eq (Mod n) where
  a == b = a' == b' where
    Mod a' = mdzRdc a
    Mod b' = mdzRdc b

instance Validable (Mod n) where
  valid (Mod n) = valid n

type instance Point (Mod n) = ()
instance ShowPoint (Mod n)
instance EqPoint (Mod n)
instance SingletonPoint (Mod n)
instance ValidablePoint (Mod n)
instance TypeablePoint (Mod n)

instance KnownNat n => Oriented (Mod n) where
  orientation = const (():>())

instance KnownNat n => Multiplicative (Mod n) where
  one _ = make 1
  Mod a * Mod b = make (a*b)
  npower (Mod a) n = make $ npower a n

instance KnownNat n => Commutative (Mod n)

instance KnownNat n => Invertible (Mod n) where
  tryToInvert m@(Mod a) | g == 1    = return (make s)
                         | otherwise = failure NotInvertible 
    where (g,s,_) = euclid a (inj $ mdzBase m)

type instance Root (Mod n) = Orientation ()
instance ShowRoot (Mod n)
instance EqRoot (Mod n)
instance ValidableRoot (Mod n)
instance TypeableRoot (Mod n)

instance KnownNat n => Fibred (Mod n)

instance KnownNat n => Additive (Mod n) where
  zero _ = make 0
  Mod a + Mod b = make (a+b)
  ntimes n (Mod a) = make $ ntimes n a

instance KnownNat n => Abelian (Mod n) where
  negate (Mod a) = make (negate a)
  Mod a - Mod b = make (a-b)
  ztimes z (Mod a) = make $ ztimes z a

instance KnownNat n => FibredOriented (Mod n)
instance KnownNat n => Distributive (Mod n)
instance KnownNat n => Vectorial (Mod n) where
  type Scalar (Mod n) = Z
  (!) = ztimes
instance KnownNat n => Algebraic (Mod n)

instance Field (Mod 2) where a / b = a * invert b
-}
--------------------------------------------------------------------------------
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
hmlgKernels HmlgF = rngKernelsSomeFreeFreeTip mtxKernels

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
hmlgFreeRing c@(ConsecutiveZero d) = ConsecutiveZeroFree c sf where
  sf = amap1 rngSomeFree $ tail $ dgPoints d

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

hmlgFreeHomRing :: (Attestable n, Ring x)
  => ConsecutiveZeroHom To n (Matrix x) -> ConsecutiveZeroFreeHom To n (Matrix x)
hmlgFreeHomRing h = ConsecutiveZeroFreeHom a' b' fs where
  a' = hmlgFreeRing $ start h
  b' = hmlgFreeRing $ end h
  fs = cnzHomArrows h

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
