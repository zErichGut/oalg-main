
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}


-- |
-- Module      : OAlg.Topology.Definition
-- Description : definition of topological spaces.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Definition of topological spaces.
module OAlg.Topology.Definition
  (

    -- * Space
    Space(..), Model(..), eqVertexType
  , spcAbstract, dimension, skeleton, border
  , spcChainComplexSet, spcChainComplexSetZ

    -- * Continuous
  , Continuous(..)
  , cntDomain, cntRange
  , cntAbstract

    -- * Homology
  , hC, hC', hN, hZ, hD, hF, hB
  , Homological(..)
  , HCat

  ) where


import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Exception
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Ring

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Slice
import OAlg.Entity.Matrix

import OAlg.Limes.Exact.Free
import OAlg.Limes.Exact.ConsecutiveZero

import OAlg.Homology.Simplical hiding (dimension)
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Definition

--------------------------------------------------------------------------------
-- Model -

data Model = Concrete | Abstract deriving (Show,Read,Eq,Ord,Enum,Bounded)

--------------------------------------------------------------------------------
-- Space -

-- | topological space given by a 'Complex' over some vertex set @__x__@.
data Space m where
  SpaceAbstract :: (Entity x, Ord x) => Complex x -> Space Abstract
  SpaceConcrete :: Complex (Vector Q)             -> Space Concrete
  
deriving instance Show (Space m)

eqVertexType :: (Typeable x, Typeable y) => c x -> c y -> Maybe (x :~: y)
eqVertexType _ _ = eqT

instance Eq (Space m) where
  SpaceAbstract c == SpaceAbstract c' = case eqVertexType c c' of
    Just Refl -> c == c'
    Nothing   -> False
  SpaceConcrete c == SpaceConcrete c' = c == c'

instance Validable (Space m) where
  valid (SpaceAbstract c) = Label "SpaceAbstract" :<=>: valid c
  valid (SpaceConcrete c) = Label "SpaceConcrete" :<=>: valid c 

--------------------------------------------------------------------------------
-- spcAbstract -

-- | abstraction of a space.
spcAbstract :: Space m -> Space Abstract
spcAbstract x@(SpaceAbstract _) = x
spcAbstract (SpaceConcrete c)   = SpaceAbstract c

--------------------------------------------------------------------------------
-- dimension -

-- | the dimenson of a space @c@, i.e. the dimenson of its underlying complex.
dimension :: Space m -> Z
dimension (SpaceAbstract cpx) = cpxDim cpx
dimension c                   = dimension $ spcAbstract c

--------------------------------------------------------------------------------
-- border -

border :: Space m -> Space m
border c = skeleton (pred $ dimension c) c

--------------------------------------------------------------------------------
-- skeleton -

-- | the @p@-skeleton of a space @c@, i.e. the sub space of @c@ consisting of all simplices with
--- dimension less or equal to @p@.
skeleton :: Z -> Space m -> Space m
skeleton p c = case c of
  SpaceAbstract cpx -> SpaceAbstract $ cpxSkeleton p cpx 
  SpaceConcrete cpx -> SpaceConcrete $ cpxSkeleton p cpx

--------------------------------------------------------------------------------
-- spcChainComplexSet -

spcChainComplexSet :: (Ring r, Commutative r)
  => ChainComplexType -> SimplexType s -> Any n -> Space m -> ChainComplexHom r n
spcChainComplexSet t s n (SpaceAbstract c) = chainComplexSet t s n c
spcChainComplexSet t s n x = spcChainComplexSet t s n (spcAbstract x)

spcChainComplexSetZ ::  ChainComplexType -> SimplexType s -> Any n -> Space m -> ChainComplexHom Z n
spcChainComplexSetZ = spcChainComplexSet

--------------------------------------------------------------------------------
-- Continuous -

-- | mapping between two spaces.
data Continuous s m where
  CntAbstract :: ComplexMap s (Complex x) (Complex y) -> Continuous s Abstract
  CntConcrete :: ComplexMap s (Complex (Vector Q)) (Complex (Vector Q)) -> Continuous s Concrete

deriving instance Show (Continuous s m)

cntEqAbstr :: Homomorphous EntOrd x y -> Homomorphous EntOrd x' y'
  -> ComplexMap s (Complex x) (Complex y) -> ComplexMap s (Complex x') (Complex y')
  -> Bool
cntEqAbstr (Struct :>: Struct) (Struct :>: Struct) f g
  = case (eqVertexType (cpmDomain f) (cpmDomain g), eqVertexType (cpmRange f) (cpmRange g)) of
      (Just Refl,Just Refl) -> f == g
      _                     -> False

instance Eq (Continuous s m) where
  CntAbstract f == CntAbstract g = cntEqAbstr (cpmHomEntOrd f) (cpmHomEntOrd g) f g
  CntConcrete f == CntConcrete g = f == g

instance Validable (Continuous s m) where
  valid f = Label "Continous" :<=>: case f of
    CntAbstract f' -> Label "Abstract" :<=>: valid f'
    CntConcrete f' -> Label "Concrete" :<=>: valid f'

--------------------------------------------------------------------------------
-- cntAbstract -

-- | abstraction of a continuous map.
cntAbstract :: Continuous s m -> Continuous s Abstract
cntAbstract f@(CntAbstract _ ) = f
cntAbstract (CntConcrete f)    = CntAbstract f

--------------------------------------------------------------------------------
-- cntDomain -

cntDomain :: Continuous s m -> Space m
cntDomain (CntAbstract f) = case cpmHomEntOrd f of Struct :>: _ -> SpaceAbstract (cpmDomain f)
cntDomain (CntConcrete f) = SpaceConcrete (cpmDomain f)

--------------------------------------------------------------------------------
-- contRange -

cntRange :: Continuous s m -> Space m
cntRange (CntAbstract f) = case cpmHomEntOrd f of _ :>: Struct -> SpaceAbstract (cpmRange f)
cntRange (CntConcrete f) = SpaceConcrete (cpmRange f)

--------------------------------------------------------------------------------
-- Continuous - Multiplicative -

type instance Point (Continuous s m) = Space m

deriving instance ShowPoint (Continuous s m)
deriving instance EqPoint (Continuous s m)
deriving instance ValidablePoint (Continuous s m)
deriving instance Typeable m => TypeablePoint (Continuous s m)

instance (Typeable s, Typeable m) => Oriented (Continuous s m) where
  start = cntDomain
  end   = cntRange

instance (AttestableSimplexType s, Typeable m) => Multiplicative (Continuous s m) where
  one (SpaceAbstract c) = CntAbstract (cpmOne Struct simplexType c) 
  one (SpaceConcrete c) = CntConcrete (cpmOne Struct simplexType c)

  CntConcrete f * CntConcrete g        = CntConcrete (cpmMlt f g)  
  CntAbstract f * CntAbstract g        = case (cpmHomEntOrd f,cpmHomEntOrd g) of
    (Struct:>:Struct,Struct:>:Struct) -> case eqVertexType (cpmRange g) (cpmDomain f) of
      Just Refl                       -> CntAbstract (cpmMlt f g)
      Nothing                         -> throw NotMultiplicable


--------------------------------------------------------------------------------
-- Hmlg -

data Hmlg n x y where
  ChC  :: (Ring r, Commutative r, AttestableSimplexType s, Typeable m)
       => ChainComplexType -> Any n -> Hmlg n (Continuous s m) (ChainComplexHom r n)
  Crd  :: Ring r => Hmlg n (ChainComplexHom r n) (CardsHom n)
  Cnz  :: Ring r => Hmlg n (ChainComplexHom r n) (ConsecutiveZeroHom To n (Matrix r))
  Hmlg :: (Galoisian r, SlicedFree h, Distributive h)
       => HomologyApp r h n x y -> Hmlg n x y

instance Attestable n => Morphism (Hmlg n) where
  type ObjectClass (Hmlg n) = Mlt
  homomorphous (ChC _ _) = Struct :>: Struct
  homomorphous Crd       = Struct :>: Struct
  homomorphous Cnz       = Struct :>: Struct
  homomorphous (Hmlg h)  = hmphMlt (homomorphous h) where
    hmphMlt :: Homomorphous Dst x y -> Homomorphous Mlt x y
    hmphMlt (Struct :>: Struct) = Struct :>: Struct
    
instance Attestable n => ApplicativeG Id (Hmlg n) (->) where
  amapG (ChC t n) (Id f) = Id $ case cntAbstract f of
    CntAbstract f'      -> case cpmHomEntOrd f' of
      Struct:>:Struct   -> chainComplexHom t n f'

  amapG Crd (Id c)       = Id $ ccxCardsHom c
  amapG Cnz (Id c)       = Id $ ccxConsecutiveZeroHom c
  amapG (Hmlg h) x       = amapG h x
  
instance Attestable n => ApplicativeG Pnt (Hmlg n) (->) where
  amapG h (Pnt x)    =  Pnt $ case homomorphous h of
    Struct:>:Struct -> start $ amap h (one x) 

instance Attestable n => HomOriented (Hmlg n)
instance Attestable n => HomMultiplicative (Hmlg n)


--------------------------------------------------------------------------------
-- HCat -

-- | category of homology operators.
type HCat n = Path (Hmlg n)

hC :: (Ring r, Commutative r, AttestableSimplexType s, Typeable m)
  => ChainComplexType -> Any n -> HCat n (Continuous s m) (ChainComplexHom r n)
hC t n = ChC t n :. IdPath Struct

hC' :: (Ring r, Commutative r, AttestableSimplexType s, Typeable m)
  => q s -> Homological r h
  -> ChainComplexType -> Any n -> HCat n (Continuous s m) (ChainComplexHom r n)
hC' _ _ = hC

hN :: (Ring r, Attestable n) => HCat n (ChainComplexHom r n) (CardsHom n)
hN = Crd :. IdPath Struct

hZ :: (Ring r, Attestable n) => HCat n (ChainComplexHom r n) (ConsecutiveZeroHom To n (Matrix r))
hZ = Cnz :. IdPath Struct

hD :: (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => Homological r h
  -> HCat n (ConsecutiveZeroHom To n (Matrix r)) (ConsecutiveZeroHom To n (Matrix r))
hD h = Hmlg (D h) :. IdPath Struct 

hF :: (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => Homological r h
  -> HCat n (ConsecutiveZeroHom To n (Matrix r)) (ConsecutiveZeroFreeHom To n h)
hF h = Hmlg (F h) :. IdPath Struct

hB :: (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => Homological r h
  -> HCat n (ConsecutiveZeroFreeHom To n h) (BettiHom n h)
hB h = Hmlg (B h) :. IdPath Struct


{-
hBetti :: (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => Homological r h -> HCat n (ChainComplexHom r n) (BettiHom n h)
hBetti h = error "nyi" -- Betti t :. IdPath Struct
-}
{-
--------------------------------------------------------------------------------
-- HomologyType -

data HomologyType r h where
  HmlgTypeZ :: HomologyType Z AbHom
  -- HmlgTypeF :: Field r => HomologyType r (Matrix r)

hmlg :: Attestable n
  => HomologyType r h -> ConsecutiveZeroHom To n (Matrix r) -> ConsecutiveZeroFreeHom To n h
hmlg HmlgTypeZ = cnzFreeHomAbl
-- hmlg HmlgTypeF = id

  
--------------------------------------------------------------------------------
-- Hmlg -

data Hmlg x y where
  ChC   :: (Ring r, Commutative r, AttestableSimplexType s, Typeable m, Attestable n)
        => ChainComplexType -> Any n -> Hmlg (Continuous s m) (ChainComplexHom r n)
  Crd   :: (Ring r, Attestable n) => Hmlg (ChainComplexHom r n) (CardsHom n)
  Betti :: (Ring r, Commutative r, Homological h, Attestable n)
        => HomologyType r h
        -> Hmlg (ChainComplexHom r n) (BettiHom n h)

instance Morphism Hmlg where
  type ObjectClass Hmlg = Mlt
  homomorphous (ChC _ _)    = Struct :>: Struct
  homomorphous Crd          = Struct :>: Struct
  homomorphous (Betti _)    = Struct :>: Struct

instance ApplicativeG Id Hmlg (->) where
  amapG (ChC t n) (Id f) = Id $ case cntAbstract f of
    CntAbstract f'      -> case cpmHomEntOrd f' of
      Struct:>:Struct   -> chainComplexHom t n f'

  amapG Crd (Id c)       = Id $ ccxCardsHom c
  
  amapG (Betti h) (Id c) = Id
                         $ bettiHom
                         $ homologyHom
                         $ hmlg h 
                         $ ccxConsecutiveZeroHom c

instance ApplicativeG Pnt Hmlg (->) where
  amapG h (Pnt x)    =  Pnt $ case homomorphous h of
    Struct:>:Struct -> start $ amap h (one x) 

instance HomOriented Hmlg
instance HomMultiplicative Hmlg

--------------------------------------------------------------------------------
-- HCat -

-- | category of homology operators.
type HCat = Path Hmlg

hChC :: (Ring r, Commutative r, AttestableSimplexType s, Typeable m, Attestable n)
  => ChainComplexType -> Any n -> HCat (Continuous s m) (ChainComplexHom r n)
hChC t n = ChC t n :. IdPath Struct

hChC' :: (Ring r, Commutative r, AttestableSimplexType s, Typeable m, Attestable n)
  => q s -> ChainComplexType -> Any n -> HCat (Continuous s m) (ChainComplexHom r n)
hChC' _ = hChC

hCrd :: (Ring r, Attestable n) => HCat (ChainComplexHom r n) (CardsHom n)
hCrd = Crd :. IdPath Struct

hBetti :: (Ring r, Commutative r, Homological h, Attestable n)
  => HomologyType r h -> HCat (ChainComplexHom r n) (BettiHom n h)
hBetti t = Betti t :. IdPath Struct

hZ :: (Attestable n, AttestableSimplexType s, Typeable m)
  => ChainComplexType -> Any n -> HCat (Continuous s m) (BettiHom n AbHom)
hZ t n = hBetti HmlgTypeZ . hChC t n -- Hmlg t HmlgTypeZ n :. IdPath Struct 

hZ' :: (Attestable n, AttestableSimplexType s, Typeable m)
  => q s -> ChainComplexType -> Any n -> HCat (Continuous s m) (BettiHom n AbHom)
hZ' _ = hZ
-}
