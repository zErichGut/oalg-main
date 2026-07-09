
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
    Space(..), eqVertexType
  , spcDim, spcSkeleton, spcBorder
  , spcChainComplexSet

    -- * Continuous
  , Continuous(..)
  , cntDomain, cntRange


    -- * Homology
  , hC, hC', hN, hZ, hD, hF, hB, hB'
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
-- Space -

-- | topological space given by a 'Complex', where the vertex type is ignored.
--
-- __Note__ Viewing a complex as a topological space ignores the concrete vertex type because
-- its type is not relay relevant and it gives rise to explore the algebraic properties by 'Continuous'
-- maps, which form a 'Multiplicative' structure where one can define new spaces by using the
-- frame work of limits.
data Space where
  Space :: (Entity x, Ord x) => Complex x -> Space

deriving instance Show Space

eqVertexType :: (Typeable x, Typeable y) => c x -> c y -> Maybe (x :~: y)
eqVertexType _ _ = eqT

instance Eq Space where
  Space c == Space c' = case eqVertexType c c' of
    Just Refl -> c == c'
    Nothing   -> False

instance Validable Space where
  valid (Space c) = Label "Space" :<=>: valid c

--------------------------------------------------------------------------------
-- spcDim -

spcDim :: Space -> Z
spcDim (Space c) = cpxDim c

--------------------------------------------------------------------------------
-- spcSkeleton -

-- | the @p@-skeleton of a space @c@, i.e. the sub space of @c@ consisting of all simplices with
--- dimension less or equal to @p@.
spcSkeleton :: Z -> Space -> Space
spcSkeleton p c = case c of
  Space cpx -> Space $ cpxSkeleton p cpx 

--------------------------------------------------------------------------------
-- spcBorder -

-- | the boder of a space, i,e, the @n '-' 1@-dimenional skeleton where @n@ denotes the dimension of
-- the given space.
spcBorder :: Space -> Space
spcBorder c = spcSkeleton (pred $ spcDim c) c

{-
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
-}


--------------------------------------------------------------------------------
-- spcChainComplexSet -

spcChainComplexSet :: (Ring r, Commutative r)
  => ChainComplexType -> SimplexType s -> Any n -> Space -> ChainComplexHom r n
spcChainComplexSet t s n (Space c) = chainComplexSet t s n c

{-
spcChainComplexSetZ ::  ChainComplexType -> SimplexType s -> Any n -> Space m -> ChainComplexHom Z n
spcChainComplexSetZ = spcChainComplexSet
-}


--------------------------------------------------------------------------------
-- Continuous -

-- | mapping between two spaces.
data Continuous s where
  Continuous :: ComplexMap s (Complex x) (Complex y) -> Continuous s

deriving instance Show (Continuous s)

cntEqStuct :: Homomorphous EntOrd x y -> Homomorphous EntOrd x' y'
  -> ComplexMap s (Complex x) (Complex y) -> ComplexMap s (Complex x') (Complex y')
  -> Bool
cntEqStuct (Struct :>: Struct) (Struct :>: Struct) f g
  = case (eqVertexType (cpmDomain f) (cpmDomain g), eqVertexType (cpmRange f) (cpmRange g)) of
      (Just Refl,Just Refl) -> f == g
      _                     -> False

instance Eq (Continuous s) where
  Continuous f == Continuous g = cntEqStuct (cpmHomEntOrd f) (cpmHomEntOrd g) f g


instance Validable (Continuous s) where
  valid (Continuous f) = Label "Continous" :<=>: valid f

{-
--------------------------------------------------------------------------------
-- cntAbstract -

-- | abstraction of a continuous map.
cntAbstract :: Continuous s m -> Continuous s Abstract
cntAbstract f@(Continuous _ ) = f
cntAbstract (CntConcrete f)    = Continuous f
-}

--------------------------------------------------------------------------------
-- cntDomain -

cntDomain :: Continuous s -> Space
cntDomain (Continuous f) = case cpmHomEntOrd f of Struct :>: _ -> Space (cpmDomain f)

--------------------------------------------------------------------------------
-- contRange -

cntRange :: Continuous s -> Space
cntRange (Continuous f) = case cpmHomEntOrd f of _ :>: Struct -> Space (cpmRange f)


--------------------------------------------------------------------------------
-- Continuous - Multiplicative -

type instance Point (Continuous s) = Space

deriving instance ShowPoint (Continuous s)
deriving instance EqPoint (Continuous s)
deriving instance ValidablePoint (Continuous s)
deriving instance TypeablePoint (Continuous s)

instance Typeable s => Oriented (Continuous s) where
  start = cntDomain
  end   = cntRange

instance AttestableSimplexType s => Multiplicative (Continuous s) where
  one (Space c) = Continuous (cpmOne Struct simplexType c) 

  Continuous f * Continuous g        = case (cpmHomEntOrd f,cpmHomEntOrd g) of
    (Struct:>:Struct,Struct:>:Struct) -> case eqVertexType (cpmRange g) (cpmDomain f) of
      Just Refl                       -> Continuous (cpmMlt f g)
      Nothing                         -> throw NotMultiplicable


--------------------------------------------------------------------------------
-- Hmlg -

data Hmlg n x y where
  ChC  :: (Ring r, Commutative r, AttestableSimplexType s)
       => ChainComplexType -> Any n -> Hmlg n (Continuous s) (ChainComplexHom r n)
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
  amapG (ChC t n) (Id f) = Id $ case f of
    Continuous f'       -> case cpmHomEntOrd f' of
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

hC :: (Ring r, Commutative r, AttestableSimplexType s)
  => ChainComplexType -> Any n -> HCat n (Continuous s) (ChainComplexHom r n)
hC t n = ChC t n :. IdPath Struct

hC' :: (Ring r, Commutative r, AttestableSimplexType s)
  => q s -> Homological r h
  -> ChainComplexType -> Any n -> HCat n (Continuous s) (ChainComplexHom r n)
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

hB' :: (Galoisian r, SlicedFree h, Distributive h, Attestable n)
  => Homological r h
  -> HCat n (ChainComplexHom r n) (BettiHom n h)
hB' h = hB h . hF h . hD h . hZ


