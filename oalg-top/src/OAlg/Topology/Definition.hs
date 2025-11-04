
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
    Space(..), Model(..)
  , spcAbstract

    -- * Continuous
  , Continuous(..)
  , cntDomain, cntRange
  , cntAbstract

    -- * Homology
  , HmlgCat, Hmlg(..)
  , cntAbs, cntChc, cntCrd, cntCnz, cntDev
  ) where


import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Exception
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Matrix.Vector

import OAlg.Limes.Exact.Deviation

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Complex hiding (Hmlg)
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
-- Continuous -

-- | mapping between two spaces.
data Continuous m where
  CntAbstract :: ComplexMap Preserving (Complex x) (Complex x)
               -> Continuous Abstract
  CntConcrete :: ComplexMap Preserving (Complex (Vector Q)) (Complex (Vector Q))
               -> Continuous Concrete

deriving instance Show (Continuous m)

cntEqAbstr :: Homomorphous EntOrd x y -> Homomorphous EntOrd x' y'
  -> ComplexMap s (Complex x) (Complex y) -> ComplexMap s (Complex x') (Complex y')
  -> Bool
cntEqAbstr (Struct :>: Struct) (Struct :>: Struct) f g
  = case (eqVertexType (cpmDomain f) (cpmDomain g), eqVertexType (cpmRange f) (cpmRange g)) of
      (Just Refl,Just Refl) -> f == g
      _                     -> False

instance Eq (Continuous m) where
  CntAbstract f == CntAbstract g = cntEqAbstr (cpmHomEntOrd f) (cpmHomEntOrd g) f g
  CntConcrete f == CntConcrete g = f == g

instance Validable (Continuous m) where
  valid f = Label "Continous" :<=>: case f of
    CntAbstract f' -> Label "Abstract" :<=>: valid f'
    CntConcrete f' -> Label "Concrete" :<=>: valid f'
    
--------------------------------------------------------------------------------
-- cntAbstract -

-- | abstraction of a continuous map.
cntAbstract :: Continuous m -> Continuous Abstract
cntAbstract f@(CntAbstract _ ) = f
cntAbstract (CntConcrete f)    = CntAbstract f

--------------------------------------------------------------------------------
-- cntDomain -

cntDomain :: Continuous m -> Space m
cntDomain (CntAbstract f) = case cpmHomEntOrd f of Struct :>: _ -> SpaceAbstract (cpmDomain f)
cntDomain (CntConcrete f) = SpaceConcrete (cpmDomain f)

--------------------------------------------------------------------------------
-- contRange -

cntRange :: Continuous m -> Space m
cntRange (CntAbstract f) = case cpmHomEntOrd f of _ :>: Struct -> SpaceAbstract (cpmRange f)
cntRange (CntConcrete f) = SpaceConcrete (cpmRange f)

--------------------------------------------------------------------------------
-- Continuous - Multiplicative -

type instance Point (Continuous m) = Space m

deriving instance ShowPoint (Continuous m)
deriving instance EqPoint (Continuous m)
deriving instance ValidablePoint (Continuous m)
deriving instance Typeable m => TypeablePoint (Continuous m)

instance Typeable m => Oriented (Continuous m) where
  start = cntDomain
  end   = cntRange

instance Typeable m => Multiplicative (Continuous m) where
  one (SpaceAbstract c) = CntAbstract (cpmOne Struct c) 
  one (SpaceConcrete c) = CntConcrete (cpmOne Struct c)

  CntConcrete f * CntConcrete g = CntConcrete (cpmMlt f g)
  CntAbstract f * CntAbstract g = case (cpmHomEntOrd f,cpmHomEntOrd g) of
    (Struct:>:Struct,Struct:>:_) -> case eqVertexType (cpmRange g) (cpmDomain f) of
      Just Refl                  -> CntAbstract (cpmMlt f g)
      Nothing                    -> throw NotMultiplicable

--------------------------------------------------------------------------------
-- Hmlg -

data Hmlg n x y where
  Abs :: Typeable m => Hmlg n (Continuous m) (Continuous Abstract)
  Chc :: (Typeable t, Attestable n)
      => ChainComplexType t -> Any n
      -> Hmlg n (Continuous Abstract) (SomeChainComplexHom t Z n)
  Crd :: (Typeable t, Attestable n) => Hmlg n (SomeChainComplexHom t Z n) (CardsHom Z n)
  Cnz :: (Typeable t, Attestable n)
      => Hmlg n (SomeChainComplexHom t Z n) (ConsecutiveZeroFreeHom To n AbHom)
  Dev :: Attestable n => Hmlg n (ConsecutiveZeroFreeHom To n AbHom) (DeviationHom (n+1) AbHom)


instance Typeable n => Morphism (Hmlg n) where
  type ObjectClass (Hmlg n) = Mlt
  homomorphous Abs       = Struct :>: Struct
  homomorphous (Chc _ _) = Struct :>: Struct
  homomorphous Crd       = Struct :>: Struct
  homomorphous Cnz       = Struct :>: Struct
  homomorphous Dev       = Struct :>: Struct 

instance ApplicativeG Id (Hmlg n) (->) where
  amapG Abs (Id f)        = Id $ cntAbstract f
  amapG (Chc t n) (Id f)  = Id $ case f of
    CntAbstract f'       -> case domain $ cpmHomEntOrd f' of
      Struct             -> SomeChainComplexHom $ chainComplexHom t n f'
  amapG Crd (Id sc)       = case sc of SomeChainComplexHom f -> Id $ ccxCardsHom f
  amapG Cnz (Id sc)       = Id $ case sc of SomeChainComplexHom f -> abhCnzfh f
  amapG Dev (Id c)        = Id $ homologyGroupsHom $ abhCnzfhHomologyHom c

instance ApplicativeG Pnt (Hmlg n) (->) where
  amapG Abs (Pnt s)       = Pnt $ spcAbstract s
  amapG (Chc t n) (Pnt s) = Pnt $ case s of
    SpaceAbstract s'     -> SomeChainComplex $ chainComplex t n s'
  amapG Crd (Pnt sc)      = Pnt $ case sc of SomeChainComplex c -> ccxCards c
  amapG Cnz (Pnt sc)      = case sc of SomeChainComplex c -> Pnt $ abhCnzf c
  amapG Dev (Pnt c)       = Pnt $ homologyGroups $ abhCnzfHomology c

instance Typeable n => HomOriented (Hmlg n)
instance Typeable n => HomMultiplicative (Hmlg n)

--------------------------------------------------------------------------------
-- HmlgCat -

type HmlgCat n = Path (Hmlg n)

cntAbs :: Typeable m => HmlgCat n (Continuous m) (Continuous Abstract)
cntAbs = Abs :. IdPath Struct

cntChc :: (Typeable t, Attestable n)
  => ChainComplexType t -> Any n -> HmlgCat n (Continuous Abstract) (SomeChainComplexHom t Z n)
cntChc t n = Chc t n :. IdPath Struct

cntCrd :: (Typeable t, Attestable n) => HmlgCat n (SomeChainComplexHom t Z n) (CardsHom Z n)
cntCrd = Crd :. IdPath Struct

cntCnz :: (Typeable t, Attestable n)
  => HmlgCat n (SomeChainComplexHom t Z n) (ConsecutiveZeroFreeHom To n AbHom)
cntCnz = Cnz :. IdPath Struct

cntDev :: Attestable n => HmlgCat n (ConsecutiveZeroFreeHom To n AbHom) (DeviationHom (n+1) AbHom)
cntDev = Dev :. IdPath Struct
