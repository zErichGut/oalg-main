
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
  ) where


import Control.Monad

import Data.Typeable
import Data.List as L ((++),repeat)
import Data.Foldable (foldl)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Filterable

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
import OAlg.Structure.Algebraic

import OAlg.Hom.Distributive ()

import OAlg.Entity.Diagram
import OAlg.Entity.FinList as F hiding ((++),repeat)
import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Sequence hiding (span,isEmpty)
import OAlg.Entity.Matrix.Vector

import OAlg.Structure.Exception
import OAlg.Structure.PartiallyOrdered

import OAlg.Homology.Simplical
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
-- SomeChainComplex -

data SomeChainComplex t r s n where
  SomeChainComplex :: (Simplical s x, Attestable n)
    => ChainComplex t r s n x -> SomeChainComplex t r s n

deriving instance (Ring r, Commutative r, Ord r) => Show (SomeChainComplex t r s n)

instance (Ring r, Commutative r, Ord r) => Eq (SomeChainComplex t r s n) where
  SomeChainComplex a == SomeChainComplex b = case eqVertexType a b of
    Just Refl -> a == b
    Nothing   -> False

instance (Ring r, Commutative r, Ord r) => Validable (SomeChainComplex t r s n) where
  valid (SomeChainComplex c) = Label "SomeChainComplex" :<=>: valid c

--------------------------------------------------------------------------------
-- someChainComplex -

someChainComplex :: ( Ring r, Commutative r, Ord r, Attestable n)
  => SimplexType s -> ChainComplexType t -> Any n -> Space m -> SomeChainComplex t r s n
someChainComplex s t n (SpaceAbstract c) = case structSmpl s c of
  Struct -> SomeChainComplex $ chainComplex t n c
someChainComplex s t n x = someChainComplex s t n (spcAbstract x)

--------------------------------------------------------------------------------
-- sccHomology -

sccHomology :: SomeChainComplex t Z s n -> Homology n
sccHomology (SomeChainComplex ccx) = homology ccx

--------------------------------------------------------------------------------
-- chainHomology -

chainHomology :: Attestable n
  => SimplexType s -> ChainComplexType t -> Any n -> Space m -> Homology n
chainHomology s t n x = sccHomology $ someChainComplex s t n x

--------------------------------------------------------------------------------
-- Continuous -

-- | mapping between two spaces.
data Continuous m where
  ContAbstract :: ComplexMap Preserving (Complex x) (Complex x)
               -> Continuous Abstract
  ContConcrete :: ComplexMap Preserving (Complex (Vector Q)) (Complex (Vector Q))
               -> Continuous Concrete

deriving instance Show (Continuous m)

contEqAbstr :: Homomorphous EntOrd x y -> Homomorphous EntOrd x' y'
  -> ComplexMap s (Complex x) (Complex y) -> ComplexMap s (Complex x') (Complex y')
  -> Bool
contEqAbstr (Struct :>: Struct) (Struct :>: Struct) f g
  = case (eqVertexType (cpmDomain f) (cpmDomain g), eqVertexType (cpmRange f) (cpmRange g)) of
      (Just Refl,Just Refl) -> f == g
      _                     -> False

instance Eq (Continuous m) where
  ContAbstract f == ContAbstract g = contEqAbstr (cpmHomEntOrd f) (cpmHomEntOrd g) f g
  ContConcrete f == ContConcrete g = f == g

instance Validable (Continuous m) where
  valid f = Label "Continous" :<=>: case f of
    ContAbstract f' -> Label "Abstract" :<=>: valid f'
    ContConcrete f' -> Label "Concrete" :<=>: valid f'
    
--------------------------------------------------------------------------------
-- contAbstract -

-- | abstraction of a continuous map.
contAbstract :: Continuous m -> Continuous Abstract
contAbstract f@(ContAbstract _ ) = f
contAbstract (ContConcrete f)    = ContAbstract f

--------------------------------------------------------------------------------
-- contDomain -

contDomain :: Continuous m -> Space m
contDomain (ContAbstract f) = case cpmHomEntOrd f of Struct :>: _ -> SpaceAbstract (cpmDomain f)
contDomain (ContConcrete f) = SpaceConcrete (cpmDomain f)

--------------------------------------------------------------------------------
-- contRange -

contRange :: Continuous m -> Space m
contRange (ContAbstract f) = case cpmHomEntOrd f of _ :>: Struct -> SpaceAbstract (cpmRange f)
contRange (ContConcrete f) = SpaceConcrete (cpmRange f)

--------------------------------------------------------------------------------
-- Continuous - Multiplicative -

type instance Point (Continuous m) = Space m

deriving instance ShowPoint (Continuous m)
deriving instance EqPoint (Continuous m)
deriving instance ValidablePoint (Continuous m)
deriving instance Typeable m => TypeablePoint (Continuous m)

instance Typeable m => Oriented (Continuous m) where
  start = contDomain
  end   = contRange

instance Typeable m => Multiplicative (Continuous m) where
  one (SpaceAbstract c) = ContAbstract (cpmOne Struct c) 
  one (SpaceConcrete c) = ContConcrete (cpmOne Struct c)

  ContConcrete f * ContConcrete g = ContConcrete (cpmMlt f g)
  ContAbstract f * ContAbstract g = case (cpmHomEntOrd f,cpmHomEntOrd g) of
    (Struct:>:Struct,Struct:>:_) -> case eqVertexType (cpmRange g) (cpmDomain f) of
      Just Refl                  -> ContAbstract (cpmMlt f g)
      Nothing                    -> throw NotMultiplicable

--------------------------------------------------------------------------------
-- SomeChainChomplexHom -

data SomeChainComplexHom t r n where
  SomeChainComplexHom :: (Entity x, Ord x, Entity y, Ord y)
    => ChainComplexHom t r Asc n x y -> SomeChainComplexHom t r n

deriving instance (Ring r, Ord r, AlgebraicSemiring r) => Show (SomeChainComplexHom t r n)

instance (Ring r, Ord r, AlgebraicSemiring r) => Eq (SomeChainComplexHom t r n) where
  SomeChainComplexHom f == SomeChainComplexHom g = error "nyi"
--------------------------------------------------------------------------------
-- someChainComplexHom -

someChainComplexHom :: (Ring r, Ord r, AlgebraicSemiring r)
  => ChainComplexType t -> Any n -> Continuous m -> SomeChainComplexHom t r n
someChainComplexHom t n (ContAbstract f) = case cpmHomEntOrd f of
  Struct :>: Struct                     -> SomeChainComplexHom $ chainComplexHom t n f
someChainComplexHom t n (ContConcrete f) = SomeChainComplexHom $ chainComplexHom t n f

--------------------------------------------------------------------------------
-- sccHomologyHom -

sccHomologyHom :: SomeChainComplexHom t Z n -> HomologyHom n
sccHomologyHom (SomeChainComplexHom f) = homologyHom f

--------------------------------------------------------------------------------
-- chainHomologyHom -

chainHomologyHom :: ChainComplexType t -> Any n -> Continuous m -> HomologyHom n
chainHomologyHom t n f = sccHomologyHom $ someChainComplexHom t n f

--------------------------------------------------------------------------------
-- SomeChainComplexHom - Multiplicative -

type instance Point (SomeChainComplexHom t r n) = SomeChainComplex t r Asc n

deriving instance (Ring r, Commutative r, Ord r) => ShowPoint (SomeChainComplexHom t r n)
deriving instance (Ring r, Commutative r, Ord r) => EqPoint (SomeChainComplexHom t r n)
deriving instance (Ring r, Commutative r, Ord r) => ValidablePoint (SomeChainComplexHom t r n)
deriving instance (Typeable t, Typeable r, Typeable n) => TypeablePoint (SomeChainComplexHom t r n)

{-
instance (Ring r, Commutative r, Ord r, Typeable t, Typeable n)
  => Oriented (SomeChainComplexHom t r n) where
-}  
