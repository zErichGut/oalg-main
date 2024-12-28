
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.Chain
-- Description : chains and there boundary.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- The boundary of a 'Chain'.
module OAlg.Homology.Chain
  (
    -- * Boundary
    HomBoundary(..), boundary

    -- * Chain
  , Chain, ch
  ) where

import Data.Kind
import Data.Typeable

import Data.List as L (zip)

import OAlg.Prelude

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Vectorial

import OAlg.Entity.Sum

import OAlg.Homology.Simplical
import OAlg.Homology.Complex

--------------------------------------------------------------------------------
-- Chain -

-- | chains as a formal sum of simplices.
type Chain r s x = SumSymbol r (s x)

--------------------------------------------------------------------------------
-- ch -

-- | simplex as a chain.
ch :: (Ring r, Commutative r, Simplical s, Entity (s x), Ord (s x)) => s x -> Chain r s x
ch = sy

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary operator of chains.
boundary :: (Ring r, Commutative r, Simplical s, Entity (s x), Ord (s x))
  => Chain r s x -> Chain r s x
boundary = ssySum (bdr rAlt) where
  bdr :: Simplical s => [r] -> s x -> LinearCombination r (s x)
  bdr rs s = LinearCombination (rs `zip` faces s)

--------------------------------------------------------------------------------
-- HomBoundary -

-- | the 'boundary' operator as homomorphism.
data HomBoundary r (s :: Type -> Type) x y where
  HomBoundary :: (Entity (s x), Ord (s x)) 
    => HomBoundary r s (Chain r s x) (Chain r s x)

--------------------------------------------------------------------------------
-- HomBoundary - Entity -

deriving instance Show (HomBoundary r s x y)
instance Show2 (HomBoundary s r)

deriving instance Eq (HomBoundary r s x y)
instance Eq2 (HomBoundary r s)

instance Validable (HomBoundary r s x y) where
  valid HomBoundary = SValid
  
instance Validable2 (HomBoundary r s)

instance (Typeable r, Typeable s, Typeable x, Typeable y) => Entity (HomBoundary r s x y)
instance (Typeable r, Typeable s) => Entity2 (HomBoundary r s)

--------------------------------------------------------------------------------
-- HomBoundary - HomVectorial -

instance (Ring r, Commutative r) => Morphism (HomBoundary r s) where
  type ObjectClass (HomBoundary r s) = Vec r
  homomorphous HomBoundary = Struct :>: Struct


instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r s) Typ
instance (Ring r, Commutative r) => EmbeddableMorphismTyp (HomBoundary r s) 
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r s) Fbr
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r s) Add
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r s) (Vec r)

instance (Ring r, Commutative r, Simplical s, Typeable s) => Applicative (HomBoundary r s) where
  amap HomBoundary = boundary

instance (Ring r, Commutative r, Simplical s, Typeable s) => HomFibred (HomBoundary r s) where
  rmap HomBoundary = const ()

instance (Ring r, Commutative r, Simplical s, Typeable s) => HomAdditive (HomBoundary r s)
instance (Ring r, Commutative r, Simplical s, Typeable s) => HomVectorial r (HomBoundary r s)
