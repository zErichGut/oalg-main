
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
-- The 'boundary' of a 'Chain'.
module OAlg.Homology.Chain
  ( -- * Boundary
    HomBoundary(..), boundary

    -- * Chain
  , Chain, ch
  , ChainZero

  ) where

import Data.Typeable


import Data.List as L (zip)
import Data.Foldable

import OAlg.Prelude

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Vectorial

import OAlg.Entity.Natural
import OAlg.Entity.Sum as Sum hiding (S)

import OAlg.Homology.Simplex

--------------------------------------------------------------------------------
-- ChainZero -

-- | chains for empty simplex sets. For example chains with a /negative/ length.
type ChainZero r x = SumSymbol r Empty

--------------------------------------------------------------------------------
-- Chain -

-- | chains of order @__o__@ as free sum over simplices of the length @__o__@.
type Chain r (o :: N') x = SumSymbol r (Simplex o x)


--------------------------------------------------------------------------------
-- ch -

-- | simplex as a chain.
ch :: (Attestable o, Ring r, Commutative r, Entity x, Ord x) => Simplex o x -> Chain r o x
ch = Sum.sy

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

-------------------------------------------------------------------------------
-- boundary -

-- | the boundary operator of a chain of order @__o__@. 
boundary :: (Attestable o, Ring r, Commutative r, Entity x, Ord x)
  => Chain r (o+1) x -> Chain r o x
boundary = ssySum (f rAlt) where
  f :: [r] -> Simplex (n+1) x -> LinearCombination r (Simplex n x)
  f rs sn' = LinearCombination (rs `zip` (toList $ faces sn'))
 
--------------------------------------------------------------------------------
-- HomBoundary -

-- | the 'boundary' operator as homomorphism.
data HomBoundary r x y where
  HomBoundary :: (Attestable o, Entity x, Ord x) 
    => HomBoundary r (Chain r (o+1) x) (Chain r o x)

--------------------------------------------------------------------------------
-- HomBoundary - Entity -

deriving instance Show (HomBoundary r x y)
instance Show2 (HomBoundary r)

deriving instance Eq (HomBoundary r x y)
instance Eq2 (HomBoundary r)

instance Validable (HomBoundary r x y) where
  valid HomBoundary     = SValid
  
instance Validable2 (HomBoundary r)

instance (Typeable r, Typeable x, Typeable y) => Entity (HomBoundary r x y)
instance Typeable r => Entity2 (HomBoundary r)

--------------------------------------------------------------------------------
-- HomBoundary - HomVectorial -

instance (Ring r, Commutative r) => Morphism (HomBoundary r) where
  type ObjectClass (HomBoundary r) = Vec r
  homomorphous HomBoundary = Struct :>: Struct


instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r) Typ
instance (Ring r, Commutative r) => EmbeddableMorphismTyp (HomBoundary r) 
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r) Fbr
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r) Add
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r) (Vec r)

instance (Ring r, Commutative r) => Applicative (HomBoundary r) where
  amap HomBoundary     = boundary
  
instance (Ring r, Commutative r) => HomFibred (HomBoundary r) where
  rmap HomBoundary     = const ()

instance (Ring r, Commutative r) => HomAdditive (HomBoundary r)
instance (Ring r, Commutative r) => HomVectorial r (HomBoundary r)




