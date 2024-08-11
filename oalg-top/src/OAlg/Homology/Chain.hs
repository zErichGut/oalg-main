
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}


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
    HomBoundary(..), homBoundary

    -- * Chain
  , Chain, ch

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
-- Chain -

type Chain r (n :: N') x = SumSymbol r (Simplex n x)


--------------------------------------------------------------------------------
-- ch -
{-
chStruct :: (Ring r, Commutative r)
  => Struct Ent (s n x) -> Struct Ord' (s n x) -> s n x -> Chain r s n x
chStruct Struct Struct = Sum.sy
-}

ch :: (Ring r, Commutative r, Entity x, Attestable n, Ord x) => Simplex n x -> Chain r n x
ch = Sum.sy


--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

-------------------------------------------------------------------------------
-- homBoundary -
{-
homBoundaryOrd :: (Simplical s x, Ring r, Commutative r)
  => Struct Ord' (s n x) -> Struct Ent (s n x) -> Chain r s (n+1) x -> Chain r s n x
homBoundaryOrd Struct Struct c = ssySum (f rAlt) c where
  f :: Simplical s x => [r] -> s (n+1) x -> LinearCombination r (s n x)
  f rs sn' = f' rs (amap1 fcSimplex $ toList $ faces sn')
 
  f' :: forall r (s :: N' -> Type -> Type) (n :: N') x . [r] -> [s n x] -> LinearCombination r (s n x)
  f' rs sns = LinearCombination (rs `zip` sns) 
-}            
homBoundary :: (Ring r, Commutative r, Attestable n, Entity x, Ord x)
  => Chain r (n+1) x -> Chain r n x
homBoundary = ssySum (f rAlt) where
  f :: [r] -> Simplex (n+1) x -> LinearCombination r (Simplex n x)
  f rs sn' = f' rs (amap1 fcSimplex $ toList $ faces sn')
 
  f' rs sns = LinearCombination (rs `zip` sns) 


--------------------------------------------------------------------------------
-- HomBoundary -

data HomBoundary r x y where
  HomBoundary :: (Entity x, Ord x, Attestable n) 
    => HomBoundary r (Chain r (n+1) x) (Chain r n x)

--------------------------------------------------------------------------------
-- HomBoundary - Entity -

deriving instance Show (HomBoundary r x y)
instance Show2 (HomBoundary r)

deriving instance Eq (HomBoundary r x y)
instance Eq2 (HomBoundary r)

instance Validable (HomBoundary r x y) where
  valid HomBoundary = SValid
instance Validable2 (HomBoundary r)

instance (Typeable r, Typeable x, Typeable y) => Entity (HomBoundary r x y)
instance Typeable r => Entity2 (HomBoundary r)

--------------------------------------------------------------------------------
-- HomBoundary - HomVectorial -

{-
hbdOrd :: HomBoundary r s (Chain r s (n+1) x) (Chain r s n x)
  -> Homomorphous Ord' (s (n+1) x) (s n x)
hbdOrd HomBoundary = sOrd :>: sOrd

hbdEnt :: HomBoundary r s (Chain r s (n+1) x) (Chain r s n x)
  -> Homomorphous Ent (s (n+1) x) (s n x)
hbdEnt HomBoundary = sEnt :>: sEnt
-}


instance (Ring r, Commutative r) => Morphism (HomBoundary r) where
  type ObjectClass (HomBoundary r) = Vec r
  homomorphous HomBoundary = Struct :>: Struct


instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r) Typ
instance (Ring r, Commutative r) => EmbeddableMorphismTyp (HomBoundary r) 
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r) Fbr
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r) Add
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r) (Vec r)

instance (Ring r, Commutative r) => Applicative (HomBoundary r) where
  amap HomBoundary = homBoundary
  
instance (Ring r, Commutative r) => HomFibred (HomBoundary r) where
  rmap HomBoundary _ = ()
instance (Ring r, Commutative r) => HomAdditive (HomBoundary r)
instance (Ring r, Commutative r) => HomVectorial r (HomBoundary r)



