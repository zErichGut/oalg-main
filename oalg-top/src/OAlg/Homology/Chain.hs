
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Homology.Chain
-- Description : boundary of chains.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'boundary' of a 'Chain'.
module OAlg.Homology.Chain
  (  -- * Boundary
    HomBoundary(..), hbdEnt, hbdOrd, homBoundary

    -- * Chain
  , Chain, ch
  

  ) where

import Data.Typeable
import Data.Kind

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

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- Chain -

type Chain r s (n :: N') x = SumSymbol r (s n x)

--------------------------------------------------------------------------------
-- ch -

chStruct :: (Ring r, Commutative r)
  => Struct Ent (s n x) -> Struct Ord' (s n x) -> s n x -> Chain r s n x
chStruct Struct Struct = Sum.sy

ch :: (Simplical s x, Ring r, Commutative r, Attestable n) => s n x -> Chain r s n x
ch = chStruct sEnt sOrd

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

-------------------------------------------------------------------------------
-- homBoundary -

homBoundaryOrd :: (Simplical s x, Ring r, Commutative r)
  => Struct Ord' (s n x) -> Struct Ent (s n x) -> Chain r s (n+1) x -> Chain r s n x
homBoundaryOrd Struct Struct c = ssySum (f rAlt) c where
  f :: Simplical s x => [r] -> s (n+1) x -> LinearCombination r (s n x)
  f rs sn' = f' rs (amap1 fcSimplex $ toList $ faces sn')
 
  f' :: forall r (s :: N' -> Type -> Type) (n :: N') x . [r] -> [s n x] -> LinearCombination r (s n x)
  f' rs sns = LinearCombination (rs `zip` sns) 
            
homBoundary :: (Simplical s x, Ring r, Commutative r, Attestable n)
  => Chain r s (n+1) x -> Chain r s n x
homBoundary = homBoundaryOrd sOrd sEnt

--------------------------------------------------------------------------------
-- HomBoundary -

data HomBoundary r s x y where
  HomBoundary :: (Simplical s x, Attestable n) 
    => HomBoundary r s (Chain r s (n+1) x) (Chain r s n x)

--------------------------------------------------------------------------------
-- HomBoundary - Entity -

deriving instance Show (HomBoundary r s x y)
instance Show2 (HomBoundary r s)

deriving instance Eq (HomBoundary r s x y)
instance Eq2 (HomBoundary r s)

instance Validable (HomBoundary r s x y) where
  valid HomBoundary = SValid
instance Validable2 (HomBoundary r s)

instance (Typeable r, Typeable s, Typeable x, Typeable y) => Entity (HomBoundary r s x y)
instance (Typeable r, Typeable s) => Entity2 (HomBoundary r s)

--------------------------------------------------------------------------------
-- HomBoundary - HomVectorial -

hbdOrd :: HomBoundary r s (Chain r s (n+1) x) (Chain r s n x)
  -> Homomorphous Ord' (s (n+1) x) (s n x)
hbdOrd HomBoundary = sOrd :>: sOrd

hbdEnt :: HomBoundary r s (Chain r s (n+1) x) (Chain r s n x)
  -> Homomorphous Ent (s (n+1) x) (s n x)
hbdEnt HomBoundary = sEnt :>: sEnt

instance (Ring r, Commutative r) => Morphism (HomBoundary r s) where
  type ObjectClass (HomBoundary r s) = Vec r
  homomorphous d@HomBoundary = case (hbdOrd d,hbdEnt d) of
    (Struct :>: Struct,Struct :>: Struct) -> Struct :>: Struct


instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r s) Typ
instance (Ring r, Commutative r) => EmbeddableMorphismTyp (HomBoundary r s) 
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r s) Fbr
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r s) Add
instance (Ring r, Commutative r) => EmbeddableMorphism (HomBoundary r s) (Vec r)

instance (Ring r, Commutative r) => Applicative (HomBoundary r s) where
  amap HomBoundary = homBoundary
  
instance (Ring r, Commutative r, Typeable s) => HomFibred (HomBoundary r s) where
  rmap HomBoundary _ = ()
instance (Ring r, Commutative r, Typeable s) => HomAdditive (HomBoundary r s)
instance (Ring r, Commutative r, Typeable s) => HomVectorial r (HomBoundary r s)


