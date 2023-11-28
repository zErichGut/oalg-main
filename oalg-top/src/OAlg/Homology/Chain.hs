
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
-- Description : Boundary of chains.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'boundary' of a 'Chain'.
module OAlg.Homology.Chain
  (  -- * Boundary
    boundary

    -- * Chain
  , Chain, ch
  

  ) where

import Data.Kind

import Data.List as L (zip)
import Data.Foldable

import OAlg.Prelude

import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

import OAlg.Hom.Definition
import OAlg.Hom.Vectorial

import OAlg.Entity.Natural
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence
import OAlg.Entity.Sum as Sum hiding (S)

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- Chain -

type Chain r s (n :: N') x = SumSymbol r (s n x)

--------------------------------------------------------------------------------
-- ch -

chOrd :: (Ring r, Commutative r, Entity (s n x)) => Struct Ord' (s n x) -> s n x -> Chain r s n x
chOrd Struct = Sum.sy

ch :: (Simplical s x, Ring r, Commutative r, Entity (s n x)) => s n x -> Chain r s n x
ch = chOrd sOrd

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

-------------------------------------------------------------------------------
-- boundary -

boundaryOrd :: (Simplical s x, Ring r, Commutative r)
  => Struct Ord' (s n x) -> Struct Ent (s n x) -> Chain r s (n+1) x -> Chain r s n x
boundaryOrd Struct Struct c = ssSum (f rAlt) c where
  f :: Simplical s x => [r] -> s (n+1) x -> LinearCombination r (s n x)
  f rs sn' = f' rs (amap1 fcSimplex $ toList $ faces sn')
 
  f' :: forall r (s :: N' -> Type -> Type) (n :: N') x . [r] -> [s n x] -> LinearCombination r (s n x)
  f' rs sns = LinearCombination (rs `zip` sns) 
            
boundary :: (Simplical s x, Ring r, Commutative r, Attestable n)
  => Chain r s (n+1) x -> Chain r s n x
boundary = boundaryOrd sOrd sEnt

--------------------------------------------------------------------------------
-- Boundary -

data Boundary r s x y where
  Boundary :: (Simplical s x, Attestable n) 
    => Boundary r s (Chain r s (n+1) x) (Chain r s n x)

bdOrd :: Boundary r s (Chain r s (n+1) x) (Chain r s n x)
  -> Homomorphous Ord' (s (n+1) x) (s n x)
bdOrd Boundary = sOrd :>: sOrd

bdEnt :: Boundary r s (Chain r s (n+1) x) (Chain r s n x)
  -> Homomorphous Ent (s (n+1) x) (s n x)
bdEnt Boundary = sEnt :>: sEnt

instance (Ring r, Commutative r) => Morphism (Boundary r s) where
  type ObjectClass (Boundary r s) = Vec r
  homomorphous d@Boundary = case (bdOrd d,bdEnt d) of
    (Struct :>: Struct,Struct :>: Struct) -> Struct :>: Struct
  
-- instance HomVectorial r (Boundary r s)

--------------------------------------------------------------------------------
-- boundaryMatrix -

-- | representing the 'boundary' operator as a matrix.
--
-- __Property__ Let @m = 'boudaryMatrix' sn' sn@ then holds:
-- If for all @s@ in @sn'@ holds that @'boundary' ('ch' s)@ is a linear combination with elements
-- in @sn@, then @m@ is 'valid'.
boundaryMatrix :: (Simplical s x, Ring r, Commutative r, Entity (s n x))
  => Set (s (n+1) x) -> Set (s n x) -> Matrix r
boundaryMatrix = error "nyi"

--------------------------------------------------------------------------------
-- repMatrix -

repMatrix :: Hom (Vec r) h => h (SumSymbol r x) (SumSymbol r y) -> Set x -> Set y -> Matrix r
repMatrix = error "nyi"
