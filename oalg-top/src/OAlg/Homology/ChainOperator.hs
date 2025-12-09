
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}


-- |
-- Module      : OAlg.Homology.ChainOperator
-- Description : operators on chains of simlices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Operators on chains of simplices.
module OAlg.Homology.ChainOperator
  (
    -- * Operator
    ChainOperator(..)

    -- * Chain
  , ChainG, ch, chZ, boundary, chainMap
  ) where

import Data.List as L (zip)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Vectorial

import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- ChainG -

-- | chains as a formal sum of simplices.
type ChainG r s x = SumSymbol r (s x)

--------------------------------------------------------------------------------
-- ch -

-- | a simplex as a @__r__@-chain.
ch :: (Ring r, Commutative r, Simplical s x) => s x -> ChainG r s x
ch = sy

-- | a simplex as a 'Z'-chain.
chZ :: Simplical s x => s x -> ChainG Z s x
chZ = ch

--------------------------------------------------------------------------------
-- rAlt -

-- | infinite list of alternating @['rOne', -'rOne','rOne'...]@. 
rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

--------------------------------------------------------------------------------
-- zeroHom -

-- | the zero homomorphism.
zeroHom :: (Ring r, Commutative r, Simplical s y)
  => ChainG r s x -> ChainG r s y
zeroHom = ssySum (const $ LinearCombination [])

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary operator of chains.
boundary :: (Ring r, Commutative r, Simplical s x)
  => ChainG r s x -> ChainG r s x
boundary = ssySum (bdr rAlt) where
  bdr :: Simplical s x => [r] -> s x -> LinearCombination r (s x)
  bdr rs s = LinearCombination (rs `zip` faces s)

--------------------------------------------------------------------------------
-- chainMap -

chainMap :: (Ring r, Commutative r, SimplicalApplicative s x y)
  => Map EntOrd x y -> ChainG r s x -> ChainG r s y
chainMap f = ssySum (chMap f) where
  chMap :: (Ring r, SimplicalApplicative s x y) => Map EntOrd x y -> s x -> LinearCombination r (s y)
  chMap f sx = LinearCombination [(rOne,amap1 f sx)]

--------------------------------------------------------------------------------
-- chainSimplex -

chainSimplex :: (Ring r, Commutative r, Simplical s x)
  => ChainG r Set x -> ChainG r s x
chainSimplex = ssySum toSmpl where
  toSmpl :: (Ring r, Simplical s x) => Set x -> LinearCombination r (s x)
  toSmpl s = LinearCombination [(rOne,simplex s)]

--------------------------------------------------------------------------------
-- chainVertices -

chainVertices :: (Ring r, Commutative r, Simplical s x)
  => ChainG r s x -> ChainG r Set x
chainVertices = ssySum toVrts where
  toVrts :: (Ring r, Simplical s x) => s x -> LinearCombination r (Set x)
  toVrts s = LinearCombination [(rOne,vertices s)]

--------------------------------------------------------------------------------
-- ChainOperator -

data ChainOperator r s x y where
  Boundary :: Simplical s x => ChainOperator r s (ChainG r s x) (ChainG r s x)
  ChainMap :: SimplicalApplicative s x y
    => Map EntOrd x y -> ChainOperator r s (ChainG r s x) (ChainG r s y)
  Simplex :: Simplical s x => ChainOperator r s (ChainG r Set x) (ChainG r s x)

instance (Ring r, Commutative r) => Morphism (ChainOperator r s) where
  type ObjectClass (ChainOperator r s) = Vec r
  homomorphous Boundary     = Struct :>: Struct
  homomorphous (ChainMap _) = Struct :>: Struct
  homomorphous Simplex      = Struct :>: Struct

instance (Ring r, Commutative r) => ApplicativeG Id (ChainOperator r s) (->) where
  amapG Boundary     = toIdG boundary
  amapG (ChainMap f) = toIdG (chainMap f)
  amapG Simplex      = toIdG chainSimplex

instance Ring r => ApplicativeG Rt (ChainOperator r s) (->) where
  amapG Boundary     = amapRt (const ())
  amapG (ChainMap _) = amapRt (const ())
  amapG Simplex      = amapRt (const ())

instance (Ring r, Commutative r) => HomFibred (ChainOperator r s)
instance (Ring r, Commutative r) => HomAdditive (ChainOperator r s)
instance (Ring r, Commutative r) => HomVectorial r (ChainOperator r s)

