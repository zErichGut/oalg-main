
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Definition
-- Description : definition of homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Homology'.
module OAlg.Homology.Definition
  (
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Either

import OAlg.Structure.Additive
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Algebraic

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Diagram

import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.ConsZero

import OAlg.Hom.Definition

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator
import OAlg.Homology.ChainComplex

--------------------------------------------------------------------------------
-- Homology -

type Homology n = Deviation (n+1)

--------------------------------------------------------------------------------
-- homology -

homology :: ( Hom Dst h
            , AlgebraicSemiring r, Ring r, Ord r, Typeable s
            , Distributive a
            )
  => h (Matrix r) a -> Kernels N1 a -> Cokernels N1 a
  -> ChainComplex n (ChainOperator r s) -> Homology n a
homology h kers cokers c = deviations kers cokers reps where
  reps = cnzMap h $ ccpRepMatrix c

a = complex [Set "abc"]

hmgSet :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> Homology n AbHom
hmgSet r n c = homology FreeAbHom abhKernels abhCokernels $ ccp r n c  where
  ccp :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> ChainComplex n (ChainOperator Z Set)
  ccp = chainComplex

hmgLst :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> Homology n AbHom
hmgLst r n c = homology FreeAbHom abhKernels abhCokernels $ ccp r n c  where
  ccp :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> ChainComplex n (ChainOperator Z [])
  ccp = chainComplex

hmgAsc :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> Homology n AbHom
hmgAsc r n c = homology FreeAbHom abhKernels abhCokernels $ ccp r n c  where
  ccp :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> ChainComplex n (ChainOperator Z Asc)
  ccp = chainComplex
