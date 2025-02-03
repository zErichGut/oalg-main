
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
import OAlg.Category.Map

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
homology h kers cokers = deviations kers cokers . cnzMap h . ccpRepMatrix

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

--------------------------------------------------------------------------------
-- HomologyOperatorAtom -

data HomologyOperatorAtom n r s x y where
  C :: Regular -> Any n
    -> HomologyOperatorAtom n r s (Complex x) (ChainComplex n (ChainOperator r s))
  H :: Hom Dst h => h (Matrix r) a -> Kernels N1 a -> Cokernels N1 a
    -> HomologyOperatorAtom n r s (ChainComplex n (ChainOperator r s)) (Homology n a)
  T :: HomologyOperatorAtom n r s (ChainComplex n (ChainOperator r s)) (Cards (n+3))

--------------------------------------------------------------------------------
-- HomologyOperator -

type HomologyOperator n r s = Path (HomologyOperatorAtom n r s)

--------------------------------------------------------------------------------
-- HomologyTrafo -

type HomologyTrafo n = DeviationTrafo (n+1)

------------------------------------------------------------------------------------------
-- homologyTrafo -

homologyTrafo :: ( Hom Dst h
                 , AlgebraicSemiring r, Ring r, Ord r, Typeable s
                 , Distributive a
                 )
  => h (Matrix r) a -> Kernels N1 a -> Cokernels N1 a
  -> ChainComplexTrafo n (ChainOperator r s) -> HomologyTrafo n a
homologyTrafo h kers cokers = deviationTrafos kers cokers . cnztMap h . ccptRepMatrix

hmgt :: (Homological s x y) => Regular -> Any n
  -> ComplexMap s (Complex x) (Complex y) -> HomologyTrafo n AbHom
hmgt r n f = homologyTrafo FreeAbHom abhKernels abhCokernels $ ccpt r n f where
  ccpt :: (Homological s x y)
       => Regular -> Any n -> ComplexMap s (Complex x) (Complex y)
       -> ChainComplexTrafo n (ChainOperator Z s)
  ccpt = chainComplexTrafo
