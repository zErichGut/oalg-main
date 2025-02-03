
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
import OAlg.Homology.SomeComplex.Definition

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

{-
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
-}

data FF s where
  FFSet :: FF Set
  FFLst :: FF []
  FFAsc :: FF Asc

ff :: (Entity x, Ord x) => FF s -> Complex x -> Struct (Smpl s) x
ff FFSet _ = Struct
ff FFLst _ = Struct
ff FFAsc _ = Struct


--------------------------------------------------------------------------------
-- HomologyOperatorAtom -

data HomologyOperatorAtom n r s x y where
  C :: FF s -> Regular -> Any n
    -> HomologyOperatorAtom n r s SomeComplex (ChainComplex n (ChainOperator r s))
  R :: HomologyOperatorAtom n r s (ChainComplex n (ChainOperator r s)) (ChainComplex n (Matrix r))
  M :: Hom Dst h => h (Matrix r) a
    -> HomologyOperatorAtom n r s (ChainComplex n (Matrix r)) (ChainComplex n a)
  H :: Distributive a => Kernels N1 a -> Cokernels N1 a
    -> HomologyOperatorAtom n r s (ChainComplex n a) (Homology n a)
    
  U :: Any n ->  HomologyOperatorAtom n r s SomeComplex (Cards (n+3))
  V :: HomologyOperatorAtom n r s (ChainComplex n (ChainOperator r s)) (Cards (n+3))


instance (AlgebraicSemiring r, Ring r, Ord r, Typeable s)
  => Applicative (HomologyOperatorAtom n r s) where
  amap (C s r n)       = \(SomeComplex c) -> chainComplex (ff s c) r n c
  amap R               = ccpRepMatrix
  amap (M h)           = case range h of Struct -> cnzMap h
  amap (H kers cokers) = deviations kers cokers 
  amap (U n)           = scpxCards n
  amap V               = ccpCards

{-

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
-}
