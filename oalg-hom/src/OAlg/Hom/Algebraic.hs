
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : OAlg.Hom.Algebraic
-- Description : homomorphisms between algebraic structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Algebraic' structures having the same associated
-- 'OAlg.Structure.Vectorial.Definition.Scalar'.
module OAlg.Hom.Algebraic
  (
    -- * Algebraic
    HomAlgebraic

  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Distributive.Definition
import OAlg.Structure.Algebraic.Definition

import OAlg.Hom.Definition
import OAlg.Hom.Multiplicative
import OAlg.Hom.FibredOriented
import OAlg.Hom.Distributive
import OAlg.Hom.Vectorial

--------------------------------------------------------------------------------
-- HomAlgebraic -

-- | type family of homomorphisms between 'Algebraic' structures having the same associated
-- 'OAlg.Structure.Vectorial.Definition.Scalar'.
class (HomDistributive h, HomVectorial k h, Transformable (ObjectClass h) (Alg k))
  => HomAlgebraic k h

instance HomAlgebraic k h => HomAlgebraic k (Path h)

--------------------------------------------------------------------------------
-- HomAlgebraicDisjunctive -

-- | disjunctive homomorphisms between @__k__@-'Algebraic' structures.
class ( HomDistributiveDisjunctive h, HomVectorial k h, Transformable (ObjectClass h) (Alg k)
      ) => HomAlgebraicDisjunctive k h

instance ( HomAlgebraic k h
         , DualisableFibredOriented s o, DualisableMultiplicative s o
         , DualisableVectorial k s o
         , Transformable s Dst, Transformable s (Alg k)
         )
  => HomAlgebraicDisjunctive k (HomDisj s o h)

