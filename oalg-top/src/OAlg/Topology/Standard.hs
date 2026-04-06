
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, TupleSections #-}

-- |
-- Module      : OAlg.Topology.Standard
-- Description : some standard topological spaces.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- some standard topological spaces.
module OAlg.Topology.Standard
  (
  ) where

import Data.List (foldr,repeat)

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Either
import OAlg.Data.Filterable

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.PartiallyOrdered

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F hiding (repeat)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Matrix

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.ProductsAndSums

import OAlg.Homology.Definition
import OAlg.Homology.Simplical hiding (simplex,dimension)
import OAlg.Homology.Complex hiding (cpxProduct, cpxProductAsc)
import OAlg.Homology.ChainComplex

import OAlg.Topology.Definition
import OAlg.Topology.Limes.TerminalAndInitialSpace
import OAlg.Topology.Limes.ProductsAndSums

--------------------------------------------------------------------------------
-- simplex -

-- | the standard abstract @n@-dimensional simplex given by the points @0@..@n@.
simplex :: N -> Space Abstract
simplex n = SpaceAbstract $ complex $ [Set [0..n]]

--------------------------------------------------------------------------------
-- point -

-- | the standard point, i.e. the standard 'simplex' of 'dimension' @0@.
point :: Space Abstract
point = simplex 0

--------------------------------------------------------------------------------
-- line -

-- | the standard line, i.e. the standard 'simplex' of 'dimension' @1@,
line :: Space Abstract
line = simplex 1

--------------------------------------------------------------------------------
-- sphere -

-- | the standard abstract sphere, i.e. the 'border' of the @n+1@-dimensional 'simplex'.
sphere :: N -> Space Abstract
sphere n = border $ simplex (n+1)

--------------------------------------------------------------------------------
-- torus -

-- | the standard abstract @n@-dimensional torus, i.e. the product of @n@ times the standard
-- 'sphere' of dimension @1@.
torus :: N -> Space Abstract
torus n = foldr (<*>) point $ takeN n $ repeat $ sphere 1


{-
t :: Diagram Discrete N4 N0 (Continuous Asc Abstract)
t = DiagramDiscrete (s:|s:|s:|s:|Nil) where s = sphere 1

torus :: Space Abstract
torus = tip $ universalCone $ limes cntProductsAsc t

torus' = spcChainComplexSetZ ChainComplexStandard SpxTypeAsc (attest :: Any N3) torus 
-}

z = HmlgZ
f2 = HmlgF :: f ~ F2 => Homological f (Matrix f)
-- ccTorus h = pmap (hC' SpxTypeSet h ChainComplexStandard (attest :: Any N5)) torus

c h = hC' SpxTypeSet h ChainComplexStandard (attest :: Any N5)
-- b h = hB h . hF h . hD h . hZ . hC' SpxTypeSet h ChainComplexStandard (attest :: Any N5)
b h = hB h . hF h . hD h . hZ
-- n h = hN . hC' SpxTypeSet h ChainComplexStandard (attest :: Any N5)


