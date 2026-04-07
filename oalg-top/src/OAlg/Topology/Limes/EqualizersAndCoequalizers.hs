
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, TupleSections #-}

-- |
-- Module      : OAlg.Topology.Limes.EqualizersAndCoequalizers
-- Description : equalizers and coequalizers.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Equalizers and coequalizers.
module OAlg.Topology.Limes.EqualizersAndCoequalizers
  (
  ) where

-- import Control.Monad as M

-- import Data.Typeable

import OAlg.Prelude

-- import OAlg.Category.Map

-- import OAlg.Data.Either
-- import OAlg.Data.Filterable

import OAlg.Structure.Oriented
-- import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
-- import OAlg.Structure.PartiallyOrdered

-- import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Sequence.Set
-- import OAlg.Entity.Sequence.Graph

import OAlg.Entity.Matrix

import OAlg.Limes.Definition
import OAlg.Limes.Cone
-- import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.Deviation

import OAlg.Homology.Simplical hiding (simplex,dimension)
import OAlg.Homology.Complex -- hiding (cpxProduct, cpxProductAsc)
import OAlg.Homology.ChainComplex
import OAlg.Homology.Definition hiding (B)

import OAlg.Topology.Definition
-- import OAlg.Topology.Limes.TerminalAndInitialSpace

import OAlg.Data.Symbol
--------------------------------------------------------------------------------
-- ff -

-- | the various conection classes.
ff :: Space m -> Matrix F2
ff u@(SpaceConcrete _) = ff $ spcAbstract u
ff u@(SpaceAbstract _)   = p * v where
  p = cokernelFactor $ universalCone ckr
  v = universalFactor kr (ConeKernel d o) where
    d = universalDiagram kr
    o = one $ end $ kernelFactor $ universalCone kr

  VarianceG _ ((kr,ckr):|Nil) = homology f2 cf
  
  cf = pmap (hF f2 . hZ . hC) u
  f2 = HmlgF :: f ~ F2 => Homological f (Matrix f)
  hC = hC' SpxTypeSet f2 ChainComplexStandard (attest :: Any N0)

  

s = SpaceAbstract $ complex [Set [A,B],Set [C]] 
