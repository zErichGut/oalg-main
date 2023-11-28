
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Definition
-- Description : definition of a homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Homology'.
module OAlg.Homology.Definition
  ( -- * Homology
    Homology(..), homologyGroups, homology
  , homologyFrom
  ) where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Distributive

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.Entity.Natural
import OAlg.Entity.FinList as F hiding (zip) 
import OAlg.Entity.Diagram
import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels


import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex

--------------------------------------------------------------------------------
-- homologyFrom -

-- | the homology
--
-- __Pre__ @'end' g '==' 'start' f@
homologyFrom :: Distributive a => Kernels N1 a -> Cokernels N1 a -> ChainComplex From n a -> Point a
homologyFrom ker coker (ChainComplex (DiagramChainFrom _ (g:|f:|_))) = tip $ universalCone hCoker where

  -- image of g
  gCoker = limes coker (cokernelDiagram g)
  gIm    = limes ker (kernelDiagram $ cokernelFactor $ universalCone gCoker)

  -- kernel of f
  fKer   = limes ker (kernelDiagram f)

  h      = universalFactor fKer (ConeKernel (diagram fKer) (kernelFactor $ universalCone gIm))
  hCoker = limes coker (cokernelDiagram h)

--------------------------------------------------------------------------------
-- Homology -

newtype Homology n a = Homology (FinList (n+1) (Point a))

deriving instance Distributive a => Show (Homology n a)


--------------------------------------------------------------------------------
-- homology -

homology :: Distributive a
  => Kernels N1 a -> Cokernels N1 a -> ChainComplex From n a -> Homology n a
homology ker coker = Homology . hmlgy ker coker where
  hmlgy :: Distributive a
    => Kernels N1 a -> Cokernels N1 a -> ChainComplex From n a -> FinList (n+1) (Point a)
  
  hmlgy ker coker c@(ChainComplex (DiagramChainFrom _ (_:|_:|Nil)))
    = homologyFrom ker coker c:|Nil
  hmlgy ker coker c@(ChainComplex (DiagramChainFrom _ (_:|_:|_:|_)))
    = homologyFrom ker coker c:|hmlgy ker coker (ccplPred c)

-----------------------------------------------------------------------------------------
-- homologyGroups -

homologyGroups :: Simplical s x => Complex s n x -> Homology n AbHom
homologyGroups = homology abhKernels abhCokernels . chainComplex




