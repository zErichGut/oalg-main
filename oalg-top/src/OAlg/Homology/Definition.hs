
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
  (
    -- * Homology
    Homology(..), homologyGroups, homology


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
import OAlg.Entity.Slice.Free

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels


import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex


--------------------------------------------------------------------------------
-- HomologyGroup -

data HomologyGroup where
  HomologyGroup 
    :: ChainComplex From N0 AbHom
    -> Kernel N1 AbHom
    -> AbHom
    -> CokernelLiftableFree AbHom
    -> HomologyGroup

--------------------------------------------------------------------------------
-- homologyGroup - 
homologyGroup :: HomologyGroup -> AbGroup
homologyGroup (HomologyGroup _ _ _ c) = tip $ universalCone $ clfCokernel c

--------------------------------------------------------------------------------
-- ccplFromHomologyGroup -

ccplFromHomologyGroup :: ChainComplex From n AbHom -> HomologyGroup
ccplFromHomologyGroup (ChainComplex (DiagramChainFrom s (d:|d':|_)))
  = HomologyGroup
      (ChainComplex (DiagramChainFrom s (d:|d':|Nil)))
      ker
      img
      (abhCokernelLftFree $ cokernelDiagram img)
  where
    d'Dgm = kernelDiagram d'
    ker   = limes abhKernels d'Dgm
    img   = universalFactor ker (ConeKernel d'Dgm d)

--------------------------------------------------------------------------------
-- Homology -

newtype Homology n a = Homology (FinList (n+1) (Point a))

deriving instance Distributive a => Show (Homology n a)


--------------------------------------------------------------------------------
-- homology -

homology :: ChainComplex From n AbHom -> Homology n AbHom
homology = Homology . hmlgy where
  hmlgy :: ChainComplex From n AbHom -> FinList (n+1) AbGroup
  
  hmlgy c@(ChainComplex (DiagramChainFrom _ (_:|_:|Nil)))
    = (homologyGroup $ ccplFromHomologyGroup c):|Nil
  hmlgy c@(ChainComplex (DiagramChainFrom _ (_:|_:|_:|_)))
    = (homologyGroup $ ccplFromHomologyGroup c):|hmlgy (ccplPred c)


-----------------------------------------------------------------------------------------
-- homologyGroups -

homologyGroups :: (Entity x, Ord x) => Complex n x -> Homology n AbHom
homologyGroups = homology . chainComplex




