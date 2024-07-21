
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.AbelianGroup.Proposition
-- Description : validity of abelian groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- validity of abelian groups.
module OAlg.AbelianGroup.Proposition
  ( prpAbelianGroups, prpAbhCokernelLftFree
  ) where

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Slice

import OAlg.Structure.Oriented

import OAlg.Hom.Multiplicative

import OAlg.Limes.Definition
import OAlg.Limes.Cone.Definition
import OAlg.Limes.KernelsAndCokernels

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

--------------------------------------------------------------------------------
-- xHomMltAbhSliceFreeAdjunction -

xHomMltAbhSliceFreeAdjunction :: Attestable k
  => XOrtSite To AbHom -> XHomMlt (AbhSliceFreeAdjunction k)
xHomMltAbhSliceFreeAdjunction xAbhTo = XHomMlt (xPnt k xAbhTo) xMlt where
  k = unit1
  xPnt :: Free k AbHom -> XOrtSite To AbHom -> X (SomeApplPnt (AbhSliceFreeAdjunction k))
  xPnt = error "nyi"
  xMlt = error "nyi"

--------------------------------------------------------------------------------
-- prpAbhCokernelLftFree -

-- | validity of 'abhCokernelLftFree' for a given cokernel diagram @h@.
prpAbhCokernelLftFree :: CokernelDiagram N1 AbHom -> Statement
prpAbhCokernelLftFree h = Prp "AbhCokernelLftFree" :<=>:
  And [ valid c
      , Label "1" :<=>: (h == (diagram $ clfCokernel c)) :?> Params ["h":=show h]
      , Label "2" :<=>: (isSmithNormal $ tip $ universalCone $ clfCokernel c)
          :?> Params ["h":=show h]
      
      ]
  where c = abhCokernelLftFree h

-- | validity for abelian groups.
prpAbelianGroups :: Statement
prpAbelianGroups = Prp "AbelianGroups"
  :<=>: And [ prpAbHom
            , Label "isoSmithNormal" :<=>: Forall xStandard (valid . isoSmithNormal)
            , Label "kernels" :<=>: valid abhKernels
            , Label "cokernels liftable" :<=>: Forall xStandard prpAbhCokernelLftFree
            , Label "abhFreeAdjunction" :<=>: valid abhFreeAdjunction
            ]
