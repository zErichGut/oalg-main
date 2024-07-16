
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.AbelianGroup.Proposition
-- Description : validity of abelian groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- validity of abelian groups.
module OAlg.AbelianGroup.Proposition
  ( prpAbelianGroups
  ) where

import OAlg.Prelude

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Slice.Free

import OAlg.Limes.Definition
import OAlg.Limes.KernelsAndCokernels

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

--------------------------------------------------------------------------------
-- prpAbhCokernelLftFree -

prpAbhCokernelLftFree :: CokernelDiagram N1 AbHom -> Statement
prpAbhCokernelLftFree dgm
  = And [ (dgm == (diagram $ clfCokernel ck)) :?> Params ["dgm":=show dgm]
        , valid ck
        ]
  where ck = abhCokernelLftFree dgm

-- | validity for abelian groups.
prpAbelianGroups :: Statement
prpAbelianGroups = Prp "AbelianGroups"
  :<=>: And [ prpAbHom
            , Label "isoSmithNormal" :<=>: Forall xStandard (valid . isoSmithNormal)
            , Label "kernels" :<=>: valid abhKernels
            , Label "cokernels liftable" :<=>: Forall xStandard prpAbhCokernelLftFree
            , Label "abhFreeAdjunction" :<=>: valid abhFreeAdjunction
            ]
