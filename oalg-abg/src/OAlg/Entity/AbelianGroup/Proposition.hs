
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Entity.AbelianGroup.Proposition
-- Description : validity of abelian groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- validity of abelian groups.
module OAlg.Entity.AbelianGroup.Proposition
  ( prpAbelianGroups
  ) where

import OAlg.Prelude
import OAlg.Entity.AbelianGroup.KernelsAndCokernels

-- | validity for abelian groups.
prpAbelianGroups :: Statement
prpAbelianGroups = Prp "AbelianGroups"
  :<=>: And [ Label "isoSmithNormal" :<=>: Forall xStandard (valid . isoSmithNormal)
            , Label "kernels" :<=>: valid abhKernels
            ]
