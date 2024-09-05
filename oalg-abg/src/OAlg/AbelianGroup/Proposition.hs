
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
  ( prpAbelianGroups
  ) where

import OAlg.Prelude

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels
import OAlg.AbelianGroup.Liftable
--------------------------------------------------------------------------------
-- prpAbelianGroups -

-- | validity for abelian groups.
prpAbelianGroups :: Statement
prpAbelianGroups = Prp "AbelianGroups"
  :<=>: And [ prpAbHom
            , Label "isoSmithNormal" :<=>: Forall xStandard (valid . isoSmithNormal)
            , Label "kernels" :<=>: valid abhKernels
            , Label "cokernels liftable" :<=>: valid abhCokernelLftFree
            , prpMatrixZLiftable
            ]


