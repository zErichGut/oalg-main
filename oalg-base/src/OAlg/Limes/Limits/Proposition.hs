
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

-- |
-- Module      : OAlg.Limes.Limits.Proposition
-- Description : propositions for limits.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- duality for 'LimitsG'.
module OAlg.Limes.Limits.Proposition
  (
    -- * Proposition
    prpLimitsG
  ) where

import OAlg.Prelude

import OAlg.Entity.Diagram

import OAlg.Limes.Cone
import OAlg.Limes.Definition

import OAlg.Limes.Limits.Core

--------------------------------------------------------------------------------
-- prpLimitsG -

-- | validity according to 'LimitsG'.
prpLimitsG ::
  ( Conic c
  , Diagrammatic d
  , Entity (d t n m x)
  , Entity x
  )
  => XEligibleCone c s p d t n m x
  -> XEligibleConeFactor c s p d t n m x
  -> X (d t n m x)
  -> LimitsG c s p d t n m x
  -> Statement
prpLimitsG xec xef xd l = Prp "LimitsG" :<=>: Forall xd (prpLimes xec xef . limes l)

--------------------------------------------------------------------------------
-- LimitsG - Validable -

instance
  ( Conic c
  , Diagrammatic d
  , XStandardEligibleCone c s p d t n m x
  , XStandardEligibleConeFactor c s p d t n m x
  , XStandard (d t n m x)
  , Entity (d t n m x)
  , Entity x
  )
  => Validable (LimitsG c s p d t n m x) where
  valid = prpLimitsG xStandardEligibleCone xStandardEligibleConeFactor xStandard


