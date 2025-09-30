
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Limes.Limits
-- Description : limits of diagrammatic objects.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- limits of diagrammatic objectss, i.e. assigning to each diagrammatic object a
-- limes according to it. (see "OAlg.Entity.Diagram.Diagrammatic").
module OAlg.Limes.Limits
  (
    -- * Limits
    limes, LimitsG(..), Limits
  , limesCone, limitsCone

    -- * Constructions
  , lmsMltPrjOrnt, lmsMltInjOrnt
  
    -- * Duality
  , module Dl

    -- * Proposition
  , module Prp
  ) where

import OAlg.Limes.Limits.Core
import OAlg.Limes.Limits.Duality as Dl
import OAlg.Limes.Limits.Proposition as Prp

