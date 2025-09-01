
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Limes.Definition
-- Description : definition of a limes over a digrammatic object.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Definition of a 'Limes' over a 'Diagrammatic' object yielding a 'Conic' object.
module OAlg.Limes.Definition
  (
    -- * Limes
    Limes, LimesG(..)
  , universalCone, universalFactor
  , eligibleCone, eligibleFactor
  , lmDiagramTypeRefl
  
    -- * Constructions
  , lmMltPrjOrnt, lmMltInjOrnt  

    -- * Duality
  , module Dl

    -- * Proposition
  , module Prp
  ) where

import OAlg.Limes.Definition.Core
import OAlg.Limes.Definition.Duality as Dl
import OAlg.Limes.Definition.Proposition as Prp
