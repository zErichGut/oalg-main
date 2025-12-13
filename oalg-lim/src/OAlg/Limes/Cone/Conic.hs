
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Limes.Cone.Conic
-- Description : objects with a naturally underlying cone.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- objects with a naturally underlying cone.
module OAlg.Limes.Cone.Conic
  (
    -- * Conic
    Conic(..)
  , ConeG(..)

    -- * Natural
  , NaturalConic
  , crohS

    -- * Duality
  , module Dl
  ) where

import OAlg.Limes.Cone.Conic.Core
import OAlg.Limes.Cone.Conic.Duality as Dl
