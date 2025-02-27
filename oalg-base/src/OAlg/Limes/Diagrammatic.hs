
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , TypeOperators
  , DataKinds
#-}

-- |
-- Module      : OAlg.Limes.Diagrammatic
-- Description : objects having an underlying diagram.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Objects having an underlying 'Diagram'.
module OAlg.Limes.Diagrammatic
  ( Diagrammatic(..)
  ) where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Entity.Diagram

-- | object @__d__@ having an underlying 'Diagram'.
class Oriented a => Diagrammatic d t n m a where
  diagram :: d t n m a -> Diagram t n m a

instance Oriented a => Diagrammatic Diagram t n m a where diagram = id



