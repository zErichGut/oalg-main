
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
           , DefaultSignatures
#-}


-- |
-- Module      : OAlg.Homology.IO.Interactive
-- Description : pretty printing of values
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- pretty printing of values
module OAlg.Homology.IO.Pretty
  ( Pretty(..)
  ) where

import Data.List ((++))

import OAlg.Prelude

import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum

-- import OAlg.Structure.Fibred
-- import OAlg.Structure.Additive
-- import OAlg.Structure.Multiplicative
-- import OAlg.Structure.Vectorial
-- import OAlg.Structure.Exception

import OAlg.AbelianGroup.Definition

--------------------------------------------------------------------------------
-- Pretty -

-- | pretty printing of values
class Pretty x where
  pshow :: x -> String
  default pshow :: Show x => x -> String
  pshow = show

instance Pretty N
instance Pretty Z

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pshow (Left a)  = "Left (" ++ pshow a ++ ")"
  pshow (Right b) = "Right (" ++ pshow b ++ ")"

instance Pretty AbGroup
