
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , PolyKinds
  , DefaultSignatures
#-}

-- |
-- Module      : OAlg.SDuality.Variant
-- Description : concept of co- and contra.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- concept of co- and contra.
module OAlg.SDuality.Variant
  ( -- * Variant
    Variant(..)

    -- * Disjunctive
  , Disjunctive(..), Disjunctive2(..)
  ) where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Number

--------------------------------------------------------------------------------
-- Variant -

-- | concept of co- and contravariant.
data Variant = Covariant | Contravariant
  deriving (Show,Read,Eq,Ord,Enum,Bounded)

instance Validable Variant where
  valid Covariant = SValid
  valid _         = SValid

instance Entity Variant

--------------------------------------------------------------------------------
-- Variant - Multiplicative -

instance Oriented Variant where
  type Point Variant = ()
  orientation _ = () :> ()

instance Multiplicative Variant where
  one _ = Covariant
  
  Covariant * v                 = v
  v * Covariant                 = v
  Contravariant * Contravariant = Covariant

  npower Covariant _                      = Covariant
  npower Contravariant n | n `mod` 2 == 0 = Covariant
                         | otherwise      = Contravariant

--------------------------------------------------------------------------------
-- Disjunctive -

-- type Disjunctive :: forall k . k -> Constraint

-- | object having two variants.
class Disjunctive x where
  variant :: x -> Variant

--------------------------------------------------------------------------------
-- Disjunctive2 -

class Disjunctive2 h where
  variant2 :: h x y -> Variant
  default variant2 :: Disjunctive (h x y) => h x y -> Variant
  variant2 = variant

instance Disjunctive2 h => Disjunctive2 (Path h) where
  variant2 (IdPath _) = Covariant
  variant2 (f :. p)   = variant2 f * variant2 p

instance Disjunctive2 h => Disjunctive (Path h x y) where
  variant = variant2
