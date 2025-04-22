
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , PolyKinds
  , DefaultSignatures
  , DataKinds
#-}

-- |
-- Module      : OAlg.Data.Variant
-- Description : concept of co- and contra.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- concept of co- and contra.
module OAlg.Data.Variant
  ( -- * Variant
    Variant(..), Variant2(..), toVariant2

    -- * Disjunctive
  , Disjunctive(..), Disjunctive2(..)
  ) where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Either

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

--------------------------------------------------------------------------------
-- Variant2 -

data Variant2 v h x y where
  Covariant2     :: h x y -> Variant2 Covariant h x y
  Contravariant2 :: h x y -> Variant2 Contravariant h x y

toVariant2 :: Disjunctive2 h
  => h x y -> Either2 (Variant2 Contravariant h) (Variant2 Covariant h) x y
toVariant2 h = case variant2 h of
  Contravariant -> Left2 (Contravariant2 h)
  Covariant     -> Right2 (Covariant2 h)
  
--------------------------------------------------------------------------------
-- Variant2 - Morphism -

instance Morphism h => Morphism (Variant2 v h) where
  type ObjectClass (Variant2 v h) = ObjectClass h
  homomorphous (Covariant2 h)     = homomorphous h
  homomorphous (Contravariant2 h) = homomorphous h

instance ApplicativeG t h c => ApplicativeG t (Variant2 v h) c where
  amapG (Covariant2 h)     = amapG h
  amapG (Contravariant2 h) = amapG h

