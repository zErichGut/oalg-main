
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- | concept of 'Projective' and 'Injective'.
module OAlg.Limes.Perspective
  ( Perspective(..)
  ) where

import OAlg.Prelude

--------------------------------------------------------------------------------
-- Perspective -

-- | concept of 'Projective' and 'Injective'.
data Perspective = Projective | Injective deriving (Show,Eq,Ord,Enum,Bounded)

type instance Dual Projective = Injective
type instance Dual Injective = Projective
{-
instance Transposable Perspective where
  transpose Projective = Injective
  transpose Injective = Projective
-}
