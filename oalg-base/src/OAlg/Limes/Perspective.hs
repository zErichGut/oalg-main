
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Perspective
-- Description : concept of perspective
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- concept of 'Projective' and 'Injective'.
module OAlg.Limes.Perspective
  ( Perspective(..), DualPerspective
  ) where

import OAlg.Prelude

--------------------------------------------------------------------------------
-- Perspective -

-- | concept of 'Projective' and 'Injective'.
data Perspective = Projective | Injective deriving (Show,Eq,Ord,Enum,Bounded)

type family DualPerspective p where
  DualPerspective Projective = Injective
  DualPerspective Injective  = Projective

{-
type instance Dual Projective = Injective
type instance Dual Injective = Projective
-}

type instance ToSite Projective = To
type instance ToSite Injective  = From


