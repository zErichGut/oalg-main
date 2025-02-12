
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
-- Module      : OAlg.Limes.OpDuality
-- Description : definition of Op-duality.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of 'Op'-duality.
module OAlg.Limes.OpDuality
  ( OpDuality(..), OpDualisable(..)
  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Diagram
import OAlg.Entity.Natural

import OAlg.Limes.Cone.Structure
import OAlg.Limes.Perspective

--------------------------------------------------------------------------------
-- OpDuality -

-- | 'Op'-duality between according to the index types @__l__@.
data OpDuality (l :: Type -> Perspective -> DiagramType -> N' -> N' -> Type -> Type) s f f' where
  OpDuality
    :: f  :~: l s p t n m
    -> f' :~: l s (Dual p) (Dual t) n m
    -> Dual (Dual p) :~: p
    -> Dual (Dual t) :~: t
    -> OpDuality l s f f'


--------------------------------------------------------------------------------
-- UniversalOpDualisable -

class OpDualisable l s where
  opdToOp   :: ConeStruct s a -> OpDuality l s f f' -> f a -> f' (Op a)
  opdFromOp :: ConeStruct s a -> OpDuality l s f f' -> f' (Op a) -> f a

