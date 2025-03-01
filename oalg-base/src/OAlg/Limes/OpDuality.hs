
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
  ( OpDuality(..)
  , OpReflexive(..), opdStructMlt
  , OpDualisable(..)
  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Either

import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Cone.Structure
import OAlg.Limes.Perspective

--------------------------------------------------------------------------------
-- OpDuality -

-- | 'Op'-duality according to the index types @__l__@.
data OpDuality (l :: Type -> Perspective -> DiagramType -> N' -> N' -> Type -> Type) s x y where
  OpDuality
    :: Dual (Dual p) :~: p -> Dual (Dual t) :~: t
    -> OpDuality l s (l s p t n m) (l s (Dual p) (Dual t) n m)

--------------------------------------------------------------------------------
-- OpReflexive -

class OpReflexive c s where
  opdStructOp   :: c s a -> c s (Op a)
  opdConeStruct :: c s a -> ConeStruct s a
  opdRefl       :: c s a -> IsoOp s a (Op (Op a))

instance OpReflexive ConeStruct s where
  opdStructOp = cnStructOp
  
  opdConeStruct = id
  
  opdRefl ConeStructMlt = isoToOpOpMlt
  opdRefl ConeStructDst = isoToOpOpDst

--------------------------------------------------------------------------------
-- opdStructMlt -

opdStructMlt :: OpReflexive c s => c s a -> Struct Mlt a
opdStructMlt = cnStructMlt . opdConeStruct

--------------------------------------------------------------------------------
-- UniversalOpDualisable -

-- | 'Op'-dualisable type index types.
class OpReflexive c s => OpDualisable c l s where
  -- | mapping a /limes/ to 'Op'.
  opdToOp :: c s a -> OpDuality l s x y -> x a -> y (Op a)

  -- | mapping a /limes/ from 'Op'.
  opdFromOp :: c s a -> OpDuality l s x y -> y (Op a) -> x a

