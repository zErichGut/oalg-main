
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
  (

    Functor1(..), TransformableDual1(..), ReflexiveDual1(..)
  , Duality1(..), fromBidual1, toBidual1, fromDual1
  , DiagramDuality(..), dgDuality
  , Dual1
  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude hiding (Reflexive)

import OAlg.Data.Either

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram hiding (DiagramDuality(..))
import OAlg.Entity.Natural

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Cone.Structure
import OAlg.Limes.Perspective

--------------------------------------------------------------------------------
-- Functor1 -

data Functor1 h c x y where
  Functor1 :: Functorial1 h c => h x y -> Functor1 h c x y

--------------------------------------------------------------------------------
-- TransformableDual1 -

-- class TransformableDual1 (d :: (Type -> Type) -> Type) where
class TransformableDual1 d where
  tauDual1 :: d c -> d (Dual1 c)

--------------------------------------------------------------------------------
-- ReflexiveDual1 -

class ReflexiveDual1 d where
  reflDual1 :: d c -> Dual1 (Dual1 c) :~: c

--------------------------------------------------------------------------------
-- Duality1 -

-- | duality for one-parameterized structures.
--
-- __Property__ Let @'Duality1' __s__ __d__ __i__ __o__@ then holds:
-- For all @__c__@, @__x__@, @d@ in @__d__ __i__ __o__ __c__@, @s@ in @'Struct' __s__ __x__@ and
-- @'Functor1' i = 'isoBidual1' d s@ holds:
-- @'toBidual1' d s c '==' 'amap1' i c@ for all @c@ in @__c__ __x__@.
class (Cayleyan2 i, Transformable1 o s, TransformableDual1 (d i o), ReflexiveDual1 (d i o))
  => Duality1 s d i o where
  toDual1    :: d i o c -> Struct s x -> c x -> Dual1 c (o x)
  isoBidual1 :: d i o c -> Struct s x -> Functor1 i c x (o (o x))


fromBidual1 :: Dual1 (Dual1 c) :~: c -> Dual1 (Dual1 c) x -> c x
fromBidual1 Refl = id

toBidual1 :: Duality1 s d i o => d i o c -> Struct s x -> c x -> c (o (o x))
toBidual1 d s = fromBidual1 (reflDual1 d) . toDual1 (tauDual1 d) (tau1 s) . toDual1 d s
{-  
ii :: Duality1 s d i o => d i o c -> Struct s x -> Dual1 c (o x) -> Dual1 (Dual1 c) (o (o x))
ii d s = toDual1 (tauDual11 d s) (tau1 s)

jj :: Duality1 s d i o => d i o c -> Struct s x -> Dual1 c (o x) -> c (o (o x))
jj d s = fromBidual1 (reflexive1 d s) . ii d s
-}
fromDual1 :: Duality1 s d i o => d i o c -> Struct s x -> Dual1 c (o x) -> c x
-- kk d s = amap1 (invert2 (isoBidual1 d s)) . jj d s
fromDual1 d s = case isoBidual1 d s of
  Functor1 i -> amap1 (invert2 i) . fromBidual1 (reflDual1 d) . toDual1 (tauDual1 d) (tau1 s)


--------------------------------------------------------------------------------
-- DiagramDuality -

data DiagramDuality s i o c where
  DiagramDuality :: Dual (Dual t) :~: t -> DiagramDuality s (IsoOp s) Op (Diagram t n m)

instance TransformableDual1 (DiagramDuality s i o) where
  tauDual1 (DiagramDuality Refl) = DiagramDuality Refl

instance ReflexiveDual1 (DiagramDuality s i o) where
  reflDual1 (DiagramDuality Refl) = Refl
  
instance (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => Functorial1 (IsoOp s) (Diagram t n m)

instance (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => Duality1 s (DiagramDuality s) (IsoOp s) Op where
  toDual1 (DiagramDuality _)    = const coDiagram
  isoBidual1 (DiagramDuality _) = Functor1 . isoToOpOpStruct


--------------------------------------------------------------------------------
-- dgDuality -

dgDuality :: p s a -> Diagram t n m a -> DiagramDuality s (IsoOp s) Op (Diagram t n m)
dgDuality _ = DiagramDuality . dgTypeRefl

--------------------------------------------------------------------------------
-- tauOrt -

tauOrt :: Transformable s Ort => Struct s x -> Struct Ort x
tauOrt = tau





{-

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

-}
