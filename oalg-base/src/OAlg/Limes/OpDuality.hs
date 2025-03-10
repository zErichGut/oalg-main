
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
  , RankNTypes
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
    Functor1(..)
  , Duality1(..), toBidual1, fromDual1
  , prpBidual1
  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude hiding (Reflexive)

import OAlg.Data.Relation

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
-- Duality1 -

-- | duality for one-parameterized structures, where @__b__@ is the dual of @__a__@ and vice versa.
--
-- __Property__ Let @'Duality1' __s__ __d__ __i__ __o__@ then holds:
-- For all @__a__@, @__b__@, @__x__@, @d@ in @__d__ __i__ __o__ __a__ __b__@,
-- @s@ in @'Struct' __s__ __x__@ and @'Functor1' i = 'isoBidual1' d s@ holds:
-- @'toBidual1' d s a '==' 'amap1' i a@ for all @a@ in @__a__ __x__@.
class (Cayleyan2 i, Symmetric (d i o), Transformable1 o s)
  => Duality1 s d i o where
  -- | mapping to dual.
  toDual1    :: d i o a b -> Struct s x -> a x -> b (o x)

  -- | functor to bidual.
  isoBidual1 :: d i o a b -> Struct s x -> Functor1 i a x (o (o x))

--------------------------------------------------------------------------------
-- toBidual1 -

-- | mapping to bidual.
toBidual1 :: Duality1 s d i o => d i o a b -> Struct s x -> a x -> a (o (o x))
toBidual1 d s = toDual1 (swap d) (tau1 s) . toDual1 d s

--------------------------------------------------------------------------------
-- fromDual1 -
-- | mapping from dual.
fromDual1 :: Duality1 s d i o => d i o a b -> Struct s x -> b (o x) -> a x
fromDual1 d s = case isoBidual1 d s of Functor1 i -> amap1 (invert2 i) . toDual1 (swap d) (tau1 s)

--------------------------------------------------------------------------------
-- prpBidual1 -

-- | validity of the property of 'Duality1'.
prpBidual1 :: (Duality1 s d i o, Show (a x), Eq (a (o (o x))))
  => d i o a b -> Struct s x -> X (a x) -> Statement
prpBidual1 d s xa = Prp "Bidual1" :<=>: case isoBidual1 d s of
  Functor1 i -> Forall xa (\a -> (toBidual1 d s a == amap1 i a) :?> Params ["a":=show a])







{-
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
-}




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
