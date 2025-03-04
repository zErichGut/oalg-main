
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
  , PolyKinds
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
{-
    OpDuality(..)
  , OpReflexive(..), opdStructMlt
  , OpDualisable(..)
-}
  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude hiding (Reflexive)

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

{-
data Reflexive s o where
  Reflexive :: Applicative1 (IsoOp s) o => Reflexive s o

class CoObject d s where
  coObject :: d o -> Struct s x -> o x -> Dual o (Op x) 

class CoObject d s => OpDualisable d s where
  aa :: d o -> Struct s x -> d (Dual o)
  bb :: d o -> Struct s x -> Struct s (Op x)
  cc :: d o -> Struct s x -> Dual (Dual o) :~: o
  ee :: d o -> Struct s x -> IsoOp s (Op (Op x)) x
  rr :: d o -> Struct s x -> Reflexive s o

ff :: OpDualisable d s => d o -> Struct s x -> o x -> Dual (Dual o) (Op (Op x))
ff d s = coObject (aa d s) (bb d s) . coObject d s

hh :: Dual (Dual o) :~: o -> Dual (Dual o) y -> o y
hh Refl = id

gg :: OpDualisable d s => d o -> Struct s x -> o x -> o (Op (Op x))
gg d s o = hh (cc d s) (ff d s o)

ii :: OpDualisable d s => d o -> Struct s x -> Dual o (Op x) -> Dual (Dual o) (Op (Op x))
ii d s = coObject (aa d s) (bb d s)

jj :: OpDualisable d s => d o -> Struct s x -> Dual o (Op x) -> o (Op (Op x))
jj d s = hh (cc d s) . ii d s

kk :: OpDualisable d s => d o -> Struct s x -> Dual o (Op x) -> o x
kk d s = case rr d s of Reflexive -> amap1 (ee d s) . jj d s
-}

data Functor1 h c x y where
  Functor1 :: Functorial1 h c => h x y -> Functor1 h c x y

class (Cayleyan2 h, Transformable1 o s) => StructuralDualisable s d h o where
  coObject :: d h o c -> Struct s x -> c x -> Dual c (o x)
  aa :: d h o c -> Struct s x -> d h o (Dual c)
  cc :: d h o c -> Struct s x -> Dual (Dual c) :~: c
  ee :: d h o c -> Struct s x -> Functor1 h c x (o (o x))

hh :: Dual (Dual c) :~: c -> Dual (Dual c) x -> c x
hh Refl = id

coCoObject :: StructuralDualisable s d h o => d h o c -> Struct s x -> c x -> c (o (o x))
coCoObject d s = hh (cc d s) . coObject (aa d s) (tau1 s) . coObject d s where
{-  
ii :: StructuralDualisable s d h o => d h o c -> Struct s x -> Dual c (o x) -> Dual (Dual c) (o (o x))
ii d s = coObject (aa d s) (tau1 s)

jj :: StructuralDualisable s d h o => d h o c -> Struct s x -> Dual c (o x) -> c (o (o x))
jj d s = hh (cc d s) . ii d s
-}
coObjectInv :: StructuralDualisable s d h o => d h o c -> Struct s x -> Dual c (o x) -> c x
-- kk d s = amap1 (invert2 (ee d s)) . jj d s
coObjectInv d s = case ee d s of
  Functor1 i -> amap1 (invert2 i) . hh (cc d s) . coObject (aa d s) (tau1 s)

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
