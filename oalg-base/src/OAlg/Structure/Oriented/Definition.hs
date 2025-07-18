
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Structure.Oriented.Definition
-- Description : general definition of oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- General definition of 'Oriented' structures.
module OAlg.Structure.Oriented.Definition
  (
    -- * Oriented
    Oriented(..), isEndo, isEndoAt
  , Ort, tauOrt, TransformableOrt
  , module Pnt
  , module Orn

    -- * Duality
  
    -- ** Transposable
  , TransposableOriented

    -- * Extensional Equlity
  , EqualExtOrt, EqEOrt
  
    -- * X
  , OrtX
  )
  where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.Unify

import OAlg.Structure.Oriented.Point as Pnt
import OAlg.Structure.Oriented.Orientation as Orn

--------------------------------------------------------------------------------
-- Oriented -

-- | types with a 'Oriented' structure. The values of an 'Oriented' structure will
-- be called __/arrows/__ and the values of the associated 'Point' type __/points/__. To each
-- arrow there is a __/'start'/__ and a __/'end'/__ point assigned.
--
-- __Property__ Let __@q@__ be a type instance of the class 'Oriented', then holds:
--
-- (1) #Ort1#For all @a@ in __@q@__ holds: @'orientation' a '==' 'start' a ':>' 'end' a@.
--
-- __Note__
--
-- (1) If the types @__q__@ and @'Point' __q__@ are interpreted as sets
-- @__A__@ and @__P__@ and 'start', 'end' as functions from @__A__@ to @__P__@
-- then this structure forms a __/quiver/__ with __/arrows/__ in @__A__@
-- and __/points/__ in @__P__@.
-- 
-- (2) 'Morphism's can be interpreted as 'Oriented' structures via 'SomeMorphism'.
-- The bad thing about this is that we lose the check for /composability/ of two
-- 'Morphism's given by the type checker, but we gain all the functionality of
-- 'Oriented' structures, i.e we can define homomorphisms,
-- limits etc on 'Morphism's.
class (Entity q, EntityPoint q) => Oriented q where
  {-# MINIMAL orientation | (start,end) #-}
  
  -- | the orientation of an arrow.
  orientation :: q -> Orientation (Point q)
  orientation a = start a :> end a

  -- | the start point of an arrow.
  start :: q -> Point q
  start a = s where s :> _ = orientation a

  -- | the end point of an arrow.
  end :: q -> Point q
  end a = e where _ :> e = orientation a

--------------------------------------------------------------------------------
-- Oriented - Instance -

instance Oriented () where
  orientation _ = ():>()

instance Oriented Int where
  orientation _ = ():>()

instance Oriented Integer where
  orientation _ = ():>()

instance Oriented N where
  orientation _ = ():>()

instance Oriented Z where
  orientation _ = ():>()

instance Oriented Q where
  orientation _ = ():>()

instance Oriented x => Oriented (Id x) where
  orientation (Id x) = orientation x

instance Entity p => Oriented (Orientation p) where
  orientation = id

instance (Morphism m, TransformableObjectClassTyp m, Entity2 m) => Oriented (SomeMorphism m) where
  start (SomeMorphism f) = SomeObjectClass (domain f)
  end (SomeMorphism f) = SomeObjectClass (range f)

instance Entity x => Oriented (U x) where
  orientation (U _) = () :> ()

--------------------------------------------------------------------------------
-- isEndo -

-- | check for being an endo.
--
--  __Definition__ Let @__q__@ be a 'Oriented' structure, then an arrow @a@ in @__q__@
--  is called __/endo/__ if and only if @'start' a '==' 'end' a@.
isEndo :: Oriented q => q -> Bool
isEndo a = start a == end a

--------------------------------------------------------------------------------
-- isEndoAt -

-- | check for being an endo at the given point.
isEndoAt :: Oriented a => Point a -> a -> Bool
isEndoAt p a = orientation a == p :> p

--------------------------------------------------------------------------------
-- TransposableOriented -

-- | transposable oriented structures.
--
--  __Property__ Let @__q__@ be a 'TransposableOriented' structure, then holds:
--  For all @a@ in @__q__@ holds:
--  @'orientation' ('transpose' a) '==' 'opposite' ('orientation' a)@.
class (Transposable q, Oriented q) => TransposableOriented q

instance Entity p => TransposableOriented (Orientation p)

instance TransposableOriented N
instance TransposableOriented Z
instance TransposableOriented Q

--------------------------------------------------------------------------------
-- Ort -

-- | type representing the class of 'Oriented' structures.
data Ort

type instance Structure Ort x = Oriented x

instance Transformable Ort Typ where tau Struct = Struct
instance Transformable Ort Ent where tau Struct = Struct

instance Transformable Ort Type where tau _ = Struct
instance TransformableType Ort

--------------------------------------------------------------------------------
-- TransformableOrt -

-- | transformable to 'Oriented' structure.
class Transformable s Ort => TransformableOrt s

instance TransformableTyp Ort
instance TransformableOrt Ort

--------------------------------------------------------------------------------
-- tauOrt -

-- | transforming to 'Ort'.
tauOrt :: Transformable s Ort => Struct s x -> Struct Ort x
tauOrt = tau

--------------------------------------------------------------------------------
-- OrtX -

-- | type representing the class of 'Oriented' structures with associated standard random
-- variables.
data OrtX

type instance Structure OrtX x
  = (Oriented x, XStandard x, XStandardPoint x)

instance Transformable OrtX XStd where tau Struct = Struct

instance Transformable OrtX Typ where tau Struct = Struct
instance TransformableTyp OrtX

instance Transformable OrtX Ort where tau Struct = Struct
instance TransformableOrt OrtX 
instance TransformableG Id OrtX EqE where tauG Struct = Struct
instance TransformableG Pnt OrtX EqE where tauG Struct = Struct
instance Transformable OrtX Type where tau _ = Struct
instance TransformableType OrtX

--------------------------------------------------------------------------------
-- EqEOrt

-- | type representing extensional equality for 'Oriented' structures.
data EqEOrt

type instance Structure EqEOrt x
  = (Show x, ShowPoint x, Eq x, EqPoint x, XStandard x, XStandardPoint x) 

--------------------------------------------------------------------------------
-- EqualExtOrt -

-- | category of extensional equality for 'Oriented' structures.
type EqualExtOrt = Sub EqEOrt (->)

instance EqExt EqualExtOrt where
  Sub f .=. Sub g = prpEqualExt xStandard f g

instance Transformable OrtX EqEOrt where tau Struct = Struct
instance TransformableObjectClass OrtX EqualExtOrt

instance TransformableG Id OrtX EqEOrt where tauG Struct = Struct
instance TransformableGObjectClassRange Id OrtX EqualExtOrt

instance TransformableG Pnt OrtX EqEOrt where tauG Struct = Struct
instance TransformableGObjectClassRange Pnt OrtX EqualExtOrt

instance Transformable EqEOrt Type where tau _ = Struct
