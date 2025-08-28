
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Entity.Slice.Sliced
-- Description : oriented structures with a distinguished point.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- 'Oriented' structures with a distinguished 'Point'.
module OAlg.Entity.Slice.Sliced
  (

    -- * Sliced
    Sliced(..), TransformableSld

    -- * Hom
  , HomSliced, Sld

  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Singleton

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive

import OAlg.Hom.Definition
import OAlg.Hom.Oriented

import OAlg.Data.Symbol

--------------------------------------------------------------------------------
-- Sliced -

-- | Slicing 'Oriented' structures at a distinguished 'Point', given by the type of the index
--  __@i@__. 
--
--  __Note__ The constraint @'Singleton1' __i__@ ensures that the distinguished point
--  depends only on the type __@i c@__.
class (Entity1 i, Singleton1 i, Oriented c) => Sliced i c where
  -- | the distingueished point of the given index type @__i__@.
  slicePoint :: i c -> Point c

instance Sliced i c => Sliced i (Op c) where
  slicePoint i = to i $ slicePoint $ fo i where
    
    fo :: Singleton1 i => i (f c) -> i c
    fo _ = unit1

    to :: Point c ~ Point (f c) => p (f c) -> Point c -> Point (f c)
    to _ = id

instance Sliced Proxy OS where
  slicePoint _ = P

--------------------------------------------------------------------------------
-- Sld -

-- | type representing the class of 'Sliced' structures.
data Sld s (i :: Type -> Type) 

type instance Structure (Sld s i) x = (Sliced i x, Structure s x)

--------------------------------------------------------------------------------
-- TransformableSld -

-- | helper class to circumvent @UndecidableInstances@.
class Transformable (Sld s i) (Sld t i) => TransformableSld i s t

instance TransformableSld i s s
instance TransformableSld i Mlt Ort

--------------------------------------------------------------------------------
-- sldStruct -

-- | the underlying 'Structure' of the 'Sliced'-'Structure'.
sldStruct :: Struct (Sld s i) x -> Struct s x
sldStruct Struct = Struct

instance Transformable1 Op s => TransformableG Op (Sld s i) (Sld s i) where
  tauG s@Struct = case tauOp (sldStruct s) of Struct -> Struct

instance TransformableOp s => TransformableOp (Sld s i)

instance Transformable (Sld s i) Ort where tau Struct = Struct
instance TransformableOrt (Sld s i)

instance Transformable (Sld s i) Typ where tau Struct = Struct
instance TransformableTyp (Sld s i)

instance Transformable s Mlt => Transformable (Sld s i) Mlt where
  tau s@Struct = case tauMlt (sldStruct s) of Struct -> Struct
instance Transformable s Mlt => TransformableMlt (Sld s i)

instance Transformable s Fbr => Transformable (Sld s i) Fbr where
  tau s@Struct = case tauFbr (sldStruct s) of Struct -> Struct
instance Transformable s Fbr => TransformableFbr (Sld s i)

instance Transformable s Add => Transformable (Sld s i) Add where
  tau s@Struct = case tauAdd (sldStruct s) of Struct -> Struct
instance (Transformable s Fbr, Transformable s Add) => TransformableAdd (Sld s i)

instance Transformable s FbrOrt => Transformable (Sld s i) FbrOrt where
  tau s@Struct = case tauFbrOrt (sldStruct s) of Struct -> Struct
instance (Transformable s Fbr, Transformable s FbrOrt) => TransformableFbrOrt (Sld s i)

instance Transformable s Dst => Transformable (Sld s i) Dst where
  tau s@Struct = case tauDst (sldStruct s) of Struct -> Struct
instance ( Transformable s Fbr, Transformable s FbrOrt, Transformable s Add
         , Transformable s Mlt, Transformable s Dst
         ) => TransformableDst (Sld s i)
  
instance Transformable (Sld Mlt i) (Sld Ort i) where tau Struct = Struct
instance Transformable (Sld Dst i) (Sld Mlt i) where tau Struct = Struct
instance TransformableSld i Dst Mlt

--------------------------------------------------------------------------------
-- HomSliced -

-- | homomorphisms between 'Sliced' structures, i.e homomorphisms between 'Oriented' structures where
-- 'pmap' preserves the distinguished point.
--
-- __Property__ Let @__h__@ be in instance of @'HomSliced' __i__ __h__@, then holds:
--
-- (1) For all @__a__@, @__b__@ and @h@ in @__h__ __a__ __b__@ holds:
-- @'pmap' h ('slicePoint' i) '==' 'slicePioint' ('singelton1' i)@, where @i@ is in @__i__ __a__@.
class (HomOrientedDisjunctive h, Transformable (ObjectClass h) (Sld s i)) => HomSliced s i h

type instance Hom (Sld s i) h = (HomSliced s i h, Hom s h)

--------------------------------------------------------------------------------
-- Path - HomSliced -

instance HomSliced s i h => HomSliced s i (Path h)

{-
--------------------------------------------------------------------------------
-- Forget - HomSliced -

instance (HomSliced t i h, TransformableOp t, TransformableSld i t s)
  => HomSliced s i (Forget (Sld t i) h)
-}

{-
--------------------------------------------------------------------------------
-- IdHom - HomSliced -

instance (Transformable1 Op t, TransformableSld i t s) => HomSliced s i (IdHom (Sld t i))

--------------------------------------------------------------------------------
-- IsoOp - HomSliced -

instance (Transformable1 Op t, TransformableSld i t s) => HomSliced s i (IsoOp (Sld t i))
-}

instance Transformable (Sld t i) Type where
  tau _ = Struct
  
instance TransformableType (Sld t i)

instance
  ( TransformableOp t
  , TransformableSld i t s
  )
  => HomSliced s i (HomDisjEmpty (Sld t i) Op)

{-
--------------------------------------------------------------------------------
-- Forget' - HomSliced -

instance ( HomSliced t i h
         , TransformableSld i t s
         , TransformableOp t
         ) => HomSliced s i (Forget' (Sld t i) h)
-}

