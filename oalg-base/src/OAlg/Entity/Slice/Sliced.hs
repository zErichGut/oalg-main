
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
    Sliced(..)

    -- * Hom
  , HomSliced, Sld
  , IsoSlice

    -- * IsoOp
  -- , isoToOpOpSld, isoFromOpOpSld
  
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
import OAlg.Structure.Additive

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Distributive

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


sldStruct :: Struct (Sld s i) x -> Struct s x
sldStruct Struct = Struct

tauOp :: Transformable1 Op s => Struct s x -> Struct s (Op x)
tauOp = tau1

tauMlt :: Transformable s Mlt => Struct s x -> Struct Mlt x
tauMlt = tau

tauFbr :: Transformable s Fbr => Struct s x -> Struct Fbr x
tauFbr = tau

tauFbrOrt :: Transformable s FbrOrt => Struct s x -> Struct FbrOrt x
tauFbrOrt = tau

tauAdd :: Transformable s Add => Struct s x -> Struct Add x
tauAdd = tau

tauDst :: Transformable s Dst => Struct s x -> Struct Dst x
tauDst = tau

instance Transformable1 Op s => Transformable1 Op (Sld s i) where
  tau1 s@Struct = case tauOp (sldStruct s) of Struct -> Struct

instance Transformable1 Op s => TransformableOp (Sld s i)

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

--------------------------------------------------------------------------------
-- HomSliced -

-- | homomorphisms between 'Sliced' structures, i.e homomorphisms between 'Oriented' structures where
-- 'pmap' preserves the distinguished point.
--
-- __Property__ Let @__h__@ be in instance of @'HomSliced' __i__ __h__@, then holds:
--
-- (1) For all @__a__@, @__b__@ and @h@ in @__h__ __a__ __b__@ holds:
-- @'pmap' h ('slicePoint' i) '==' 'slicePioint' ('singelton1' i)@, where @i@ is in @__i__ __a__@.
class (HomOriented h, Transformable (ObjectClass h) (Sld s i)) => HomSliced s i h


instance HomSliced s i h => HomSliced s i (Path h)

instance (HomSliced t i h, Transformable1 Op t, Transformable (Sld t i) (Sld s i))
  => HomSliced s i (Forget (Sld t i) h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom (Sld s i) h = HomSliced s i h

--------------------------------------------------------------------------------
-- IsoSliced -

type IsoSlice s i h = (FunctorialHomOriented h, Cayleyan2 h, HomSliced s i h)

--------------------------------------------------------------------------------
-- IdHom - HomSliced -

instance Transformable1 Op s => HomSliced s i (IdHom (Sld s i))


--------------------------------------------------------------------------------
-- IsoOp - HomSliced -

instance Transformable1 Op s => HomSliced s i (IsoOp (Sld s i))


ff :: (HomSliced Dst i h, HomDistributive h) => i a -> h (Op (Op a)) a -> N
ff = error "nyi"

gg :: (Sliced i a, Distributive a) => i a -> IsoOp (Sld Dst i) (Op (Op a)) a
gg _ = isoFromOpOp


hh :: (Sliced i a, Distributive a) => i a -> N
hh i = ff i (gg i)




{-
isoFromOpOpSld :: Sliced i a => IsoOp (Sld Ort i) (Op (Op a)) a
isoFromOpOpSld = make (FromOpOp :. IdPath Struct)


isoToOpOpSld :: Sliced s i a => IsoOp (Sld s i) a (Op (Op a))
isoToOpOpSld = make (ToOpOp :. IdPath Struct)
-}
