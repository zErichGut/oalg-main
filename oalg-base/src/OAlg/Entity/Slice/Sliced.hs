
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds, RankNTypes #-}

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
    Sliced(..), sliceIndex

    -- * Hom
  , HomSlicedOriented, Sld
  , sliceIndexDomain, sliceIndexRange
  , sldHom
  , toDualOpOrtSld, toDualOpOrtSld'

  , HomSlicedMultiplicative
  , toDualOpMltSld, toDualOpMltSld'  
    -- * IsoO

    -- * Proposition
  , prpHomSlicedOriented
  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Singleton
import OAlg.Data.Proxy

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative

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
-- sliceIndex -

sliceIndex :: Sliced i x => q i x -> i x
sliceIndex _ = unit1

--------------------------------------------------------------------------------
-- Sld -

data Sld (i :: Type -> Type)

type instance Structure (Sld i) x = Sliced i x

--------------------------------------------------------------------------------
-- HomSlicedOriented -

-- | homomorphisms between 'Sliced' structures, i.e homomorphisms between 'Oriented' structures where
-- 'pmap' preserves the distinguished point.
--
-- __Property__ Let @'HomSlicedOriented' __i__ __h__@, then holds:
--
-- (1) For all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
-- @'pmap' h px '==' py@, where @px = 'slicePoint' '$' 'sliceIndexDomain' '$' 'sldHom' q h@,
-- @py = 'slicePoint' '$' 'sliceIndexRange' '$' 'sldHom' q h@ and @q@ is any proxy in @__q i__@.
class (HomOrientedDisjunctive h, Transformable (ObjectClass h) (Sld i)) => HomSlicedOriented i h

--------------------------------------------------------------------------------
-- sliceIndexDomain -
-- | the slice index for the 'domain'.
sliceIndexDomain :: Homomorphous (Sld i) x y -> i x
sliceIndexDomain (Struct :>: _) = unit1

--------------------------------------------------------------------------------
-- sliceIndexRange -

-- | the slice index for the 'range'.
sliceIndexRange :: Homomorphous (Sld i) x y -> i y
sliceIndexRange (_ :>: Struct) = unit1

--------------------------------------------------------------------------------
-- sldHom -

-- | the induced homomorphous structure.
sldHom :: HomSlicedOriented i h => q i -> h x y -> Homomorphous (Sld i) x y
sldHom _ h = tauHom (homomorphous h)

--------------------------------------------------------------------------------
-- prpHomSlicedOriented -

relHomSlicedOriented :: (HomSlicedOriented i h, Show2 h)
  => Homomorphous Ort x y -> Homomorphous (Sld i) x y -> h x y -> Statement
relHomSlicedOriented (Struct:>:Struct) hSld@(Struct:>:Struct) h
  = (pmap h px == py) :?> Params [ "h":=show2 h
                                 , "px":= show px
                                 , "py":=show py
                                 ] 
    where
      px = slicePoint $ sliceIndexDomain hSld
      py = slicePoint $ sliceIndexRange hSld

-- | validity according to 'HomSlicedOriented'.
prpHomSlicedOriented :: (HomSlicedOriented i h, Show2 h)
  => q i -> h x y -> Statement
prpHomSlicedOriented q h = Prp "HomSlicedOriented"
  :<=>: relHomSlicedOriented (tauHom $ homomorphous h) (sldHom q h) h

--------------------------------------------------------------------------------
-- IsoO - HomSlicedOriented -

instance Transformable s Ort => Transformable (s,Sld i) Ort where
  tau = tau . tauFst

instance Transformable s Mlt => Transformable (s,Sld i) Mlt where
  tau = tau . tauFst
  
instance Transformable s Ort => TransformableOrt (s,Sld i)
instance TransformableMlt s  => TransformableMlt (s,Sld i)

instance Transformable (s,Sld i) Type where tau _ = Struct

instance TransformableType (s,Sld i)

tauOpSld :: (Struct s x -> Struct s (Op x)) -> Struct (s,Sld i) x -> Struct (s,Sld i) (Op x)
tauOpSld tauOp s = case (s,tauOp $ tauFst s) of (Struct,Struct) -> Struct

instance TransformableG Op s s => TransformableG Op (s,Sld i) (s,Sld i) where tauG = tauOpSld tauOp

instance TransformableGRefl Op s => TransformableGRefl Op (s,Sld i)

instance TransformableGRefl Op s => TransformableOp (s,Sld i)

instance
  ( Transformable s Ort
  , TransformableGRefl Op s
  )
  => HomSlicedOriented i (HomDisjEmpty (s,Sld i) Op)

instance
  ( Transformable s Ort
  , TransformableGRefl Op s
  )
  => HomSlicedOriented i (IsoO (s,Sld i) Op)

--------------------------------------------------------------------------------
-- toDualOpOrtSld -

toDualOpOrtSld :: Sliced i x => Variant2 Contravariant (IsoO (Ort,Sld i) Op) x (Op x)
toDualOpOrtSld = toDualO Struct

toDualOpOrtSld' :: Sliced i x => q i -> Variant2 Contravariant (IsoO (Ort, Sld i) Op) x (Op x)
toDualOpOrtSld' _ = toDualOpOrtSld

--------------------------------------------------------------------------------
-- HomSlicedMultiplicative -

type HomSlicedMultiplicative i h = (HomSlicedOriented i h, HomMultiplicativeDisjunctive h)

--------------------------------------------------------------------------------
-- toDualOpMltSld -

toDualOpMltSld :: (Sliced i x, Multiplicative x)
  => Variant2 Contravariant (IsoO (Mlt,Sld i) Op) x (Op x)
toDualOpMltSld = toDualO Struct

toDualOpMltSld' :: (Sliced i x, Multiplicative x)
  => q i -> Variant2 Contravariant (IsoO (Mlt,Sld i) Op) x (Op x)
toDualOpMltSld' _ = toDualOpMltSld

