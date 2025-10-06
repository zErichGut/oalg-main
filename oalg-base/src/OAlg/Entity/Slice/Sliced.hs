
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
    
    -- ** Oriented
  , HomOrientedSliced, Sld
  , sliceIndexDomain, sliceIndexRange
  , sldHom
  , toDualOpOrtSld, toDualOpOrtSld'

    -- ** Multiplicative
  , HomMultiplicativeSliced
  , toDualOpMltSld, toDualOpMltSld'

    -- ** Distributive
  , HomDistributiveSliced
  , toDualOpDstSld, toDualOpDstSld'
  
    -- * Proposition
  , prpHomOrientedSliced

  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
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
-- sliceIndex -

-- | the slice index according to the proxy type.
sliceIndex :: Sliced i x => q i x -> i x
sliceIndex _ = unit1

--------------------------------------------------------------------------------
-- Sld -

-- | type index for 'Sliced' structures.
data Sld (i :: Type -> Type)

type instance Structure (Sld i) x = Sliced i x

--------------------------------------------------------------------------------
-- HomOrientedSliced -

-- | homomorphisms between 'Sliced' structures, i.e homomorphisms between 'Oriented' structures where
-- 'pmap' preserves the distinguished point.
--
-- __Property__ Let @'HomOrientedSliced' __i__ __h__@, then holds:
--
-- (1) For all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
-- @'pmap' h px '==' py@, where @px = 'slicePoint' '$' 'sliceIndexDomain' '$' 'sldHom' q h@,
-- @py = 'slicePoint' '$' 'sliceIndexRange' '$' 'sldHom' q h@ and @q@ is any proxy in @__q i__@.
class (HomOrientedDisjunctive h, Transformable (ObjectClass h) (Sld i)) => HomOrientedSliced i h

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
sldHom :: HomOrientedSliced i h => q i -> h x y -> Homomorphous (Sld i) x y
sldHom _ h = tauHom (homomorphous h)

--------------------------------------------------------------------------------
-- prpHomOrientedSliced -

relHomOrientedSliced :: (HomOrientedSliced i h, Show2 h)
  => Homomorphous Ort x y -> Homomorphous (Sld i) x y -> h x y -> Statement
relHomOrientedSliced (Struct:>:Struct) hSld@(Struct:>:Struct) h
  = (pmap h px == py) :?> Params [ "h":=show2 h
                                 , "px":= show px
                                 , "py":=show py
                                 ] 
    where
      px = slicePoint $ sliceIndexDomain hSld
      py = slicePoint $ sliceIndexRange hSld

-- | validity according to 'HomOrientedSliced'.
prpHomOrientedSliced :: (HomOrientedSliced i h, Show2 h)
  => q i -> h x y -> Statement
prpHomOrientedSliced q h = Prp "HomOrientedSliced"
  :<=>: relHomOrientedSliced (tauHom $ homomorphous h) (sldHom q h) h

--------------------------------------------------------------------------------
-- IsoO - HomOrientedSliced -

instance Transformable (s,Sld i) Type where tau _ = Struct

instance TransformableType (s,Sld i)

instance Transformable (s,Sld i) (Sld i) where tau = tauSnd

instance Transformable s Ort => Transformable (s,Sld i) Ort where tau = tau . tauFst
instance Transformable s Ort => TransformableOrt (s,Sld i)

instance Transformable s Mlt => Transformable (s,Sld i) Mlt where tau = tau . tauFst
instance TransformableMlt s => TransformableMlt (s,Sld i)

instance Transformable s Fbr => Transformable (s,Sld i) Fbr where tau = tau . tauFst
instance TransformableFbr s => TransformableFbr (s,Sld i)

instance Transformable s Add => Transformable (s,Sld i) Add where tau = tau . tauFst
instance TransformableAdd s => TransformableAdd (s,Sld i)

instance Transformable s FbrOrt => Transformable (s,Sld i) FbrOrt where tau = tau . tauFst
instance TransformableFbrOrt s => TransformableFbrOrt (s,Sld i)

instance Transformable s Dst => Transformable (s,Sld i) Dst where tau = tau . tauFst
instance TransformableDst s => TransformableDst (s,Sld i)


instance TransformableG Op (Sld i) (Sld i) where tauG Struct = Struct
instance TransformableG Op (s,Sld i) (Sld i) where tauG = tauG . tauSnd

instance TransformableOp (Ort,Sld i)
instance TransformableGRefl Op (Ort,Sld i)

instance TransformableOp (Mlt,Sld i)
instance TransformableGRefl Op (Mlt,Sld i)

instance TransformableOp (Dst,Sld i)
instance TransformableGRefl Op (Dst,Sld i)

instance Transformable (s,Sld i) s
  => TransformableObjectClass (s,Sld i) (HomDisjEmpty s Op)

instance
  ( Transformable s Ort
  , TransformableOp (s,Sld i)
  )
  => HomOrientedSliced i (HomDisjEmpty (s,Sld i) Op)

instance (CategoryDisjunctive h, HomOrientedSliced i h) => HomOrientedSliced i (Inv2 h)

instance
  ( TransformableOrt s
  , TransformableType s
  , TransformableOp s
  ) => HomOrientedSliced i (Sub (s,Sld i) (HomDisjEmpty s Op))

instance
  ( TransformableOrt s
  , TransformableType s
  , TransformableOp s
  )
  => HomOrientedSliced i (Sub (s,Sld i) (IsoO s Op))

--------------------------------------------------------------------------------
-- toDualOpOrtSld -

-- | contravariant isomorphism on 'Sliced' 'Oriented' structures. 
toDualOpOrtSld :: Sliced i x => Variant2 Contravariant (IsoO (Ort,Sld i) Op) x (Op x)
toDualOpOrtSld = toDualO Struct

-- | contravariant isomorphism on 'Sliced' 'Oriented' structures according to the proxy type.
toDualOpOrtSld' :: Sliced i x => q i -> Variant2 Contravariant (IsoO (Ort, Sld i) Op) x (Op x)
toDualOpOrtSld' _ = toDualOpOrtSld

--------------------------------------------------------------------------------
-- HomMultiplicativeSliced -

-- | disjunctive multiplicative homomorphism respecting the slice structure.
type HomMultiplicativeSliced i h = (HomOrientedSliced i h, HomMultiplicativeDisjunctive h)

--------------------------------------------------------------------------------
-- toDualOpMltSld -

-- | contravariant isomorphism on 'Sliced' 'Multiplicative' structures. 
toDualOpMltSld :: (Sliced i x, Multiplicative x)
  => Variant2 Contravariant (IsoO (Mlt,Sld i) Op) x (Op x)
toDualOpMltSld = toDualO Struct

-- | contravariant isomorphism on 'Sliced' 'Multiplicative' structures according to the proxy type.
toDualOpMltSld' :: (Sliced i x, Multiplicative x)
  => q i -> Variant2 Contravariant (IsoO (Mlt,Sld i) Op) x (Op x)
toDualOpMltSld' _ = toDualOpMltSld

--------------------------------------------------------------------------------
-- HomDistributiveSliced -

-- | disjunctive distributive homomorphism respecting the slice structure.
type HomDistributiveSliced i h = (HomOrientedSliced i h, HomDistributiveDisjunctive h)

-- | contravariant isomorphism on 'Sliced' 'Distributive' structures. 
toDualOpDstSld :: (Sliced i x, Distributive x)
  => Variant2 Contravariant (IsoO (Dst,Sld i) Op) x (Op x)
toDualOpDstSld = toDualO Struct

-- | contravariant isomorphism on 'Sliced' 'Distributive' structures according to the proxy type.
toDualOpDstSld' :: (Sliced i x, Distributive x)
  => q i -> Variant2 Contravariant (IsoO (Dst,Sld i) Op) x (Op x)
toDualOpDstSld' _  = toDualOpDstSld

  
