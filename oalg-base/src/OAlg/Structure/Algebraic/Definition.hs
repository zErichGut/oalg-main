
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Structure.Algebraic.Definition
-- Description : definition of algebraic structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of algebraic structures, i.e. 'Distributive' structures with a suitable
-- 'Vectorial' structure.
module OAlg.Structure.Algebraic.Definition
  ( -- * Algebraic
    Algebraic, Alg, TransformableAlg

    -- * Algebraic Semiring
  , AlgebraicSemiring, AlgebraicRing, AlgebraicField
  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Distributive.Definition
import OAlg.Structure.Vectorial.Definition
import OAlg.Structure.Ring.Definition

--------------------------------------------------------------------------------
-- Algebraic -

-- | 'Distributive' structures with a suitable 'Vectorial' structure.
--
--  __Property__ Let __@a@__ be a 'Algebraic' structure, then holds:
--
--  (1) #Alg1#For all @r@ in @'Scalar' __a__@ and @a@, @b@ in @__a__@ with
--  @'start' a '==' 'end' b@ holds: @r'!'(a'*'b) '==' (r'!'a)'*'b@ and
--  @r'!'(a'*'b) '==' a'*'(r'!'b)@.
class (Distributive a, Vectorial a) => Algebraic a

instance Algebraic ()
instance Algebraic Int
instance Algebraic Integer
instance Algebraic N
instance Algebraic Z
instance Algebraic Q
instance Entity p => Algebraic (Orientation p)
instance Algebraic a => Algebraic (Op a)

--------------------------------------------------------------------------------
-- AlgebraicSemiring -

-- | 'Commutative' 'Semiring's with a sound 'Algebraic' structure.
--
-- __Property__ Let @__r__@ be an instance of 'AlgebraicSemiring', then holds:
--
-- (1) For all @x@ and @y@ in @__r__@ holds: @x '!' y '==' x '*' y@.
--
-- __Note__
--
-- (1) The purpose of this structure is on the one hand to summarize the somewhat lengthy
-- constraints and on the other hand to ensure that the scalar multiplication @('!')@ is compatible
-- with the 'Multiplicative' structure.
--
-- (2) The property 1. for a 'Algebraic' structure forces the 'Semiring' to be 'Commutative'.
class (Semiring r, Commutative r, Algebraic r, Scalar r ~ r) => AlgebraicSemiring r

instance AlgebraicSemiring Int
instance AlgebraicSemiring Integer
instance AlgebraicSemiring N
instance AlgebraicSemiring Z
instance AlgebraicSemiring Q

--------------------------------------------------------------------------------
-- AlgebraicRing -

-- | algebraic rings.
type AlgebraicRing r = (AlgebraicSemiring r, Ring r)

--------------------------------------------------------------------------------
-- AlgebraicField -

-- | algebraic fields.
type AlgebraicField r = (AlgebraicSemiring r, Field r)

--------------------------------------------------------------------------------
-- Alg -
  
-- | type representing the class of @__k__-'Algebraic'@ structures.
data Alg k

type instance Structure (Alg k) x = (Algebraic x, k ~ Scalar x)

instance Transformable (Alg k) Typ where tau Struct = Struct
instance Transformable (Alg k) Ent where tau Struct = Struct
instance Transformable (Alg k) Ort where tau Struct = Struct
instance Transformable (Alg k) Mlt where tau Struct = Struct
instance Transformable (Alg k) Fbr where tau Struct = Struct
instance Transformable (Alg k) FbrOrt where tau Struct = Struct
instance Transformable (Alg k) Add where tau Struct = Struct
instance Transformable (Alg k) Dst where tau Struct = Struct
instance Transformable (Alg k) (Vec k) where tau Struct = Struct
instance TransformableG Op (Alg k) (Alg k) where tauG Struct = Struct

--------------------------------------------------------------------------------
-- TransformableAlg -

-- | transformable to @__k__-'Algebraic'@ structure.
class ( Transformable (s k) Ort, Transformable (s k) Mlt
      , Transformable (s k) Fbr, Transformable (s k) FbrOrt
      , Transformable (s k) Add, Transformable (s k) Dst
      , Transformable (s k) (Vec k)
      , Transformable (s k) (Alg k)
      ) => TransformableAlg k s

instance TransformableTyp (Alg k)
instance TransformableOrt (Alg k)
instance TransformableMlt (Alg k)
instance TransformableFbr (Alg k)
instance TransformableFbrOrt (Alg k)
instance TransformableAdd (Alg k)
instance TransformableDst (Alg k)
instance TransformableVec k Alg
instance TransformableAlg k Alg

