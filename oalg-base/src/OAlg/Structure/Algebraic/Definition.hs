
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneKindSignatures #-}

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
    Algebraic, Alg, ForgetfulAlg
  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Distributive.Definition
import OAlg.Structure.Vectorial.Definition


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
instance Transformable1 Op (Alg k) where tau1 Struct = Struct

--------------------------------------------------------------------------------
-- ForgetfulAlg -

-- | transformable to @__k__-'Algebraic'@ structure.
class ( ForgetfulOrt (s k), ForgetfulMlt (s k)
      , ForgetfulFbr (s k), ForgetfulFbrOrt (s k)
      , ForgetfulAdd (s k), ForgetfulDst (s k)
      , ForgetfulVec k s
      , Transformable (s k) (Alg k)
      ) => ForgetfulAlg k s

instance ForgetfulTyp (Alg k)
instance ForgetfulOrt (Alg k)
instance ForgetfulMlt (Alg k)
instance ForgetfulFbr (Alg k)
instance ForgetfulFbrOrt (Alg k)
instance ForgetfulAdd (Alg k)
instance ForgetfulDst (Alg k)
instance ForgetfulVec k Alg
instance ForgetfulAlg k Alg

