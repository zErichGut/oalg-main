
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneKindSignatures, StandaloneDeriving #-}

-- |
-- Module      : OAlg.Structure.Vectorial.Definition
-- Description : definition of vectorial structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of vectorial structures, i.e. 'Additive' structures with a scalar multiplication @('!')@.
module OAlg.Structure.Vectorial.Definition
  ( -- * Vectorial
    Vectorial(..), Vec, TransformableVec

    -- ** Sheaf
  , VectorSheaf(..)

    -- * Euclidean
  , Euclidean(..)
  )
  where

import Control.Exception

import OAlg.Prelude

import OAlg.Structure.Exception
import OAlg.Structure.Oriented.Orientation
import OAlg.Structure.Oriented.Opposite
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Ring.Definition
import OAlg.Structure.Number.Definition

--------------------------------------------------------------------------------
-- Vectorial -

infixr 8 !

-- | 'Additive' structures with a __total__ defined __scalar multiplication__ from the left
--   by a __commutative semi ring__. The entities of __@v@__ are called __vector__.
--
-- __Properties__ Let __@v@__ b a 'Vectorial' structure, then holds:
--
-- (1) #Vec1#For all @s@ in @'Scalar' __v__@ and @v@ in __@v@__ holds:
-- @s'!'v@ is 'valid' and @'root' (s'!'v) '==' 'root' v@.
--
-- (2) #Vec2#For all @v@ in __@v@__ holds: @0'!'v '==' 'zero' ('root' v)@.
--
-- (3) #Vec3#For all @s@ in @'Scalar' __v__@ and @r@ in @'Root' __v__@ holds
-- @s'!''zero' r '==' 'zero' r@.
--
-- (4) #Vec4#For all @r@, @s@ in @'Scalar' __v__@ and @v@ in __@v@__ holds:
-- @(r '+' s)'!'v '==' r'!'v '+' s'!'v@.
--
-- (5) #Vec5#For all @s@ in @'Scalar' __v__@ and @v@, @w@ in __@v@__ with
-- @'root' v '==' 'root' w@ holds: @s'!'(v '+' w) '==' s'!'v '+' s'!'w@.
--
-- (6) #Vec6#For all @v@ in __@v@__ holds: @1'!'v '==' v@.
--
-- (7) #Vec7#For all @r@, @s@ in @'Scalar' __v__@ and @v@ in __@v@__ holds:
-- @(r'*'s)'!'v '==' r'!'(s'!'v)@.
class (Semiring (Scalar v), Commutative (Scalar v), Additive v) => Vectorial v where
  -- | the type of scalars.
  type Scalar v

  -- | scalar multiplication of a vector.
  (!) :: Scalar v -> v -> v

--------------------------------------------------------------------------------
-- VectorSheaf -

-- | list of scalars and vectors, having all the same given root.
--
-- __Property__ Let @'VectorSheaf' r svs@ be in @'VectorSheaf' __v__@ for a 'Vectorial'-structure
-- @__v__@, then holds: @'root' v '==' r@, for all @(_,v)@ in @svs@.  
data VectorSheaf v = VectorSheaf (Root v) [(Scalar v,v)]

deriving instance Vectorial v => Show (VectorSheaf v)
deriving instance Vectorial v => Eq (VectorSheaf v)

instance Vectorial v => Validable (VectorSheaf v) where
  valid (VectorSheaf r xs) = Label "VectorSheaf" :<=>: valid r && vld r xs where
    vld _ []         = SValid
    vld r ((s,v):xs) = And [ valid s
                           , valid v
                           , (root v == r) :?> Params ["r":=show r,"v":=show v]
                           , vld r xs
                           ]

--------------------------------------------------------------------------------
-- Instances -

instance Vectorial () where
  type Scalar () = Q
  (!) = qtimes

instance Vectorial Int where
  type Scalar Int = Int
  (!) = (*)

instance Vectorial Integer where
  type Scalar Integer = Integer
  (!) = (*)

instance Vectorial N where
  type Scalar N = N
  (!) = (*)

instance Vectorial Z where
  type Scalar Z = Z
  (!) = (*)

instance Vectorial Q where
  type Scalar Q = Q
  (!) = (*)

instance Entity p => Vectorial (Orientation p) where
  type Scalar (Orientation p) = Q
  _ ! o = o

instance (Vectorial v, FibredOriented v) => Vectorial (Op v) where
  type Scalar (Op v) = Scalar v
  s ! (Op v) = Op (s!v)
  
--------------------------------------------------------------------------------
-- Euclidean -
infix 7 <!>
  
-- | 'Vectorial' structures with a __partially__ defined scalar product.
--
-- __Properties__ 
--
-- (1) For all @v@, @w@ holds: if @'root' v '==' 'root' w@ then @v '<!>' w@ is 'valid', otherwise
-- a 'UndefinedScalarproduct'-exception will be thrown.
--
-- (2) For all @u@ holds: @u '<!>' 'zero' ('root' u) '==' 'rZero'@.
--
-- (3) For all @u@, @v@ and @w@ with @'root' u '==' 'root' w@ and
-- @'root' w '==' 'root' v  @
-- holds: @u '<!>' (v '+' w) '==' u '<!>' v '+' u '<!>' w@.
--
-- (4) For all @w@ holds: @'zero' ('root' w) '<!>' w '==' 'rZero'@.
--
-- (5) For all @u@, @v@ and @w@ with @'root' w '==' 'root' u@ and
-- @'root' u '==' 'root' v  @
-- holds: @(u '+' v) '<!>' w '==' u '<!>' w '+' v' <!>' w@.
class Vectorial v => Euclidean v where

  -- | the scalar product of two vectors.
  (<!>) :: v -> v -> Scalar v

instance Euclidean N where
  (<!>) = (*)

instance Euclidean Z where
  (<!>) = (*)

instance Euclidean Q where
  (<!>) = (*)

instance Entity p => Euclidean (Orientation p) where
  a <!> b | root a == root b = 0
          | otherwise        = throw UndefinedScalarproduct
          

--------------------------------------------------------------------------------
-- Vec -
  
-- | type representing the class of @__k__-'Vectorial'@ structures.
data Vec k

type instance Structure (Vec k) x = (Vectorial x, k ~ Scalar x)

instance Transformable (Vec k) Typ where tau Struct = Struct
instance Transformable (Vec k) Ent where tau Struct = Struct
instance Transformable (Vec k) Fbr where tau Struct = Struct
instance Transformable (Vec k) Add where tau Struct = Struct

--------------------------------------------------------------------------------
-- TransformableVec -

-- | transformable to @__k__-'Vectorial'@ structure.
class ( Transformable (s k) Fbr, Transformable (s k) Add 
      , Transformable (s k) (Vec k)
      ) => TransformableVec k s

instance TransformableTyp (Vec k)
instance TransformableFbr (Vec k)
instance TransformableAdd (Vec k)
instance TransformableVec k Vec
