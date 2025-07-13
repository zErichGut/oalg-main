
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : OAlg.Structure.Distributive.Definition
-- Description : definition for distributive structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- distributive structures, i.e. multiplicative structures with a suitable additive structure.
module OAlg.Structure.Distributive.Definition
  ( -- * Distributive
    Distributive, Dst, TransformableDst, tauDst

    -- * Transposable
  , TransposableDistributive
  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Oriented.Opposite
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Additive.Definition

--------------------------------------------------------------------------------
-- Distributive -

-- | 'FibredOriented' structures equipped with an 'Additive' and 'Multiplicative' structure
-- satisfying the laws of __/distributivity/__.
--
-- __Properties__ Let @__d__@ be a 'Distributive' structure, then holds:
--
-- (1) #Dst1#For all @g@ in @__d__@ and @r@ in @'Root' __d__@ with
-- @'end' g '==' 'start' r@ holds: @'zero' r '*' g '==' 'zero' r'@
-- where @r' '==' 'start' g ':>' 'end' r@.
--
-- (2) #Dst2#For all @g@, @a@ and @b@ in @__d__@ with @'root' a '==' 'root' b@ and
-- @'start' a '==' 'end' g@ holds: @(a '+' b) '*' g == a'*'g '+' b'*'g@.
--
-- (3) #Dst3#For all @f@ in @__d__@ and @r@ in @'Root' __d__@ with
-- @'start' f '==' 'end' r@ holds: @f '*' 'zero' r '==' 'zero' r'@
-- where @r' = 'start' r ':>' 'end' f@.
--
-- (4) #Dst4#For all @f@, @a@ and @b@ in @__d__@ with @'root' a '==' 'root' b@ and
-- @'start' f '==' 'end' a@ holds: @f'*'(a '+' b) == f'*'a '+' f'*'b@.
--
-- __Note__ If @__d__@ is interpreted as a small category @__C__@ then it is usually called
-- __preadditive__. If @__d__@ is also 'Abelian' then @__C__@ is also usually called
-- __abelian__.
class (FibredOriented d, Additive d, Multiplicative d) => Distributive d

instance Distributive ()
instance Distributive Int
instance Distributive Integer
instance Distributive N
instance Distributive Z
instance Distributive Q
instance Entity p => Distributive (Orientation p)
instance Distributive d => Distributive (Op d)

--------------------------------------------------------------------------------
-- Transposable -

-- | transposable distributive structures.
--
-- __Property__ Let @__d__@ be a 'TransposableDistributive' structure, then holds:
--
-- (1) For all @r@ in @'Root' d@ holds:
-- @'transpose' ('zero' r) '==' 'zero' ('transpose' r)@
--
-- (2) For all @a@, @b@ in @__d__@ with @'root' a '==' 'root' b@ holds:
-- @'transpose' (a '+' b) '==' 'transpose' a '+' 'transpose' b@.
class (TransposableMultiplicative d, Distributive d) => TransposableDistributive d

instance Entity p => TransposableDistributive (Orientation p)
instance TransposableDistributive N
instance TransposableDistributive Z
instance TransposableDistributive Q

--------------------------------------------------------------------------------
-- Dst -
  
-- | type representing the class of 'Distributive' structures.
data Dst

type instance Structure Dst x = Distributive x

instance Transformable Dst Typ where tau Struct = Struct
instance Transformable Dst Ent where tau Struct = Struct
instance Transformable Dst Ort where tau Struct = Struct
instance Transformable Dst Mlt where tau Struct = Struct
instance Transformable Dst Fbr where tau Struct = Struct
instance Transformable Dst FbrOrt where tau Struct = Struct
instance Transformable Dst Add where tau Struct = Struct
instance TransformableG Op Dst Dst where tauG Struct = Struct
instance TransformableOp Dst

--------------------------------------------------------------------------------
-- tauDst -

-- | 'tau' for 'Dst'.
tauDst :: Transformable s Dst => Struct s x -> Struct Dst x
tauDst = tau

--------------------------------------------------------------------------------
-- TransformableDst -

-- | transformable to 'Distributive' structure.
class ( Transformable s Ort, Transformable s Mlt
      , Transformable s Fbr, Transformable s Add
      , Transformable s FbrOrt
      , Transformable s Dst
      ) => TransformableDst s

instance TransformableTyp Dst
instance TransformableOrt Dst
instance TransformableMlt Dst
instance TransformableFbr Dst
instance TransformableFbrOrt Dst
instance TransformableAdd Dst
instance TransformableDst Dst

