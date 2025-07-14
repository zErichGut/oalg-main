
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      : OAlg.Structure.Additive.Definition
-- Description : definition of additive structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- additive structures, i.e. structures with a __partially__ defined addition @('+')@.
module OAlg.Structure.Additive.Definition
  (
    -- * Additive
    Additive(..), zero', Add, TransformableAdd, tauAdd

    -- * Abelian
  , Abelian(..), isZero, Abl, TransformableAbl

  -- * X
  , xSheaf, xSheafRoot
  )
  where

import qualified Prelude as A

import Control.Monad
import Control.Exception

import Data.List(repeat)
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Oriented.Opposite
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Fibred.Oriented

--------------------------------------------------------------------------------
-- Additive -

infixl 6 +
-- | 'Fibred' structures with a __partialy__ defined __addition__ and having
-- 'zero' as the __neutral element__ of the summation. An entity of a 'Additive'
-- structure will be called a __summand__.
--
-- __Properties__ Let __@a@__ be a 'Additive' structure, then holds:
--
-- (1) #Add1#For all @r@ in __@'Root' a@__ holds: @'root' ('zero' r) '==' r@.
--
-- (2) #Add2#For all @f@ and @g@ in __@a@__ holds:
--
--     (1) #Add2_1#If @'root' f '==' 'root' g@ then @f '+' g@ is 'valid' and
--      @'root' (f '+' g) '==' 'root' f@.
--
--     (2) #Add2_2#If @'root' f '/=' 'root' g@ then @f '+' g@ is not 'valid' and its
--     evaluation will end up in a 'NotAddable'-exception.
--
-- (3) #Add3#For all @f@, @g@ in __@a@__ with @'root' f '==' 'root' g@ holds:
-- @f '+' g '==' g '+' f@.
--
-- (4) #Add4#For all @f@ in __@a@__ holds: @f '+' 'zero' ('root' f) '==' f@
--
-- (5) #Add5#For all @f@, @g@, @h@ in __@a@__ with @'root' f '==' 'root' g '==' 'root' h@
-- holds: @(f '+' g) '+' h '==' f '+' (g '+' h)@.
--
-- (6) #Add6#For all @f@ in @a@ and @n@ in __'N'__ holds:
-- @'ntimes' 0 f == 'zero' ('root' f)@ and @'ntimes' (n '+' 1) f '==' f '+' 'ntimes' n f@.
class Fibred a => Additive a where
  {-# MINIMAL zero, (+) #-}
  
  -- | the neutral element associated to each 'root'. If there is no ambiguity
  --   for @'zero' r@ we will briefly denote it by @0 r@ or just @0@.
  zero :: Root a -> a

  -- | the addition for two summands.
  (+) :: a -> a -> a

  -- | @n@ times of a summand.
  ntimes :: N -> a -> a
  ntimes n f = foldr (+) (zero (root f)) $ takeN n $ repeat $ f

--------------------------------------------------------------------------------
-- Additive - Instance -

instance Additive () where
  zero _ = ()
  _ + _ = ()
  ntimes _ _ = ()

instance Additive Int where
  zero _ = 0
  (+) = (A.+)
  -- ntimes n i = error "nyi"

instance Additive Integer where
  zero _ = 0
  (+) = (A.+)
  ntimes n z = inj n * z

instance Additive N where
  zero _ = 0
  (+) = (A.+)
  ntimes = (*)

instance Additive Z where
  zero _ = 0
  (+) = (A.+)
  ntimes n z = inj n * z

instance Additive Q where
  zero _ = 0
  (+) = (A.+)
  ntimes n q = inj n * q

instance Entity p => Additive (Orientation p) where
  zero = id
  a + b | a == b = a
        | otherwise = throw NotAddable
  ntimes _ a = a

instance (Additive a, FibredOriented a) => Additive (Op a) where
  zero r = Op (zero $ transpose r)
  Op a + Op b = Op (a + b)
  ntimes n (Op a) = Op (ntimes n a)

--------------------------------------------------------------------------------
-- zero' -

-- | the 'zero' to a given root. The type @p c@ serves only as proxy and 'zero'' is
--   lazy in it.
--
--   __Note__ As 'Point' may be a non-injective type family,
--   the type checker needs some times a little bit more information
--   to pic the right 'zero'.
zero' :: Additive a => p a -> Root a -> a
zero' _ = zero

--------------------------------------------------------------------------------
-- isZero -

-- | check for beeing 'zero'.
isZero :: Additive a => a -> Bool
isZero a = a == zero (root a)

--------------------------------------------------------------------------------
-- Abelian -

infixl 6 -
-- | 'Additive' structures having for each summand an __/additve inverse/__.
--
--   __Properties__ Let __@a@__ be a 'Additive' structure, then holds:
--  
--  (1) #Abl1#For all @f@ in __@a@__ holds: @'root' ('negate' f) '==' 'root' f@.
--
--  (2) #Abl2#For all @f@ in __@a@__ holds: @f '+' 'negate' f == 'zero' ('root' f)@.
--
--  (3) #Abl3#For all @f@ and @g@ in __@a@__ holds:
--
--      (1) #Abl3_1#If @'root' f '==' 'root' g@ then @f '-' g@ is 'valid' and
--      @'root' (f '-' g) '==' 'root' f@.
--
--      (2) #Abl3_2#If @'root' f '/=' 'root' g@ then @f '-' g@ is not 'valid' and its
--      evaluation will end up in a 'NotAddable'-exception.
--
--  (4) #Abl4#For @f@ and @g@ in __@a@__ with @'root' f '==' 'root' g@ holds:
--   @f '-' g '==' f '+' 'negate' g@.
--
--  (5) #Abl5#For all @z@ in 'Z' and @f@ in __@a@__ holds:
--
--      (1) #Abl5_1#If @0 '<=' z@ then @'ztimes' z f '==' 'ntimes' ('prj' z) f@.
--
--      (2) #Abl5_2#If @z '<' 0@ then  @'ztimes' z f '==' 'negate' ('ntimes' ('prj' z) f)@.
class Additive a => Abelian a where
  {-# MINIMAL negate | (-) #-}

  -- | negation of a summand.
  negate :: a -> a
  negate f = zero (root f) - f

  -- | subtraction of two summands.
  --
  --  __Properties__
  --
  (-) :: a -> a -> a
  f - g = f + negate g

  -- | @z@ times of a sumand. 
  ztimes :: Z -> a -> a  
  ztimes z f = ntimes (prj z) f' where f' = if z < 0 then negate f else f

instance Abelian () where
  negate _ = ()
  _ - _    = ()
  ztimes _ _ = ()

instance Abelian Int where
  negate = A.negate
  (-)    = (A.-)
  -- ztimes = error "nyi"

instance Abelian Integer where
  negate = A.negate
  (-)    = (A.-)
  ztimes z i = prj z * i

instance Abelian Z where
  negate = A.negate
  (-)    = (A.-)
  ztimes = (*)
  
instance Abelian Q where
  negate = A.negate
  (-)    = (A.-)
  ztimes z i = inj z * i

instance Entity p => Abelian (Orientation p) where
  negate = id

instance (Abelian a, FibredOriented a) => Abelian (Op a) where
  negate (Op x) = Op (negate x)
  Op a - Op b = Op (a-b)
  ztimes z (Op a) = Op (ztimes z a)

--------------------------------------------------------------------------------
-- Add -
  
-- | type representing the class of 'Additive' structures.
data Add

type instance Structure Add x = Additive x

instance Transformable Add Typ where tau Struct = Struct
instance Transformable Add Ent where tau Struct = Struct
instance Transformable Add Fbr where tau Struct = Struct

--------------------------------------------------------------------------------
-- tauAdd -

-- | 'tau' for 'Add'.
tauAdd :: Transformable s Add => Struct s x -> Struct Add x
tauAdd = tau

--------------------------------------------------------------------------------
-- TransformableAdd -

-- | transformable to 'Additive' structure.
class (Transformable s Fbr, Transformable s Add) => TransformableAdd s

instance TransformableTyp Add
instance TransformableFbr Add
instance TransformableAdd Add

--------------------------------------------------------------------------------
-- Abl -

-- | type representing the class of 'Abelian' structures.
data Abl

type instance Structure Abl x = Abelian x

instance Transformable Abl Typ where tau Struct = Struct
instance Transformable Abl Ent where tau Struct = Struct
instance Transformable Abl Fbr where tau Struct = Struct
instance Transformable Abl Add where tau Struct = Struct

--------------------------------------------------------------------------------
-- TransformableAbl -

-- | transformable to 'Abelian' structure.
class (Transformable s Fbr, Transformable s Add, Transformable s Abl) => TransformableAbl s

instance TransformableTyp Abl
instance TransformableFbr Abl
instance TransformableAdd Abl
instance TransformableAbl Abl

--------------------------------------------------------------------------------
-- adjZero -

-- | adjoins a 'zero' stalk for empty 'root's.
adjZero :: Additive a => XStalk a -> XStalk a
adjZero (XStalk xr xrs) = XStalk xr xrs' where
  xrs' r = case xrs r of
    XEmpty -> return (zero r)
    xs     -> xs

--------------------------------------------------------------------------------
-- xSheafRoot -

-- | random variable of sheafs, all based on the given 'root' and with the given length.
xSheafRoot :: Additive a => XStalk a -> N -> Root a -> X (Sheaf a)
xSheafRoot xs = xSheafRootMax (adjZero xs)

--------------------------------------------------------------------------------
-- xSheaf -

-- | random variable of sheafs with the given length.
xSheaf :: Additive a => XStalk a -> N -> X (Sheaf a)
xSheaf xs = xSheafMax (adjZero xs)

