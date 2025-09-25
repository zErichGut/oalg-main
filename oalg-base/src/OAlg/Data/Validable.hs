
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Data.Validable
-- Description : validable values
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- validable values @x@, which can be validated via @'OAlg.Control.Validate.validate' ('valid' x)@. 
module OAlg.Data.Validable
  ( -- * Validable
    Validable(..), rnfValid
  , ValidableDual1

  , Validable1(..), Validable2(..)

    -- * XStandard
  , XStandard(..), relXStandard
  , XStd, xStd, xStdStruct
  , XStandardDual1

    -- * Extensional Equality
  , EqualExt, EqE
  , equalExt
  )
  where

import Control.Monad (return)
import Control.DeepSeq (NFData(..))

import Data.Kind
import Data.Ratio

import OAlg.Category.Applicative
import OAlg.Category.Definition
import OAlg.Data.Identity

import OAlg.Data.Proxy
import OAlg.Data.Boolean.Definition
import OAlg.Data.Statement.Definition
import OAlg.Data.Dualisable
import OAlg.Data.Maybe
import OAlg.Data.Either
import OAlg.Data.Equal
import OAlg.Data.EqualExtensional
import OAlg.Data.Show
import OAlg.Data.Ord
import OAlg.Data.Number
import OAlg.Data.X

import OAlg.Structure.Definition

--------------------------------------------------------------------------------
-- XStandard -

-- | standard random variable for __@x@__.
--
--   __Property__ For all @x@ in the range of 'xStandard' holds: @'valid' x@.
class XStandard x where
  xStandard :: X x

instance XStandard () where xStandard = return ()
instance XStandard Int where xStandard = xInt
instance XStandard Integer where xStandard = xInteger
instance XStandard x => XStandard (Id x) where xStandard = amap1 Id xStandard

instance XStandard N where xStandard = xN
instance XStandard Z where xStandard = xZ
instance XStandard Q where xStandard = xQ

--------------------------------------------------------------------------------
-- xStandard' -

-- | the standard random variable associated to __@x@__. The type __@p x@__ serves
--   only as proxy and will be not evaluated.
xStandard' :: XStandard x => p x -> X x
xStandard' _ = xStandard

--------------------------------------------------------------------------------
-- relXStandard -

-- | validity of the standard random variable associated to __@x@__
--   (__@p x@__ just serves as proxy and will not be evaluated).
relXStandard :: (Validable x, XStandard x) => p x -> Statement
relXStandard px = Forall (xStandard' px) valid where

--------------------------------------------------------------------------------
-- XStd -

-- | type representing the class of 'XStandard' structures.
data XStd

type instance Structure XStd x = (XStandard x)

--------------------------------------------------------------------------------
-- xStd -

xStdStruct :: Struct XStd x -> X x
xStdStruct Struct = xStandard

-- | the associated standard random variable for the 'domain'.
xStd :: (Morphism m, Transformable (ObjectClass m) XStd) => m x y -> X x
xStd m = xStdStruct (tau (domain m))

--------------------------------------------------------------------------------
-- XStandardDual1 -

-- | helper class to avoid undecidable instances.
class XStandard (Dual1 d x) => XStandardDual1 d x

--------------------------------------------------------------------------------
-- Validable -

-- | validation of a value of @__a__@.
class Validable a where
  valid :: a -> Statement

instance Validable () where
  valid = rnfValid

instance Validable Bool where
  valid = rnfValid

instance Validable Valid where
  valid = rnfValid
  
instance Validable Char where
  valid = rnfValid
  
instance Validable Int where
  valid = rnfValid

instance Validable Integer where
  valid = rnfValid

instance Validable (Ratio Integer) where
  valid = rnfValid

instance Validable x => Validable (Id x) where valid (Id x) = valid x

instance Validable N where
  valid = rnfValid
  
instance Validable Z where
  valid = rnfValid
  
instance Validable Q where
  valid = rnfValid

instance Validable x => Validable (Closure x) where
  valid x' = case x' of
    It x -> valid x
    _    -> SValid


instance Validable (Proxy x) where
  valid Proxy = SValid

instance Validable (Struct s x) where
  valid Struct = SValid

instance Validable (Struct2 m x y) where
  valid Struct2 = SValid

instance Validable a => Validable (Maybe a) where
  valid (Just a)  = valid a
  valid (Nothing) = SValid
  
instance Validable a => Validable [a] where
  valid []     = SValid
  valid (x:xs) = valid x :&& valid xs

instance (Validable a,Validable b) => Validable (Either a b) where
  valid (Left a)  = valid a
  valid (Right b) = valid b

instance (Validable a,Validable b) => Validable (a,b) where
  valid (a,b) = And [valid a,valid b]

instance (Validable a,Validable b,Validable c) => Validable (a,b,c) where
  valid (a,b,c) = And [valid a,valid b,valid c]
  
instance (Validable a,Validable b,Validable c,Validable d) => Validable (a,b,c,d) where
  valid (a,b,c,d) = And [valid a,valid b,valid c,valid d]

instance (Validable a,Validable b,Validable c,Validable d,Validable e)
  => Validable (a,b,c,d,e) where
  valid (a,b,c,d,e) = And [valid a,valid b,valid c,valid d,valid e]

instance Validable a => Validable (X a) where
  valid xa = Forall xa valid

instance (XStandard x, Validable y) => Validable (x -> y) where
  valid f = Forall xStandard (valid . f)

--------------------------------------------------------------------------------
-- rnfValid -

-- | validation of being reducible to normal form.
rnfValid :: NFData x => x -> Statement
rnfValid x = ((rnf x == ()) :?> MInvalid)

--------------------------------------------------------------------------------
-- Validable1 -

-- | validation of a value of @p x@.
class Validable1 p where
  valid1 :: p x -> Statement
  default valid1 :: Validable (p x) => p x -> Statement
  valid1 = valid

instance Validable1 Proxy
instance Validable1 (Struct s)

instance (Validable (a x), Validable (b x)) => Validable (Either1 a b x) where
  valid (Left1 a) = valid a
  valid (Right1 b) = valid b

--------------------------------------------------------------------------------
-- ValidableDual1 -

-- | helper class to avoid undecidable instances.
class Validable (Dual1 d x) => ValidableDual1 d x

--------------------------------------------------------------------------------
-- Validable2 -

-- | validation of a value of @h x y@.
class Validable2 h where
  valid2 :: h x y -> Statement
  default valid2 :: Validable (h x y) => h x y -> Statement
  valid2 = valid

instance (Validable2 f, Validable2 g) => Validable2 (Either2 f g) where
  valid2 (Left2 f)  = valid2 f
  valid2 (Right2 g) = valid2 g

instance Validable2 (Struct2 m)

instance Validable2 h => Validable2 (Op2 h) where valid2 (Op2 h) = valid2 h

    
--------------------------------------------------------------------------------
-- EqE -

-- | type representing extensional equality.
data EqE

type instance Structure EqE x = (Show x, Eq x, XStandard x)

instance Transformable EqE Type where tau _ = Struct
instance TransformableType EqE

--------------------------------------------------------------------------------
-- EqualExt -

-- | category of extensional equality.
type EqualExt = Sub EqE (->)

instance EqExt EqualExt where
  Sub f .=. Sub g = prpEqualExt xStandard f g

--------------------------------------------------------------------------------
-- equalExt -

-- | embedding 'amapG' of a 'Applicative1' to 'EqualExt'.
equalExtS :: Applicative1 c t => Homomorphous EqE (t x) (t y) -> c x y -> EqualExt (t x) (t y)
equalExtS (Struct:>:Struct) f = Sub (amapG f)

-- | embedding 'amapG' of a 'Applicative1' to 'EqualExt'.
equalExt :: (Morphism c, Applicative1 c t, TransformableG t (ObjectClass c) EqE)
  => c x y -> EqualExt (t x) (t y)
equalExt f = equalExtS (tauG (domain f):>:tauG (range f)) f

--------------------------------------------------------------------------------
-- Inv2 - Validable

instance (Category c, EqExt c) => Validable (Inv2 c x y) where
  valid (Inv2 f f') = Label "Inv2" :<=>:
    And [ Label "1" :<=>: (f' . f .=. cOne (domain f))
        , Label "2" :<=>: (f . f' .=. cOne (range f))
        ]
    
instance (Category c, EqExt c) => Validable2 (Inv2 c)

