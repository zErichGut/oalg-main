
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


-- |
-- Module      : OAlg.Structure.Oriented.Point
-- Description : associating a point type.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Associating a point type for structured algebraic types.
module OAlg.Structure.Oriented.Point
  (
    -- * Point
    Point, EntityPoint
  , U(..)

    -- * Applicative
  , ApplicativePoint, pmap
  , FunctorialPoint

    -- * Point Wrapper
  , Pnt(..)
  , idPnt, toPntG, fromPntG
   
    -- * Total
  , Total

    -- * Helper Classes
  , ShowPoint, EqPoint, OrdPoint, ValidablePoint
  , TypeablePoint, SingletonPoint
  , XStandardPoint
  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Unify

import OAlg.Data.Singleton

--------------------------------------------------------------------------------
-- Point -

-- | the associated type of points.
type family Point x

--------------------------------------------------------------------------------
-- Point - helper classes -

-- | helper class to avoid undecidable instances.
class Show (Point x) => ShowPoint x

-- | helper class to avoid undecidable instances.
class Eq (Point x) => EqPoint x

-- | helper class to avoid undecidable instances.
class Ord (Point x) => OrdPoint x

-- | helper class to avoid undecidable instances.
class Validable (Point x) => ValidablePoint x

-- | helper class to avoid undecidable instances.
class Typeable (Point x) => TypeablePoint x

-- | helper class to avoid undecidable instances.
class Singleton (Point x) => SingletonPoint x

-- | helper class to avoid undecidable instances.
class XStandard (Point a) => XStandardPoint a

--------------------------------------------------------------------------------
-- EntityPoint -

-- | 'Point' as 'Entity'.
type EntityPoint x = (ShowPoint x, EqPoint x, ValidablePoint x, TypeablePoint x)

--------------------------------------------------------------------------------
-- Total -

-- | total orientations.
type Total = SingletonPoint

--------------------------------------------------------------------------------
-- Point - Associations -

type instance Point (Id x) = Point x
instance ShowPoint x => ShowPoint (Id x)
instance EqPoint x => EqPoint (Id x)
instance OrdPoint x => OrdPoint (Id x)
instance SingletonPoint x => SingletonPoint (Id x)
instance ValidablePoint x => ValidablePoint (Id x)
instance TypeablePoint x => TypeablePoint (Id x)
instance XStandardPoint x => XStandardPoint (Id x)

type instance Point () = ()
instance ShowPoint ()
instance EqPoint ()
instance OrdPoint ()
instance SingletonPoint ()
instance ValidablePoint ()
instance TypeablePoint ()
instance XStandardPoint ()

type instance Point Int = ()
instance ShowPoint Int
instance EqPoint Int
instance OrdPoint Int
instance SingletonPoint Int
instance ValidablePoint Int
instance TypeablePoint Int
instance XStandardPoint Int

type instance Point Integer = ()
instance ShowPoint Integer
instance EqPoint Integer
instance OrdPoint Integer
instance SingletonPoint Integer
instance ValidablePoint Integer
instance TypeablePoint Integer
instance XStandardPoint Integer

type instance Point N = ()
instance ShowPoint N
instance EqPoint N
instance OrdPoint N
instance SingletonPoint N
instance ValidablePoint N
instance TypeablePoint N
instance XStandardPoint N

type instance Point Z = ()
instance ShowPoint Z
instance EqPoint Z
instance OrdPoint Z
instance SingletonPoint Z
instance ValidablePoint Z
instance TypeablePoint Z
instance XStandardPoint Z

type instance Point Q = ()
instance ShowPoint Q
instance EqPoint Q
instance OrdPoint Q
instance SingletonPoint Q
instance ValidablePoint Q
instance TypeablePoint Q
instance XStandardPoint Q

type instance Point (SomeMorphism m) = SomeObjectClass m
instance ShowPoint (SomeMorphism m)
instance EqPoint (SomeMorphism m)
instance ValidablePoint (SomeMorphism m)
instance Typeable m => TypeablePoint (SomeMorphism m)

--------------------------------------------------------------------------------
-- Pnt -

-- | wrapper for 'Point's.
newtype Pnt x = Pnt (Point x)

type instance Point (Pnt x) = Point x

deriving instance ShowPoint x => Show (Pnt x)
deriving instance EqPoint x => Eq (Pnt x)
deriving instance ValidablePoint x => Validable (Pnt x)
deriving instance XStandardPoint x => XStandard (Pnt x)


instance ShowPoint x => ShowPoint (Pnt x)
instance EqPoint x => EqPoint (Pnt x)
instance ValidablePoint x => ValidablePoint (Pnt x)
instance XStandardPoint x => XStandardPoint (Pnt x)

---------------------------------------------------------------------
-- idPnt -

idPnt :: Point x ~ Point y => Pnt x -> Pnt y
idPnt (Pnt p) = Pnt p  

--------------------------------------------------------------------------------
-- toPntG -

-- | to 'Pnt',
toPntG :: (Point x -> Point y) -> Pnt x -> Pnt y
toPntG f (Pnt x) = Pnt (f x)

--------------------------------------------------------------------------------
-- fromPntG -

-- | from 'Pnt'.
fromPntG :: (Pnt x -> Pnt y) -> Point x -> Point y
fromPntG f p = p' where Pnt p' = f (Pnt p)

--------------------------------------------------------------------------------
-- U -

-- | accosiating @()@ as 'Point'
newtype U x = U x deriving (Show,Eq)

instance Validable x => Validable (U x) where valid (U x) = valid x

type instance Point (U x) = ()

instance ShowPoint (U x)
instance EqPoint (U x)
instance ValidablePoint (U x)
instance TypeablePoint (U x)
instance SingletonPoint (U x)

--------------------------------------------------------------------------------
-- ApplicativePoint -

-- | applications on 'Point's.
type ApplicativePoint h = ApplicativeG Pnt h (->)

--------------------------------------------------------------------------------
-- pmap -

-- | the induced mapping of 'Point's given by 'amapG'. 
pmap :: ApplicativePoint h => h x y -> Point x -> Point y
pmap h = fromPntG (amapG h)

--------------------------------------------------------------------------------
-- FunctorialPoint -

type FunctorialPoint h = FunctorialG Pnt h (->)



