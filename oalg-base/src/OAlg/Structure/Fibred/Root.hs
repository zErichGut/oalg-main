
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Structure.Fibred.Root
-- Description : definition of root
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Definition of 'Root'.
module OAlg.Structure.Fibred.Root
  (
    -- * Root
    Root, ShowRoot, EqRoot, OrdRoot, SingletonRoot, TotalRoot, ValidableRoot, TypeableRoot
  , EntityRoot, XStandardRoot
  , Rt(..), fromRtG, idRt

  -- * Applicative
  , ApplicativeRoot, rmap, amapRt
  , FunctorialRoot

  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Oriented

--------------------------------------------------------------------------------
-- Root -

-- | the type of roots.
type family Root x

--------------------------------------------------------------------------------
-- Root - helper classes -

-- | helper class to avoid undecidable instances.
class Show (Root x) => ShowRoot x

-- | helper class to avoid undecidable instances.
class Eq (Root x) => EqRoot x

-- | helper class to avoid undecidable instances.
class Ord (Root x) => OrdRoot x

-- | helper class to avoid undecidable instances.
class Validable (Root x) => ValidableRoot x

-- | helper class to avoid undecidable instances.
class Typeable (Root x) => TypeableRoot x
-- | helper class to avoid undecidable instances.

-- | helper class to avoid undecidable instances.
class Singleton (Root f) => SingletonRoot f

-- | helper class to avoid undecidable instances.
class XStandard (Root f) => XStandardRoot f

--------------------------------------------------------------------------------
-- EntityRoot -

type EntityRoot x = (ShowRoot x, EqRoot x, ValidableRoot x, TypeableRoot x)

--------------------------------------------------------------------------------
-- TotalRoot -

type TotalRoot = SingletonRoot

--------------------------------------------------------------------------------
-- Root - Instances -

type instance Root () = Orientation ()

type instance Root (Id x) = Root x
instance ShowRoot x => ShowRoot (Id x)
instance EqRoot x => EqRoot (Id x)
instance ValidableRoot x => ValidableRoot (Id x)
instance SingletonRoot x => SingletonRoot (Id x)
instance TypeableRoot x => TypeableRoot (Id x)

type instance Root (Op x) = Root x
instance ShowRoot x => ShowRoot (Op x)
instance EqRoot x => EqRoot (Op x)
instance ValidableRoot x => ValidableRoot (Op x)
instance SingletonRoot x => SingletonRoot (Op x)
instance TypeableRoot x => TypeableRoot (Op x)

instance ShowRoot ()
instance EqRoot ()
instance ValidableRoot ()
instance SingletonRoot ()
instance TypeableRoot ()

type instance Root Int = Orientation ()
instance ShowRoot Int
instance EqRoot Int
instance ValidableRoot Int
instance TypeableRoot Int
instance SingletonRoot Int

type instance Root Integer = Orientation ()
instance ShowRoot Integer
instance EqRoot Integer
instance ValidableRoot Integer
instance SingletonRoot Integer
instance TypeableRoot Integer

type instance Root N = Orientation ()
instance ShowRoot N
instance EqRoot N
instance ValidableRoot N
instance SingletonRoot N
instance TypeableRoot N

type instance Root Z = Orientation ()
instance ShowRoot Z
instance EqRoot Z
instance ValidableRoot Z
instance SingletonRoot Z
instance TypeableRoot Z

type instance Root Q = Orientation ()
instance ShowRoot Q
instance EqRoot Q
instance ValidableRoot Q
instance SingletonRoot Q
instance TypeableRoot Q

type instance Root (Orientation p) = Orientation p
instance Show p => ShowRoot (Orientation p)
instance Eq p => EqRoot (Orientation p)
instance Validable p => ValidableRoot (Orientation p)
instance Singleton p => SingletonRoot (Orientation p)
instance Typeable p => TypeableRoot (Orientation p)
instance XStandard p => XStandardRoot (Orientation p)

--------------------------------------------------------------------------------
-- Rt -

newtype Rt x = Rt (Root x)

type instance Root (Rt x) = Root x

deriving instance ShowRoot x => Show (Rt x)
deriving instance EqRoot x => Eq (Rt x)
deriving instance ValidableRoot x => Validable (Rt x)

instance ApplicativeG Rt h c => ApplicativeG Rt (Inv2 h) c where
  amapG (Inv2 t _) = amapG t

--------------------------------------------------------------------------------
-- idRt -

idRt :: Root x ~ Root y => Rt x -> Rt y
idRt (Rt r) = Rt r

--------------------------------------------------------------------------------
-- amapRt -

amapRt :: (Root x -> Root y) -> Rt x -> Rt y
amapRt r (Rt x) = Rt (r x)

--------------------------------------------------------------------------------
-- fromRtG -

-- | from 'Rt'.
fromRtG :: (Rt x -> Rt y) -> Root x -> Root y
fromRtG f r = r' where Rt r' = f (Rt r)

--------------------------------------------------------------------------------
-- ApplicativeRoot -

type ApplicativeRoot h = ApplicativeG Rt h (->)

--------------------------------------------------------------------------------
-- rmap -

rmap :: ApplicativeRoot h => h x y -> Root x -> Root y
rmap h = fromRtG (amapG h)

--------------------------------------------------------------------------------
-- FunctorialRoot -

type FunctorialRoot h = FunctorialG Rt h (->)

