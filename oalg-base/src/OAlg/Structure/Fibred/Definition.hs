
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
-- Module      : OAlg.Structure.Fibred.Definition
-- Description : definition of fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- fibred structures, i.e. type @__f__@ with an associated root type @'Root' __f__@ such that
-- every value in @__f__@ has a 'root'.
module OAlg.Structure.Fibred.Definition
  (
    -- * Fibred
    Fibred(..)
  , Fbr, TransformableFbr, tauFbr
  
    -- * Root
  , Root, ShowRoot, EqRoot, OrdRoot, SingletonRoot, TotalRoot, ValidableRoot, TypeableRoot
  , Rt(..), fromRtG

    -- * Fibred Oriented
  , FibredOriented, FbrOrt, TransformableFbrOrt, tauFbrOrt

    -- * Sheaf
  , Sheaf(..)

  )
  where

import Control.Exception

import Data.Typeable
import Data.List((++),map)
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Identity
import OAlg.Data.Canonical
import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Multiplicative.Definition

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

type EntityRoot x = (ShowRoot x, EqRoot x, ValidableRoot x, TypeableRoot x)

--------------------------------------------------------------------------------
-- Root - () -

type instance Root () = Orientation ()

instance ShowRoot ()
instance EqRoot ()
instance ValidableRoot ()
instance SingletonRoot ()
instance TypeableRoot ()

--------------------------------------------------------------------------------
-- Root - Id -

type instance Root (Id x) = Root x

instance ShowRoot x => ShowRoot (Id x)
instance EqRoot x => EqRoot (Id x)
instance ValidableRoot x => ValidableRoot (Id x)
instance SingletonRoot x => SingletonRoot (Id x)
instance TypeableRoot x => TypeableRoot (Id x)

--------------------------------------------------------------------------------
-- Root - Op -

type instance Root (Op x) = Root x

instance ShowRoot x => ShowRoot (Op x)
instance EqRoot x => EqRoot (Op x)
instance ValidableRoot x => ValidableRoot (Op x)
instance SingletonRoot x => SingletonRoot (Op x)
instance TypeableRoot x => TypeableRoot (Op x)

--------------------------------------------------------------------------------
-- Rt -

newtype Rt x = Rt (Root x)

type instance Root (Rt x) = Root x

deriving instance ShowRoot x => Show (Rt x)
deriving instance EqRoot x => Eq (Rt x)
deriving instance ValidableRoot x => Validable (Rt x)

--------------------------------------------------------------------------------
-- idRoot -

idRoot :: Root x ~ Root y => Rt x -> Rt y
idRoot (Rt r) = Rt r

--------------------------------------------------------------------------------
-- fromRtG -

-- | from 'Rt'.
fromRtG :: (Rt x -> Rt y) -> Root x -> Root y
fromRtG f r = r' where Rt r' = f (Rt r)

--------------------------------------------------------------------------------
-- Fibred -

-- | types with a 'Fibred' structure. An entity of a 'Fibred' structure will be
-- called a __stalk__.
--
--  __Note__
--
-- (1) On should accept the @default@ for 'root' only for 'FibredOriented' structures!
--
-- (2) For 'OAlg.Structure.Distributive.Definition.Distributive' structures the only thing to be
-- implemented is the 'Root' type and should be defined as @'Root' d = 'Orientation' p@ where-- @p = 'Point' d@ (see the default implementation of 'root').
class (Entity f, EntityRoot f) => Fibred f where
  -- | the 'root' of a stalk in @f@.
  root :: f -> Root f
  default root :: (Root f ~ Orientation (Point f), Oriented f) => f -> Root f
  root = orientation

--------------------------------------------------------------------------------
-- FibredOriented -


-- | 'Fibred' and 'Oriented' structure with matching 'root' and 'orientation'.
--
--   __Property__ Let __@d@__ be a 'FibredOriented' structure, then holds:
--
--   (1) @'root' '.=.' 'orientation'@.
--
--   __Note__ 'FibredOriented' structures are required for
--  'OAlg.Structure.Distributive.Distributive' structures.
class (Fibred d, Oriented d, Root d ~ Orientation (Point d)) => FibredOriented d

data FOr
type instance Structure FOr x = FibredOriented x

--------------------------------------------------------------------------------
-- Fibred - Instance -

instance Fibred ()
instance FibredOriented ()

type instance Root Int = Orientation ()
instance ShowRoot Int
instance EqRoot Int
instance ValidableRoot Int
instance TypeableRoot Int
instance SingletonRoot Int
instance Fibred Int
instance FibredOriented Int

type instance Root Integer = Orientation ()
instance ShowRoot Integer
instance EqRoot Integer
instance ValidableRoot Integer
instance SingletonRoot Integer
instance TypeableRoot Integer
instance Fibred Integer
instance FibredOriented Integer

type instance Root N = Orientation ()
instance ShowRoot N
instance EqRoot N
instance ValidableRoot N
instance SingletonRoot N
instance TypeableRoot N
instance Fibred N
instance FibredOriented N

type instance Root Z = Orientation ()
instance ShowRoot Z
instance EqRoot Z
instance ValidableRoot Z
instance SingletonRoot Z
instance TypeableRoot Z
instance Fibred Z
instance FibredOriented Z

type instance Root Q = Orientation ()
instance ShowRoot Q
instance EqRoot Q
instance ValidableRoot Q
instance SingletonRoot Q
instance TypeableRoot Q
instance Fibred Q
instance FibredOriented Q

type instance Root (Orientation p) = Orientation p
instance Show p => ShowRoot (Orientation p)
instance Eq p => EqRoot (Orientation p)
instance Validable p => ValidableRoot (Orientation p)
instance Singleton p => SingletonRoot (Orientation p)
instance Typeable p => TypeableRoot (Orientation p)
instance Entity p => Fibred (Orientation p) where
instance Entity p => FibredOriented (Orientation p)

instance Fibred x => Fibred (Id x) where root (Id x) = root x
instance FibredOriented x => FibredOriented (Id x)

instance FibredOriented x => Fibred (Op x)
instance FibredOriented x => FibredOriented (Op x)


--------------------------------------------------------------------------------
-- TotalRoot -

type TotalRoot = SingletonRoot

--------------------------------------------------------------------------------
-- Sheaf -

-- | a list in a 'Fibred' structure having all the same 'root'.
--
-- __Definition__ Let __@f@__ be a 'Fibred' structure and @s = 'Sheaf' r [t 0 .. t (n-1)]@ a
-- sheaf in __@'Sheaf' f@__, then @s@ is 'valid' if and only if
--
-- (1) @r@ is 'valid' and @t i@ are valid for all @i = 0..n-1@.
--
-- (2) @'root' (t i) '==' r@ for all @i = 0..n-1@.
--
-- furthermore @n@ is called the __/length/__ of @s@.
--
-- If two sheafs have the same 'root' then there stalks can be composed - via @('++')@ -
-- to a new sheaf having the same 'root'. But as @('++')@ is not commutative they
-- are equipped with a 'Multiplicative' structure.
data Sheaf f = Sheaf (Root f) [f]

deriving instance (Show f, ShowRoot f) => Show (Sheaf f)
deriving instance (Eq f, EqRoot f) => Eq (Sheaf f)

instance Foldable Sheaf where
  foldr op b (Sheaf _ fs) = foldr op b fs

instance Fibred f => Validable (Sheaf f) where
  valid (Sheaf r fs) = valid r && vld r fs where
    vld _ []     = SValid 
    vld r (f:fs) = valid f && (root f .==. r) && vld r fs

type instance Root (Sheaf f) = Root f
instance ShowRoot f => ShowRoot (Sheaf f)
instance EqRoot f => EqRoot (Sheaf f)
instance ValidableRoot f => ValidableRoot (Sheaf f)
instance TypeableRoot f => TypeableRoot (Sheaf f)
instance Fibred f => Fibred (Sheaf f) where
  root (Sheaf r _) = r


type instance Point (Sheaf f) = Root f
instance ShowRoot f => ShowPoint (Sheaf f)
instance EqRoot f => EqPoint (Sheaf f)
instance ValidableRoot f => ValidablePoint (Sheaf f)
instance TypeableRoot f => TypeablePoint (Sheaf f)
instance Fibred f => Oriented (Sheaf f) where
  orientation s = root s :> root s

-- | @'Data.List.(++)'@ is not commutative!
instance Fibred f => Multiplicative (Sheaf f) where
  one r = Sheaf r []
  Sheaf r fs * Sheaf s gs | r == s    = Sheaf r (fs++gs)
                          | otherwise = throw NotMultiplicable

type instance Dual (Sheaf f) = Sheaf (Op f)

instance FibredOriented f => Dualisable (Sheaf f) where
  toDual (Sheaf r fs)     = Sheaf (transpose r) (map Op fs)
  fromDual (Sheaf r' fs') = Sheaf (transpose r') (map fromOp fs')

instance Fibred f => Embeddable f (Sheaf f) where
  inj a = Sheaf (root a) [a]

--------------------------------------------------------------------------------
-- Fbr -

-- | type representing the class of 'Fibred' structures.
data Fbr

type instance Structure Fbr x = Fibred x

instance Transformable Fbr Typ where tau Struct = Struct
instance Transformable Fbr Ent where tau Struct = Struct

--------------------------------------------------------------------------------
-- tauFbr -

-- | 'tau' for 'Fbr'.
tauFbr :: Transformable s Fbr => Struct s x -> Struct Fbr x
tauFbr = tau

--------------------------------------------------------------------------------
-- TransformableFbr -

-- | transformable to 'Fibred' structure.
class Transformable s Fbr => TransformableFbr s

instance TransformableTyp Fbr
instance TransformableFbr Fbr

--------------------------------------------------------------------------------
-- FbrOrt -
  
-- | type representing the class of 'FibredOriented' structures.
data FbrOrt

type instance Structure FbrOrt x = FibredOriented x

instance Transformable FbrOrt Typ where tau Struct = Struct
instance Transformable FbrOrt Ent where tau Struct = Struct
instance Transformable FbrOrt Fbr where tau Struct = Struct
instance Transformable FbrOrt Ort where tau Struct = Struct

--------------------------------------------------------------------------------
-- TransformableFbrOrt -

-- | transformable to 'FibredOriented' structure.
class ( Transformable s Fbr, Transformable s Ort
      , Transformable s FbrOrt
      ) => TransformableFbrOrt s

instance TransformableTyp FbrOrt
instance TransformableOrt FbrOrt
instance TransformableFbr FbrOrt
instance TransformableFbrOrt FbrOrt

--------------------------------------------------------------------------------
-- tauFbrOrt -

-- | 'tau' for 'FbrOrt'.
tauFbrOrt :: Transformable s FbrOrt => Struct s x -> Struct FbrOrt x
tauFbrOrt = tau



