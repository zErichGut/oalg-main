
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

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
    Fibred(..), Fbr, TransformableFbr

    -- * Fibred Oriented
  , FibredOriented, FbrOrt, TransformableFbrOrt

    -- * Spezial classes
  , OrdRoot, TotalRoot

    -- * Sheaf
  , Sheaf(..)
  )
  where

import Control.Exception

import Data.List((++),map)
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Multiplicative.Definition

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
class (Entity f, Entity (Root f)) => Fibred f where
  -- | the type of roots.
  type Root f

  -- | the 'root' of a stalk in @f@.
  root :: f -> Root f
  -- default root :: FibredOriented f => f -> Root f
  default root :: (Root f ~ Orientation (Point f), Oriented f) => f -> Root f
  root = orientation

--------------------------------------------------------------------------------
-- FibredOriented -


-- | 'Fibred' and 'Oriented' structure with matching 'root' and 'orientation'.
--
--   __Property__ Let __@d@__ be a 'FibredOriented' structure, then holds:
--   For all @s@ in __@d@__ holds: @'root' s '==' 'orientation' s@.
--
--   __Note__ 'FibredOriented' structures are required for
--  'OAlg.Structure.Distributive.Distributive' structures.
class (Fibred d, Oriented d, Root d ~ Orientation (Point d)) => FibredOriented d

data FOr
type instance Structure FOr x = FibredOriented x

--------------------------------------------------------------------------------
-- Fibred - Instance -

instance Fibred () where
  type Root () = Orientation ()
instance FibredOriented ()

instance Fibred Int where
  type Root Int = Orientation ()
instance FibredOriented Int

instance Fibred Integer where
  type Root Integer = Orientation ()
instance FibredOriented Integer

instance Fibred N where
  type Root N = Orientation ()
instance FibredOriented N

instance Fibred Z where
  type Root Z = Orientation ()
instance FibredOriented Z

instance Fibred Q where
  type Root Q = Orientation ()
instance FibredOriented Q

instance Entity p => Fibred (Orientation p) where
  type Root (Orientation p) = Orientation p
instance Entity p => FibredOriented (Orientation p)

instance FibredOriented f => Fibred (Op f) where
  type Root (Op f) = Orientation (Point f)
instance FibredOriented f => FibredOriented (Op f)

--------------------------------------------------------------------------------
-- OrdRoot -

-- | type where the associated root type is ordered.
--
--  __Note__ Helper class to circumvent undecidable instances.
class Ord (Root f) => OrdRoot f

--------------------------------------------------------------------------------
-- TotalRoot -

-- | type where the associated root type is a singleton.
class Singleton (Root f) => TotalRoot f

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

deriving instance Fibred f => Show (Sheaf f)
deriving instance Fibred f => Eq (Sheaf f)

instance Foldable Sheaf where
  foldr op b (Sheaf _ fs) = foldr op b fs

instance Fibred f => Validable (Sheaf f) where
  valid (Sheaf r fs) = valid r && vld r fs where
    vld _ []     = SValid 
    vld r (f:fs) = valid f && (root f .==. r) && vld r fs

instance Fibred f => Entity (Sheaf f)

instance Fibred f => Fibred (Sheaf f) where
  type Root (Sheaf f) = Root f
  root (Sheaf r _) = r

instance Fibred f => Oriented (Sheaf f) where
  type Point (Sheaf f) = Root f
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

