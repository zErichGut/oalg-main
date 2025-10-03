
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, FlexibleInstances #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Entity.Definition
-- Description : definition of entities
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of entities. All algebraic structures defined here are based on them.
-- They are __[showable]("OAlg.Data.Show")__, __[distinguishable]("OAlg.Data.Equal")__,
-- __[validable]("OAlg.Data.Validable")__
-- and __[typeable]("Data.Typeable")__.
module OAlg.Entity.Definition
  (
    -- * Entity
    Entity, Object
  , Ent, EntOrd

    -- * Entity1
  , Entity1
  
    -- * Entity2
  , Entity2

    -- * Basic Entities
    -- ** Empty
  , EntEmpty(), fromEmpty, EntEmpty2(), fromEmpty2

  )
  where

import Prelude (Ord(..),undefined)

import Data.Typeable

import OAlg.Category.Definition

import OAlg.Data.Show
import OAlg.Data.Equal
import OAlg.Data.EqualExtensional
import OAlg.Data.Validable

import OAlg.Structure.Definition

--------------------------------------------------------------------------------
-- Object -

-- | object.
type Object x = (Show x, Validable x)

--------------------------------------------------------------------------------
-- Entity -

-- | entity.
type Entity a = (Object a, Eq a, Typeable a)

--------------------------------------------------------------------------------
-- Ent -
-- | indexing 'Entity's.
data Ent

type instance Structure Ent x = Entity x

--------------------------------------------------------------------------------
-- EntOrd -

-- | indexing orderd entities.
data EntOrd

type instance Structure EntOrd x = (Entity x, Ord x)

instance TransformableG [] EntOrd EntOrd where tauG Struct = Struct

--------------------------------------------------------------------------------
-- Entity1 -

-- | entity for parameterized types.
type Entity1 a =  (Show1 a, Eq1 a, Validable1 a, Typeable a)

--------------------------------------------------------------------------------
-- Entity2 - 

-- | entity for two parameterized types.
type Entity2 h = (Show2 h, Eq2 h, Validable2 h, Typeable h)

--------------------------------------------------------------------------------
-- EntEmpty -

-- | the empty entity.
data EntEmpty deriving (Eq, Ord, Show)

-- | the empty function.
fromEmpty :: EntEmpty -> x
fromEmpty = const undefined

instance Validable EntEmpty where
  valid = fromEmpty

--------------------------------------------------------------------------------
-- EntEmpty2 -

-- | the empty entity2.
data EntEmpty2 a b deriving (Eq, Show)

-- | the empty function.
fromEmpty2 :: EntEmpty2 a b -> x
fromEmpty2 = const undefined

instance Validable (EntEmpty2 x y) where
  valid = fromEmpty2

instance Show2 EntEmpty2
instance Eq2 EntEmpty2
instance EqExt EntEmpty2
instance Validable2 EntEmpty2
instance ApplicativeG t EntEmpty2 b where amapG = fromEmpty2

