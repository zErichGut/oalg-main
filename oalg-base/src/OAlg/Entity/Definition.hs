
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , EmptyDataDeriving
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
#-}

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
    Entity, Ent

    -- * Entity1
  , Entity1
  
    -- * Entity2
  , Entity2

    -- * Basic Entities
    -- ** Empty
  , Empty(), empty, Empty2(), empty2
  )
  where

import Prelude (Ord(..),undefined)

import Data.Typeable

import OAlg.Category.Definition


import OAlg.Data.Show
import OAlg.Data.Equal
import OAlg.Data.Validable
import OAlg.Data.Number
import OAlg.Data.Opposite

import OAlg.Data.Either
import OAlg.Data.Symbol

import OAlg.Structure.Definition

--------------------------------------------------------------------------------
-- Entity -

-- | entity.
class (Show a, Eq a, Validable a, Typeable a) => Entity a

deriving instance Entity x => Entity (Op x)

instance Entity ()
instance Entity Int
instance Entity Integer
instance Entity Char
instance Entity Symbol
instance Entity N
instance Entity Z
instance Entity Q

instance Entity a => Entity [a]
instance (Entity a,Entity b) => Entity (a,b)

--------------------------------------------------------------------------------
-- Ent -
-- | indexing 'Entity's.
data Ent

type instance Structure Ent x = Entity x 

--------------------------------------------------------------------------------
-- Entity1 -

-- | entity for parameterized types.
class (Show1 a, Eq1 a, Validable1 a, Typeable a) => Entity1 a

instance Entity1 Proxy

--------------------------------------------------------------------------------
-- Entity2 - 

-- | entity for two parameterized types.
class (Show2 h, Eq2 h, Validable2 h, Typeable h) => Entity2 h

--------------------------------------------------------------------------------
-- Empty -

-- | the empty entity.
data Empty deriving (Eq, Ord, Show)

-- | the empty function.
empty :: Empty -> x
empty = const undefined

instance Validable Empty where
  valid = empty

instance Entity Empty

--------------------------------------------------------------------------------
-- Empty2 -

-- | the empty entity2.
data Empty2 a b deriving (Eq, Show)

-- | the empty function.
empty2 :: Empty2 a b -> x
empty2 = const undefined

instance Validable (Empty2 x y) where
  valid = empty2

instance Show2 Empty2

instance Eq2 Empty2

instance Validable2 Empty2

instance Entity2 Empty2

--------------------------------------------------------------------------------
-- Entity2 - Instance -

instance (Entity2 f, Entity2 g) => Entity2 (Either2 f g)

instance (Entity2 h, Typeable t) => Entity2 (Forget t h)

