
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : OAlg.Structure.Definition
-- Description : introducing the idiom of structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- introducing the idiom of 'Structure's as parameterized constraints.
module OAlg.Structure.Definition
  (
    -- * Structure
    Structure, Struct(..)

  , Structure2, Struct2(..)

    -- * Transformable
  , Transformable(..), Transformable1(..), TransformableOp
  , TransformableTyp

    -- * Some Structure Types
  , Typ, Ord', Bol

  ) where

import Data.Kind
import Data.Typeable
import Data.Type.Equality

import OAlg.Data.Boolean.Definition
import OAlg.Data.Show
import OAlg.Data.Equal
import OAlg.Data.Ord
import OAlg.Data.Singular
import OAlg.Data.Maybe
import OAlg.Data.Opposite

--------------------------------------------------------------------------------
-- Structure -

-- | parameterized constraint for a type @__x__@.
type family Structure s x :: Constraint

--------------------------------------------------------------------------------
-- Struct -

-- | attest that the type @__x__@ admits the constrains given by the parameter @__s__@.
data Struct s x where
  Struct :: Structure s x => Struct s x

deriving instance Show (Struct s x)
deriving instance Eq (Struct s x)

instance Show1 (Struct s) where
  show1 = show

instance Eq1 (Struct s) 
instance Singular (Struct s)

--------------------------------------------------------------------------------
-- Structure2 -

-- | parameterized constraint for a two types @__x__@ and @__y__@.
type family Structure2 m x y :: Constraint

--------------------------------------------------------------------------------
-- Struct2 -

-- | attest that the two types @__x__@ and @__y__@ admit the constraint given by the parameter @__s__@.
data Struct2 m x y where
  Struct2 :: Structure2 m x y => Struct2 m x y

deriving instance Show (Struct2 m x y)
instance Show2 (Struct2 m)

deriving instance Eq (Struct2 m x y)
instance Eq2 (Struct2 m)

--------------------------------------------------------------------------------
-- Typ -

-- | 'Typeable' structures.
data Typ

type instance Structure Typ x = Typeable x

--------------------------------------------------------------------------------
-- Type -

type instance Structure Type x = ()

--------------------------------------------------------------------------------
-- Ord' -

-- | type for ordered structures.
data Ord'

type instance Structure Ord' x = Ord x

--------------------------------------------------------------------------------
-- Bol -

-- | type representing 'Boolean' structures.
data Bol

type instance Structure Bol x = Boolean x

--------------------------------------------------------------------------------
-- Transformable -

-- | transforming structural attests.
class Transformable s t where
  tau :: Struct s x -> Struct t x

instance Transformable s s where
  tau s = s

instance Transformable s Type where
  tau _ = Struct

--------------------------------------------------------------------------------
-- Transformable1 -

-- | transforming structural attests.
class Transformable1 f s where
  tau1 :: Struct s x -> Struct s (f x)

--------------------------------------------------------------------------------
-- TransformableOp -

-- | helper class to avoid undecidable instances.
class Transformable1 Op s => TransformableOp s

--------------------------------------------------------------------------------
-- TransformableTyp -

-- | helper class to avoid undecidable instances.
class Transformable s Typ => TransformableTyp s


instance Transformable s Typ => TestEquality (Struct s) where
  testEquality sa sb = te (tau sa) (tau sb) where
    te :: Struct Typ a -> Struct Typ b -> Maybe (a:~:b)
    te Struct Struct = eqT
