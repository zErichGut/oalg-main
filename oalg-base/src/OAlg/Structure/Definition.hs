
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

    -- * Transformable
  , Transformable(..), Transformable1(..), TransformableOp
  , ForgetfulTyp

    -- * Some Structure Types
  , Typ, Ord'   

  ) where

import Data.Kind
import Data.Typeable
import Data.Type.Equality

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
-- ForgetfulTyp -

-- | helper class to avoid undecidable instances.
class Transformable s Typ => ForgetfulTyp s


instance Transformable s Typ => TestEquality (Struct s) where
  testEquality sa sb = te (tau sa) (tau sb) where
    te :: Struct Typ a -> Struct Typ b -> Maybe (a:~:b)
    te Struct Struct = eqT
