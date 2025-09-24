
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}

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
  , tauTuple, tauFst, tauSnd
  
  , Structure2, Struct2(..)

    -- * Transformable
  , Transformable(..), tauType
  , Transformable1, tau1
  , TransformableTyp, TransformableType
  , TransformableG(..), tauG'
  , TransformableGRefl
  

    -- * Some Structure Types
  , Typ, tauTyp
  , Ord', Bol
  , SubStruct, tauGSubStruct, tauSubStruct

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

--------------------------------------------------------------------------------
-- Structure -

-- | parameterized constraint for a type @__x__@.
type family Structure s x :: Constraint

--------------------------------------------------------------------------------
-- (,) -

type instance Structure (s,t) x = (Structure s x,Structure t x)

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
-- tauFst -

-- | the first struct according to @__(s,t)__@.
tauFst :: Struct (s,t) x -> Struct s x
tauFst Struct = Struct

-----------------------------------------------------------------------------------------
-- tauSnd -

-- | the second struct according to @__(s,t)__@.
tauSnd :: Struct (s,t) x -> Struct t x
tauSnd Struct = Struct

--------------------------------------------------------------------------------
-- tauTuple -

-- | the product structure. 
tauTuple :: Struct s x -> Struct t x -> Struct (s,t) x
tauTuple Struct Struct = Struct

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
-- tauTyp -

-- | 'tau' to 'Typ'
tauTyp :: Transformable s Typ => Struct s x -> Struct Typ x
tauTyp = tau

--------------------------------------------------------------------------------
-- Type -

type instance Structure Type x = ()

--------------------------------------------------------------------------------
-- tauType -

-- | transformbing to 'Type'-structure.
tauType :: Struct s x -> Struct Type x
tauType _ = Struct

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
{-
instance (Transformable s u, Transformable s v) => Transformable s (u,v) where
   tau s = tauTuple (tau s) (tau s)
-}
-- instance Transformable (s,t) s where tau = tauFst
-- instance Transformable (s,t) t where tau = tauSnd

--------------------------------------------------------------------------------
-- TransformaleType -

-- | helper class to avoid undecidable instances.
class Transformable s Type => TransformableType s

{-
instance Transformable s Type where
  tau _ = Struct
-}

--------------------------------------------------------------------------------
-- TransformableG -

-- | transforming structural attests.
class TransformableG t u v where
  tauG :: Struct u x -> Struct v (t x)

instance TransformableG d s Type where
  tauG _ = Struct

instance (TransformableG d s u, TransformableG d s v) => TransformableG d s (u,v) where
  tauG s = tauTuple (tauG s) (tauG s)
  
--------------------------------------------------------------------------------
-- tauTupleG -
{-
tauTupleG :: Struct s (d x) -> Struct t (d x) -> Struct (s,t) (d x)
tauTupleG Struct
-}
--------------------------------------------------------------------------------
-- tauG' -

-- | prefixing a proxy.
tauG' :: TransformableG t u v => q t -> Struct u x -> Struct v (t x)
tauG' _ = tauG

--------------------------------------------------------------------------------
-- TransformableGRefl -

-- | helper class to avoid undecidable instances.
class TransformableG o s s => TransformableGRefl o s

--------------------------------------------------------------------------------
-- Transformable1 -

-- | transforming structural attests.
type Transformable1 f s = TransformableG f s s

--------------------------------------------------------------------------------
-- tau1 -

-- | transformation1. (needed for backward compatibility!).
tau1 :: Transformable1 f s => Struct s x -> Struct s (f x)
tau1 = tauG

--------------------------------------------------------------------------------
-- TransformableTyp -

-- | helper class to avoid undecidable instances.
class Transformable s Typ => TransformableTyp s

instance Transformable s Typ => TestEquality (Struct s) where
  testEquality sa sb = te (tau sa) (tau sb) where
    te :: Struct Typ a -> Struct Typ b -> Maybe (a:~:b)
    te Struct Struct = eqT

--------------------------------------------------------------------------------
-- SubStruct -

-- | parameterized sub structures.
data SubStruct t s

type instance Structure (SubStruct t s) x = Structure t x

instance Transformable t (SubStruct t s) where tau Struct = Struct

--------------------------------------------------------------------------------
-- tauSubStruct -
tauSubStruct :: Struct (SubStruct t s) x -> Struct t x
tauSubStruct Struct = Struct

--------------------------------------------------------------------------------
-- tauGSubStruct -

tauGSubStruct :: TransformableG t u v => Struct (SubStruct u s) x -> Struct v (t x)
tauGSubStruct u = tauG (tauSubStruct u)

