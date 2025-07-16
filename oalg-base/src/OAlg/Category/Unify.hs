
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Category.Unify
-- Description : unification of categories
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- unification of categories, i.e. projecting morphisms by dropping the parameterization by there
-- 'domain' and 'range'.
module OAlg.Category.Unify
  (
    -- * Morphism
    SomeMorphism(..), SomeObjectClass(..)
  , SomeMorphismSite(..)
  , someOne
  , SomeCmpb3(..), SomeCmpb2(..), smCmpb2
  
    -- * Path
  , SomePath(..), somePath
  , SomePathSite(..)
  
    -- * Entity
  , SomeEntity(..)

    -- * Application
  , SomeApplication(..)
  , xSomeAppl

  )
  where

import Data.Typeable
import Data.Type.Equality

import Data.List ((++))

import OAlg.Category.Definition
import OAlg.Structure.Definition
import OAlg.Category.Path

import OAlg.Data.Identity
import OAlg.Data.X
import OAlg.Data.Dualisable
import OAlg.Data.Validable
import OAlg.Data.Maybe
import OAlg.Data.Equal
import OAlg.Data.Show
import OAlg.Data.Boolean

import OAlg.Entity.Definition

--------------------------------------------------------------------------------
-- SomeApplication -

-- | some application.
data SomeApplication h where
  SomeApplication :: h x y -> x -> SomeApplication h

--------------------------------------------------------------------------------
-- xSomeAppl -

-- | random variable for some application.
xSomeAppl :: (Morphism m, Transformable (ObjectClass m) XStd) => m x y -> X (SomeApplication m)
xSomeAppl m = amap1 (SomeApplication m) (xStd m)


--------------------------------------------------------------------------------
-- SomeMorphism -

-- | some morphism.
data SomeMorphism m where
  SomeMorphism :: m x y -> SomeMorphism m

instance Show2 m => Show (SomeMorphism m) where
  show (SomeMorphism f) = "SomeMorphism[" ++ show2 f ++ "]"

instance (Morphism m, TransformableObjectClassTyp m, Typeable m, Eq2 m)
  => Eq (SomeMorphism m) where
  SomeMorphism f == SomeMorphism g = case eqlMorphism tx tx' ty ty' f g of
    Just Refl -> eq2 f g
    Nothing   -> False

    where tx  = domain (Forget f)
          tx' = domain (Forget g)
          ty  = range (Forget f)
          ty' = range (Forget g)


instance Validable2 m => Validable (SomeMorphism m) where
  valid (SomeMorphism f) = valid2 f

--------------------------------------------------------------------------------
-- SomeCmpb2 -

-- | some composable morphisms.
data SomeCmpb2 c where
  SomeCmpb2 :: c y z -> c x y -> SomeCmpb2 c
  
--------------------------------------------------------------------------------
-- SomeCmpb3 -

-- | some composable morphisms.
data SomeCmpb3 c where
  SomeCmpb3 :: c x w -> c y x ->  c z y -> SomeCmpb3 c

--------------------------------------------------------------------------------
-- smCmpb2 -

-- | composing the two composables.
smCmpb2 :: Category h => SomeCmpb2 h -> SomeMorphism h
smCmpb2 (SomeCmpb2 f g) = SomeMorphism (f . g)


--------------------------------------------------------------------------------
-- SomeEntity -

-- | some entity @x@ in @__x__@ having the given @'ObjectClass' __m__@ as structure.
data SomeEntity m where
  SomeEntity :: Entity x => Struct (ObjectClass m) x -> x -> SomeEntity m

--------------------------------------------------------------------------------
-- SomePath -

-- | some path
data SomePath m where
  SomePath :: Path m x y -> SomePath m 

instance Show2 m => Show (SomePath m) where
  show (SomePath pth) = "SomePath[" ++ show2 pth ++ "]"

type instance Dual (SomePath m) = SomePath (Op2 m)

instance Morphism m => Dualisable (SomePath m) where
  toDual (SomePath pth) = SomePath $ toDual pth
  fromDual (SomePath pth') = SomePath $ fromDual pth'
  
--------------------------------------------------------------------------------
-- SomeObjectClass -

-- | some object class.
data SomeObjectClass m where
  SomeObjectClass :: Transformable (ObjectClass m) Typ
    => Struct (ObjectClass m) x -> SomeObjectClass m

--------------------------------------------------------------------------------
-- SomeObjectClass - Dualisable -

type instance Dual (SomeObjectClass m) = SomeObjectClass (Op2 m)

instance Dualisable (SomeObjectClass m) where
  toDual (SomeObjectClass s) = SomeObjectClass s
  fromDual (SomeObjectClass s) = SomeObjectClass s

--------------------------------------------------------------------------------
-- SomeObjectClass - Entity -

deriving instance Show (SomeObjectClass m)

instance Eq (SomeObjectClass m) where
  SomeObjectClass o == SomeObjectClass o' = case testEquality o o' of
    Just Refl -> o == o'
    Nothing   -> False

instance Validable (SomeObjectClass m) where
  valid (SomeObjectClass o) = valid o

--------------------------------------------------------------------------------
-- someOne

-- | some 'cOne' for some object class.
someOne :: Category c => SomeObjectClass c -> SomeMorphism c
someOne (SomeObjectClass s) = SomeMorphism (cOne s) 

--------------------------------------------------------------------------------
-- SomePathSite -

-- | some path parameterized either by its 'domain' or 'range'.
data SomePathSite s m x where
  SomePathDomain :: Path m x y -> SomePathSite From m x
  SomePathRange  :: Path m x y -> SomePathSite To m y

type instance Dual (SomePathSite s m y) = SomePathSite (Dual s) (Op2 m) y

instance Morphism m => Dualisable (SomePathSite To m y) where
  toDual (SomePathRange pth) = SomePathDomain (toDual pth)
  fromDual (SomePathDomain pth') = SomePathRange (fromDual pth')

--------------------------------------------------------------------------------
-- somePath -

-- | embedding.
somePath :: SomePathSite s m x -> SomePath m
somePath (SomePathDomain pth) = SomePath pth
somePath (SomePathRange pth) = SomePath pth

--------------------------------------------------------------------------------
-- SomeMorphismSite -

-- | some morphism given by a 'Site'.
data SomeMorphismSite s m x where
  SomeMorphismDomain :: m x y -> SomeMorphismSite From m x
  SomeMorphismRange  :: m x y -> SomeMorphismSite To m y

type instance Dual (SomeMorphismSite s m y) = SomeMorphismSite (Dual s) (Op2 m) y

instance Dualisable (SomeMorphismSite To m y) where
  toDual (SomeMorphismRange m) = SomeMorphismDomain (Op2 m)
  fromDual (SomeMorphismDomain (Op2 m)) = SomeMorphismRange m

