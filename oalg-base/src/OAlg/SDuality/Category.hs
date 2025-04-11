
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
#-}

-- |
-- Module      : OAlg.SDuality.Category
-- Description : category of structural dualities.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- category of structural dualities.
module OAlg.SDuality.Category
  ( -- * Category
    SDualityCat()
    
    -- * Map
  , SDualityMap(..)
  , PathSDualityMap, rdcPathSDualityMap
  ) where

import Control.Monad

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Either
import OAlg.Data.Reducible
import OAlg.Data.Constructable

import OAlg.SDuality.Definition

--------------------------------------------------------------------------------
-- SDualityMap -

-- | adjoining to a type family @__h__@ of morphisms the two morphisms 'ToDual' and 'FromDual'.
data SDualityMap s o h x y where
  SDualityMap :: Transformable (ObjectClass h) s => h x y -> SDualityMap s o h x y
  ToDual :: (Structure s x, Structure s (o x)) => SDualityMap s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) => SDualityMap s o h (o x) x

instance Transformable s Typ => TransformableObjectClassTyp (SDualityMap s o h)
  
--------------------------------------------------------------------------------
-- SDualityMap - Entity2 -

instance Show2 h => Show2 (SDualityMap s o h) where
  show2 (SDualityMap h) = "SDualityMap (" ++ show2 h ++ ")"
  show2 ToDual          = "ToDual"
  show2 FromDual        = "FromDual"

instance Eq2 h => Eq2 (SDualityMap s o h) where
  eq2 (SDualityMap f) (SDualityMap g) = eq2 f g
  eq2 ToDual ToDual                   = True
  eq2 FromDual FromDual               = True
  eq2 _ _                             = False

instance Validable2 h => Validable2 (SDualityMap s o h) where
  valid2 (SDualityMap h) = valid2 h
  valid2 _               = SValid

instance (Entity2 h, Typeable s, Typeable o) => Entity2 (SDualityMap s o h)

--------------------------------------------------------------------------------
-- SDualityMap - Morphism -

instance Morphism h => Morphism (SDualityMap s o h) where
  type ObjectClass (SDualityMap s o h) = s

  homomorphous (SDualityMap h) = tauHom (homomorphous h)
  homomorphous ToDual          = Struct :>: Struct
  homomorphous FromDual        = Struct :>: Struct

--------------------------------------------------------------------------------
-- SDualityMap - Applicative -

instance (Morphism h, Applicative h, SDualisable s o) => Applicative (SDualityMap s o h) where
  amap (SDualityMap h) = amap h
  amap t@ToDual        = sdlToDual (domain t)
  amap f@FromDual      = sdlFromDual (range f)

----------------------------------------
-- SDualityMap - Applicative1 -

instance (Morphism h, Applicative1 h a, Applicative1 h b, SDualisable1 s o a b)
  => Applicative1 (SDualityMap s o h) (Either1 a b) where
  amap1 (SDualityMap h)   = \ab -> case ab of
    Left1 a              -> Left1 (amap1 h a)
    Right1 b             -> Right1 (amap1 h b)
  amap1 t@ToDual          = \ab -> case ab of
    Left1 a              -> Right1 $ sdlToDualLeft (domain t) a
    Right1 b             -> Left1 $ sdlToDualRight (domain t) b
  amap1 f@FromDual        = \ab -> case ab of
    Left1 a              -> Right1 $ sdlFromDualLeft (range f) a
    Right1 b             -> Left1 $ sdlFromDualRight (range f) b

--------------------------------------------------------------------------------
-- PathSDualityMap -

type PathSDualityMap s o h = Path (SDualityMap s o h)

--------------------------------------------------------------------------------
-- rdcPathSDualityMap -

rdcPathSDualityMap :: PathSDualityMap s o h x y -> Rdc (PathSDualityMap s o h x y)
rdcPathSDualityMap p = case p of
  FromDual :. ToDual :. p' -> reducesTo p' >>= rdcPathSDualityMap
  ToDual :. FromDual :. p' -> reducesTo p' >>= rdcPathSDualityMap
  p' :. p''                -> rdcPathSDualityMap p'' >>= return . (p' :.)
  _                        -> return p

instance Reducible (PathSDualityMap s o h x y) where
  reduce = reduceWith rdcPathSDualityMap

--------------------------------------------------------------------------------
-- SDualityCat -

newtype SDualityCat s o h x y = SDualityCat (PathSDualityMap s o h x y)
  deriving (Show, Show2, Validable, Validable2)

deriving instance (Morphism h, TransformableTyp s, Eq2 h) => Eq2 (SDualityCat s o h)

instance (Morphism h, Entity2 h, TransformableTyp s, Typeable o, Typeable s)
  => Entity2 (SDualityCat s o h)
  
--------------------------------------------------------------------------------
-- SDualityCat - Constructable -

instance Exposable (SDualityCat s o h x y) where
  type Form (SDualityCat s o h x y) = PathSDualityMap s o h x y
  form (SDualityCat p) = p

instance Constructable (SDualityCat s o h x y) where
  make = SDualityCat . reduce

--------------------------------------------------------------------------------
-- SDualityCat - Category -

instance Morphism h => Morphism (SDualityCat s o h) where
  type ObjectClass (SDualityCat s o h) = s
  homomorphous (SDualityCat p) = homomorphous p

instance Morphism h => Category (SDualityCat s o h) where
  cOne = make . IdPath
  SDualityCat f . SDualityCat g = make (f . g)

--------------------------------------------------------------------------------
-- SDualityCat - Applicative -

instance (Morphism h, Applicative h, SDualisable s o) => Applicative (SDualityCat s o h) where
  amap (SDualityCat p) = amap p


instance (Morphism h, Applicative1 h a, Applicative1 h b, SDualisable1 s o a b)
  => Applicative1 (SDualityCat s o h) (Either1 a b) where
  amap1 (SDualityCat p) = amap1 p


