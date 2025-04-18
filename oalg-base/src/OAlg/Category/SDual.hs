
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
#-}

-- |
-- Module      : OAlg.Category.SDual
-- Description : category for structural dualities.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- category for structural dualities.
module OAlg.Category.SDual
  (
    -- * Category
    CatSDual(), sctToDual, sctToDual'
    
    -- * Map
  , MapSDual(..)
  , PathMapSDual, rdcPathMapSDual

    -- * Reflexive
  , SReflexive(..)
  ) where

import Control.Monad

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Identity
import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Variant

--------------------------------------------------------------------------------
-- MapSDual -

-- | adjoining to a type family @__h__@ of morphisms two auxiliary morphisms 'ToDual' and 'FromDual'.
data MapSDual s o h x y where
  MapSDual :: (Morphism h, ObjectClass h ~ s) => h x y -> MapSDual s o h x y
  ToDual   :: (Structure s x, Structure s (o x)) => MapSDual s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) => MapSDual s o h (o x) x

--------------------------------------------------------------------------------
-- MapSDual - Disjunctive -

instance Disjunctive (MapSDual s o h x y) where
  variant (MapSDual _) = Covariant
  variant _            = Contravariant

instance Disjunctive2 (MapSDual s o h)

--------------------------------------------------------------------------------
-- MapSDual - Entity2 -

instance Show2 h => Show2 (MapSDual s o h) where
  show2 (MapSDual h) = "MapSDual (" ++ show2 h ++ ")"
  show2 ToDual       = "ToDual"
  show2 FromDual     = "FromDual"

instance Eq2 h => Eq2 (MapSDual s o h) where
  eq2 (MapSDual f) (MapSDual g) = eq2 f g
  eq2 ToDual ToDual             = True
  eq2 FromDual FromDual         = True
  eq2 _ _                       = False

instance Validable2 h => Validable2 (MapSDual s o h) where
  valid2 (MapSDual h) = valid2 h
  valid2 _            = SValid

instance (Entity2 h, Typeable s, Typeable o) => Entity2 (MapSDual s o h)

--------------------------------------------------------------------------------
-- MapSDual - Morphism -

instance Morphism (MapSDual s o h) where
  type ObjectClass (MapSDual s o h) = s

  homomorphous (MapSDual h) = homomorphous h
  homomorphous ToDual       = Struct :>: Struct
  homomorphous FromDual     = Struct :>: Struct

instance Transformable s Typ => TransformableObjectClassTyp (MapSDual s o h)

--------------------------------------------------------------------------------
-- PathMapSDual -

type PathMapSDual s o h = Path (MapSDual s o h)

--------------------------------------------------------------------------------
-- rdcPathMapSDual -

rdcPathMapSDual :: PathMapSDual s o h x y -> Rdc (PathMapSDual s o h x y)
rdcPathMapSDual p = case p of
  FromDual :. ToDual :. p' -> reducesTo p' >>= rdcPathMapSDual
  ToDual :. FromDual :. p' -> reducesTo p' >>= rdcPathMapSDual
  p' :. p''                -> rdcPathMapSDual p'' >>= return . (p' :.)
  _                        -> return p

instance Reducible (PathMapSDual s o h x y) where
  reduce = reduceWith rdcPathMapSDual

--------------------------------------------------------------------------------
-- CatSDual -

newtype CatSDual s o h x y = CatSDual (PathMapSDual s o h x y)
  deriving (Show, Show2, Validable, Validable2)

deriving instance (TransformableTyp s, Eq2 h) => Eq2 (CatSDual s o h)

instance (Entity2 h, TransformableTyp s, Typeable o, Typeable s)
  => Entity2 (CatSDual s o h)

--------------------------------------------------------------------------------
-- CatSDual - Disjunctive -

instance Disjunctive2 (CatSDual s o h)    where variant2 = restrict variant2
instance Disjunctive (CatSDual s o h x y) where variant  = restrict variant

--------------------------------------------------------------------------------
-- CatSDual - Constructable -

instance Exposable (CatSDual s o h x y) where
  type Form (CatSDual s o h x y) = PathMapSDual s o h x y
  form (CatSDual p) = p

instance Constructable (CatSDual s o h x y) where make = CatSDual . reduce

--------------------------------------------------------------------------------
-- CatSDual - Category -

instance Morphism (CatSDual s o h) where
  type ObjectClass (CatSDual s o h) = s
  homomorphous (CatSDual p) = homomorphous p

instance Category (CatSDual s o h) where
  cOne = make . IdPath
  CatSDual f . CatSDual g = make (f . g)

--------------------------------------------------------------------------------
-- sctToDual -

sctToDualStruct :: Struct s x -> Struct s (o x) -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDualStruct s@Struct Struct = Contravariant2 $ make (ToDual :. IdPath s)

sctToDual :: Transformable1 o s => Struct s x -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDual s = sctToDualStruct s (tau1 s)

sctToDual' :: Transformable1 o s
  => q h o -> Struct s x -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDual' _ = sctToDual

--------------------------------------------------------------------------------
-- SReflexive -

-- | duality of @__s__@-structured types given by a reflection.
--
-- __Property__ Let @'SReflexive' __s o__@, then for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
-- Let @q@ be any proxy in @__q o__@, @s' = 'tau1' s@ and @s'' = 'tau1' s'@,
-- @'Inv2' u v = 'sdlRelf'' q s@ and @'Inv2' _ v' = 'sdlRefl'' q s'@ in
--
-- (1) @'sdlCo'' q s' '.' 'sdlCo'' q s '.=.' u@.
--
-- (2) @'sdlCo'' q s '.' v '.=.' v' . 'sdlCo'' q s''@.
class (Category c, Transformable1 o s) => SReflexive c s o d where
  toDualG :: Struct s x -> c (d x) (d (o x))
  reflG :: Struct s x -> Inv2 c (d x) (d (o (o x)))

instance Transformable1 Op s => SReflexive (->) s Op Id where
  toDualG _ = toIdG Op 
  reflG _   = Inv2 (amap1 (Op . Op)) (amap1 (fromOp . fromOp))
  
--------------------------------------------------------------------------------
-- fromDualG -

fromDualG :: SReflexive c s o d => Struct s x -> c (d (o x)) (d x)
fromDualG s = v . toDualG (tau1 s) where Inv2 _ v = reflG s

instance (ApplicativeG d h c, SReflexive c s o d)
  => ApplicativeG d (MapSDual s o h) c where
  amapG (MapSDual h) = amapG h
  amapG t@ToDual     = toDualG (domain t)
  amapG f@FromDual   = fromDualG (range f)

instance TransformableGObjectClassRange d s c => TransformableGObjectClass d (MapSDual s o h) c

instance (ApplicativeG d h c, SReflexive c s o d, TransformableGObjectClassRange  d s c)
  => ApplicativeG d (CatSDual s o h) c where
  amapG = amapG . form

instance (ApplicativeG d h c, SReflexive c s o d, TransformableGObjectClassRange d s c)
  => FunctorialG d (CatSDual s o h) c

