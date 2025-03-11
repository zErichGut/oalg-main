
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , TypeOperators
  , DataKinds
  , RankNTypes
#-}

-- |
-- Module      : OAlg.Data.Duality
-- Description : dualities.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Dualities.
module OAlg.Data.Duality
  (
    Functor1(..)
  , Duality1(..), toBidual1, fromDual1
  , prpBidual1
  ) where

import OAlg.Prelude

import OAlg.Data.Relation

--------------------------------------------------------------------------------
-- Duality1 -

-- | duality for one-parameterized structures, where @__b__@ is the dual of @__a__@ and vice versa.
--
-- __Property__ Let @'Duality1' __s__ __d__ __i__ __o__@ then holds:
-- For all @__a__@, @__b__@, @__x__@, @d@ in @__d__ __i__ __o__ __a__ __b__@,
-- @s@ in @'Struct' __s__ __x__@ and @'Functor1' i = 'isoBidual1' d s@ holds:
-- @'toBidual1' d s a '==' 'amap1' i a@ for all @a@ in @__a__ __x__@.
class (Cayleyan2 i, Symmetric (d i o), Transformable1 o s)
  => Duality1 s d i o where
  -- | mapping to dual.
  toDual1    :: d i o a b -> Struct s x -> a x -> b (o x)

  -- | functor to bidual.
  isoBidual1 :: d i o a b -> Struct s x -> Functor1 i a x (o (o x))

--------------------------------------------------------------------------------
-- toBidual1 -

-- | mapping to bidual.
toBidual1 :: Duality1 s d i o => d i o a b -> Struct s x -> a x -> a (o (o x))
toBidual1 d s = toDual1 (swap d) (tau1 s) . toDual1 d s

--------------------------------------------------------------------------------
-- fromDual1 -
-- | mapping from dual.
fromDual1 :: Duality1 s d i o => d i o a b -> Struct s x -> b (o x) -> a x
fromDual1 d s = case isoBidual1 d s of Functor1 i -> amap1 (invert2 i) . toDual1 (swap d) (tau1 s)

--------------------------------------------------------------------------------
-- prpBidual1 -

-- | validity of the property of 'Duality1'.
prpBidual1 :: (Duality1 s d i o, Show (a x), Eq (a (o (o x))))
  => d i o a b -> Struct s x -> X (a x) -> Statement
prpBidual1 d s xa = Prp "Bidual1" :<=>: case isoBidual1 d s of
  Functor1 i -> Forall xa (\a -> (toBidual1 d s a == amap1 i a) :?> Params ["a":=show a])
