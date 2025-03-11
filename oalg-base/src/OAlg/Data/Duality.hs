
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
  , Duality1(..)
  , toDualSnd, isoBidualSnd
  , fromDualFst, fromDualSnd
  , toBidualFst, toBidualSnd
  , prpDuality1
  ) where

import OAlg.Prelude

import OAlg.Data.Relation

--------------------------------------------------------------------------------
-- Duality1 -

-- | duality for one-parameterized structures, where @__b__@ is the dual of @__a__@ and vice versa.
--
-- __Property__ Let @'Duality1' __s__ __d__ __i__ __o__@ then holds:
-- For all @__a__@, @__b__@, @__x__@, @d@ in @__d__ __i__ __o__ __a__ __b__@,
-- @s@ in @'Struct' __s__ __x__@ holds:
--
-- (1) @'toBidualFst' d s a '==' 'amap1' i a@ for all @a@ in @__a__ __x__@ and
-- @'Functor1' i = 'isoBidualFst' d s@.
--
-- (2) @'toBidualSnd' d s b '==' 'amap1' i b@ for all @b@ in @__b__ __x__@ and
-- @'Functor1' i = 'isoBidualSnd' d s@.
class (Cayleyan2 i, Symmetric (d i o), Transformable1 o s)
  => Duality1 s d i o where
  -- | mapping to dual.
  toDualFst    :: d i o a b -> Struct s x -> a x -> b (o x)

  -- | functor to bidual.
  isoBidualFst :: d i o a b -> Struct s x -> Functor1 i a x (o (o x))

--------------------------------------------------------------------------------
-- toDualSnd -

-- | mapping to dual.
toDualSnd :: Duality1 s d i o => d i o a b -> Struct s x -> b x -> a (o x)
toDualSnd d = toDualFst (swap d)

--------------------------------------------------------------------------------
-- isoBidualSnd -

-- | mapping to dual.
isoBidualSnd :: Duality1 s d i o => d i o a b -> Struct s x -> Functor1 i b x (o (o x))
isoBidualSnd d = isoBidualFst (swap d)

--------------------------------------------------------------------------------
-- toBidualFst -

-- | mapping to bidual.
toBidualFst :: Duality1 s d i o => d i o a b -> Struct s x -> a x -> a (o (o x))
toBidualFst d s = toDualFst (swap d) (tau1 s) . toDualFst d s

--------------------------------------------------------------------------------
-- toBidualSnd -

-- | mapping to bidual.
toBidualSnd :: Duality1 s d i o => d i o a b -> Struct s x -> b x -> b (o (o x))
toBidualSnd d = toBidualFst (swap d)

--------------------------------------------------------------------------------
-- fromDualFst -

-- | mapping from dual.
fromDualFst :: Duality1 s d i o => d i o a b -> Struct s x -> b (o x) -> a x
fromDualFst d s = case isoBidualFst d s of
  Functor1 i -> amap1 (invert2 i) . toDualFst (swap d) (tau1 s)

--------------------------------------------------------------------------------
-- fromDualSnd -

-- | mapping from dual.
fromDualSnd :: Duality1 s d i o => d i o a b -> Struct s x -> a (o x) -> b x
fromDualSnd d = fromDualFst (swap d)

--------------------------------------------------------------------------------
-- prpBidual1 -

relBidualFst :: (Duality1 s d i o, Show (a x), Eq (a (o (o x))))
  => d i o a b -> Struct s x -> X (a x) -> Statement
relBidualFst d s xa = case isoBidualFst d s of
  Functor1 i -> Forall xa (\a -> (toBidualFst d s a == amap1 i a) :?> Params ["a":=show a])
  
-- | validity of the property of 'Duality1'.
prpDuality1 :: ( Duality1 s d i o
               , Show (a x), Eq (a (o (o x)))
               , Show (b x), Eq (b (o (o x)))
               )
  => d i o a b -> Struct s x -> X (a x) -> X (b x) -> Statement
prpDuality1 d s xa xb = Prp "Duality1" :<=>:
  And [ Label "1" :<=>: relBidualFst d s xa
      , Label "2" :<=>: relBidualFst (swap d) s xb
      ]
