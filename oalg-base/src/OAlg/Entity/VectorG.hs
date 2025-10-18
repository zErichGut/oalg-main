
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      : OAlg.Entity.VectorG
-- Description : generalized vectors.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- generalized vectors.
module OAlg.Entity.VectorG
  ( VectorG(..)
  )

  where

import Data.List (foldl)

import OAlg.Prelude

import OAlg.Structure.Exception
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial

import OAlg.Entity.Sequence.PSequence

--------------------------------------------------------------------------------
-- VectorG -

data VectorG i x = VectorG (Root x) (PSequence i x)

deriving instance (Fibred x, Show i) => Show (VectorG i x)
deriving instance (Fibred x, Eq i) => Eq (VectorG i x)
deriving instance (Fibred x, Ord x, OrdRoot x, Ord i) => Ord (VectorG i x)


instance (Additive x, Entity i, Ord i) => Validable (VectorG i x) where
  valid (VectorG r xs) = Label "VectorG" :<=>:
    And [ valid xs
        , foldl (vld r) SValid (amap1 fst $ psqxs xs)
        ] where

    vld :: Additive x => Root x -> Statement -> x -> Statement
    vld r s x = And [ s
                    , Label "Root" :<=>: (root x == r) :?> Params ["r":=show r,"x":=show x]
                    , Label "non Zero" :<=>: not (isZero x) :?> Params ["x":=show x]
                    ]


--------------------------------------------------------------------------------
-- VectorGForm -

data VectorGForm i x = VectorGForm (Root x) [(x,i)]


--------------------------------------------------------------------------------
-- vectorG -

-- vectorG :: 
--------------------------------------------------------------------------------
-- Additve - Abelian - Vectorial -

type instance Root (VectorG i x) = Root x
instance Fibred x => ShowRoot (VectorG i x)
instance Fibred x => EqRoot (VectorG i x)
instance Fibred x => ValidableRoot (VectorG i x)
instance Fibred x => TypeableRoot (VectorG i x)

instance (Additive x, Entity i, Ord i) => Fibred (VectorG i x) where
  root (VectorG r _) = r

instance (Additive x, Entity i, Ord i) => Additive (VectorG i x) where
  zero r = VectorG r psqEmpty

  VectorG r a + VectorG r' b
    | r == r'   = VectorG r (psqFilter (not . isZero) $ psqInterlace (+) id id a b)
    | otherwise = throw NotAddable

  ntimes n (VectorG r xs) = VectorG r (psqFilter (not . isZero) $ psqMap (ntimes n) xs)

instance (Abelian x, Entity i, Ord i) => Abelian (VectorG i x) where
  negate (VectorG r xs) = VectorG r (psqMap negate xs)

  VectorG r a - VectorG r' b
    | r == r'   = VectorG r (psqFilter (not . isZero) $ psqInterlace (-) id id a b)
    | otherwise = throw NotAddable

  ztimes z (VectorG r xs) = VectorG r (psqFilter (not . isZero) $ psqMap (ztimes z) xs)

instance (Vectorial x, Entity i, Ord i) => Vectorial (VectorG i x) where
  type Scalar (VectorG i x) = Scalar x
  r ! (VectorG rt xs) = VectorG rt $ psqFilter (not . isZero) $ psqMap (r!) xs

