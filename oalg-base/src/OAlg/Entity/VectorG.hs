
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
  (
    VectorG(), vectorG
  , vecGSheaf, vecGpsq
  , VectorGForm(..)

  )

  where

import Data.List (foldl)

import OAlg.Prelude

import OAlg.Data.Constructable

import OAlg.Structure.Exception
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial

import OAlg.Entity.Sequence.PSequence

--------------------------------------------------------------------------------
-- VectorG -

-- | generalized vector with elements in a 'Additive' structure @__x__@.
--
-- __Property__ Let @v@ be in @t'VectorG' __i x__@ for a 'Additive' structure @__x__@, then holds:
--
-- (1) the underlying sheaf of @v@ is 'valid'.
--
-- (2) all components of the underlying partial sequence of @v@ are non 'zero'.
data VectorG i x = VectorG (Root x) (PSequence i x)

deriving instance (Fibred x, Show i) => Show (VectorG i x)
deriving instance (Fibred x, Eq i) => Eq (VectorG i x)
deriving instance (Fibred x, Ord x, OrdRoot x, Ord i) => Ord (VectorG i x)

--------------------------------------------------------------------------------
-- vecGpsq -

-- | the underlying partial sequence.
vecGpsq :: VectorG i x -> PSequence i x
vecGpsq (VectorG _ xis) = xis

--------------------------------------------------------------------------------
-- vecSheaf -

-- | the underlying sheaf.
vecGSheaf :: VectorG i x -> Sheaf x
vecGSheaf (VectorG r xis) = Sheaf r (amap1 fst $ psqxs xis) 

--------------------------------------------------------------------------------
-- Validable -

instance (Additive x, Entity i, Ord i) => Validable (VectorG i x) where
  valid (VectorG r xis) = Label "VectorG" :<=>:
    And [ valid r
        , valid xis
        , foldl (vld r) SValid (amap1 fst $ psqxs xis)
        ] where
    
    vld r s x = s && And [ valid x
                         , Label "root" :<=>: (r == root x) :?> Params ["r":=show r, "x":=show x]
                         , Label "non zero" :<=>: not (isZero x) :?> Params ["x":=show x]
                         ]

--------------------------------------------------------------------------------
-- VectorGForm -

-- | form for constructing vectors.
data VectorGForm i x = VectorGForm (Root x) (PSequence i x)

deriving instance (Fibred x, Show i) => Show (VectorGForm i x)
deriving instance (Fibred x, Eq i) => Eq (VectorGForm i x)
deriving instance (Fibred x, Ord x, OrdRoot x, Ord i) => Ord (VectorGForm i x)

instance (Fibred x, Entity i, Ord i) => Validable (VectorGForm i x) where
  valid (VectorGForm r xis) = Label "VectorGForm" :<=>:
    And [ valid r
        , valid xis
        , foldl (vld r) SValid (amap1 fst $ psqxs xis)
        ] where

    vld r s x = s && (Label "root" :<=>: (r == root x) :?> Params ["r":=show r, "x":=show x])


--------------------------------------------------------------------------------
-- vectorG -

-- | constructing a vector.
vectorG :: Additive x => VectorGForm i x -> VectorG i x
vectorG (VectorGForm r xis) = VectorG r $ psqFilter (not . isZero) xis

--------------------------------------------------------------------------------
-- Constructable -

instance Exposable (VectorG i x) where
  type Form (VectorG i x) = VectorGForm i x
  form (VectorG r xis) = VectorGForm r xis

instance Additive x => Constructable (VectorG i x) where
  make = vectorG

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

