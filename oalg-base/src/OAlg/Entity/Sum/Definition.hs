
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Sum.Definition
-- Description : definition of free sums over fibred symbols.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of free 'Sum's over 'Fibred' symbols.
module OAlg.Entity.Sum.Definition
  (
    -- * Sum
    Sum(), smlc, smJoin, nSum, zSum, smMap

    -- * Form
  , SumForm(..), smfLength, smflc, lcsmf
  , smfMap, smfJoin, smfReduce

    -- * Linear Combination
  , LinearCombination(..), fromLinComb, lcAggr, lcSort, lcSclFilter

  ) where

import Data.List (map,groupBy,(++),filter)
import Data.Foldable
import Data.Monoid hiding (Sum)

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Ring.Definition
import OAlg.Structure.Number
import OAlg.Structure.Vectorial

import OAlg.Hom.Definition
import OAlg.Hom.Fibred

--------------------------------------------------------------------------------
-- SumForm -

infixr 6 :+
infixr 9 :!

-- | form for a free sum over 'Fibred' symbols in @__a__@ with scalars in @__r__@.
--
-- __Definition__ Let @__r__@ be a 'Commutative' 'Semiring' and @__a__@ a 'Fibred' structure.
-- A 'SumForm' @a@ is 'valid' if and only if all scalars in @a@ are 'valid' and all symbols in @__a__@
-- are 'valid' and have the same @'root'@.
data SumForm r a
  = Zero (Root a)
  | S a
  | r :! SumForm r a
  | SumForm r a :+ SumForm r a

deriving instance (Fibred a, Entity r) => Show (SumForm r a)
deriving instance (Fibred a, Entity r) => Eq (SumForm r a)
deriving instance ( Fibred a, Entity r
                  , OrdRoot a, Ord r, Ord a
                  ) => Ord (SumForm r a)

s :: a -> SumForm Z a
s = S
--------------------------------------------------------------------------------
-- SumForm - Entity -

instance (Fibred a, Semiring r, Commutative r) => Validable (SumForm r a) where
  valid sf = And [ Label "root" :<=>: valid (root sf)
                 , Label "symbols" :<=>: vld sf
                 ] where
    
    vld sf = case sf of
      Zero e   -> valid e
      S a      -> valid a
      r :! a   -> valid r && vld a
      a :+ b   -> vld a && vld b
      
instance (Fibred a, Semiring r, Commutative r) => Entity (SumForm r a)

--------------------------------------------------------------------------------
-- SumForm - Fibred -

instance (Fibred a, Semiring r, Commutative r) => Fibred (SumForm r a) where
  type Root (SumForm r a) = Root a
  root sf = case sf of
    Zero e -> e
    S a    -> root a
    _ :! a -> root a
    a :+ b -> let r = root a in if r == root b then r else throw NotAddable
    
--------------------------------------------------------------------------------
-- SumFrom - Foldable -

instance Foldable (SumForm N) where
  foldMap _ (Zero _) = mempty
  foldMap f (S a)    = f a
  foldMap _ (0:! _)  = mempty
  foldMap f (n:!a)   = foldMap f a <> foldMap f (pred n :! a)
  foldMap f (a :+ b) = foldMap f a <> foldMap f b

--------------------------------------------------------------------------------
-- smfSum -

smfSum :: (Root x -> y) -> (r -> y -> y) -> (y -> y -> y) -> (x -> y) -> SumForm r x -> y
smfSum z (!) (+) f s = sm s where
  sm (Zero e) = z e
  sm (S x)    = f x
  sm (r :! a) = r ! sm a
  sm (a :+ b) = sm a + sm b

--------------------------------------------------------------------------------
-- smfJoin -

smfJoin :: SumForm r (SumForm r a) -> SumForm r a
smfJoin = smfSum Zero (:!) (:+) id

--------------------------------------------------------------------------------
-- smfMap -

smfMap :: Singleton (Root y) => (x -> y) -> SumForm r x -> SumForm r y
smfMap f = smfSum (const ( Zero unit)) (:!) (:+) (S . f)

--------------------------------------------------------------------------------
-- smfLength -

-- | the length of a sum form,
smfLength :: Number r => SumForm r a -> N
smfLength s = case s of
  Zero _  -> 0
  S _     -> 1
  r :! a  -> nFloor r * smfLength a
  a :+ b  -> smfLength a + smfLength b
  where nFloor r = prj $ fst $ zFloorFraction r

instance LengthN (SumForm N a) where
  lengthN = smfLength

--------------------------------------------------------------------------------
-- LinearCombination -

-- | list of symbols in @__a__@ together with a scalar in @__r__@.
--
-- __Note__ 'valid' linear combinations must not sorted according to the second component!
newtype LinearCombination r a = LinearCombination [(r,a)] deriving (Show,Eq,Validable)

instance (Entity a, Entity r) => Entity (LinearCombination r a)

--------------------------------------------------------------------------------
-- fromLinComb -

-- | the underlying list of symbols with their scalar.
fromLinComb :: LinearCombination r a -> [(r,a)]
fromLinComb (LinearCombination as) = as

--------------------------------------------------------------------------------
-- lcAggr -

-- | aggregating words with same symbols.
lcAggr :: (Eq a, Semiring r) => LinearCombination r a -> LinearCombination r a
lcAggr = LinearCombination . map aggr . groupBy (<=>) . fromLinComb where
  a <=> b = snd a == snd b
  aggr as@((_,a):_) = (foldr (+) rZero $ map fst as,a)

--------------------------------------------------------------------------------
-- lcSort -

-- | sorting a word according to its symbols.
lcSort :: Ord a => LinearCombination r a -> LinearCombination r a
lcSort (LinearCombination as) = LinearCombination (sortSnd as)

--------------------------------------------------------------------------------
-- lcSclFilter -

-- | filtering a word according to the scalars.
lcSclFilter :: (r -> Bool) -> LinearCombination r a -> LinearCombination r a
lcSclFilter p (LinearCombination ws) = LinearCombination $ filter (p . fst) ws

--------------------------------------------------------------------------------
-- smflc -

-- | transforming a sum form to its corresponding word.
smflc :: Semiring r => SumForm r a -> LinearCombination r a
smflc sf = LinearCombination (tow sf) where
  tow sf = case sf of
    Zero _        -> []
    S a           -> [(rOne,a)]
    r :! a        -> map (\(s,a) -> (r*s,a)) $ tow a
    S a :+ b      -> (rOne,a):tow b
    r :! S a :+ b -> (r,a):tow b
    a :+ b        -> tow a ++ tow b
                   
--------------------------------------------------------------------------------
-- lcsmf -

-- | transforming a word to its corresponding sum form.
lcsmf :: Semiring r => Root a -> LinearCombination r a -> SumForm r a
lcsmf e (LinearCombination ws) = smf e ws where
  smf e ws = case ws of
    []      -> Zero e
    [(r,a)] -> if r == rOne then S a else (r :! S a)
    w:ws    -> smf e [w] :+ smf e ws

--------------------------------------------------------------------------------
-- smfReduce -

-- | reducing a sum form to its canonical form,
smfReduce :: (Fibred a, Ord a, Semiring r, Commutative r) => SumForm r a -> SumForm r a
smfReduce sf = lcsmf (root sf) $ lcSclFilter (not . isZero) $ lcAggr $ lcSort $ smflc sf

instance (Fibred a, Ord a, Semiring r, Commutative r) => Reducible (SumForm r a) where
  reduce = smfReduce

--------------------------------------------------------------------------------
-- Sum -

-- | free sum over 'Fibred' symbols in @__a__@ with scalars in @__r__@.
--
-- __Definition__ A 'Sum' @s@ is 'valid' if and only if its underlying 'SumForm' @s'@ is 'valid' and
-- @s'@ is reduced, i.e. @s' '==' 'reduce' s'@.
newtype Sum r a = Sum (SumForm r a) deriving (Show,Eq,Ord,Validable)

instance (Fibred a, Semiring r, Commutative r) => Entity (Sum r a)

--------------------------------------------------------------------------------
-- Sum - Constructable -

instance Exposable (Sum r a) where
  type Form (Sum r a) = SumForm r a
  form (Sum a) = a

instance (Fibred a, Ord a, Semiring r, Commutative r) => Constructable (Sum r a) where
  make = Sum . reduce
  
--------------------------------------------------------------------------------
-- Sum - Abelian -

instance (Fibred a, Semiring r, Commutative r) => Fibred (Sum r a) where
  type Root (Sum r a) = Root a
  root (Sum sf) = root sf
  
instance (Fibred a, Ord a, Semiring r, Commutative r) => Additive (Sum r a) where
  zero e = Sum (Zero e)
  Sum a + Sum b | root a == root b = make (a :+ b)
                | otherwise        = throw NotAddable

  ntimes n (Sum a) = make (ntimes n rOne :! a) 

instance (Fibred a, Ord a, Ring r, Commutative r) => Abelian (Sum r a) where
  negate (Sum a)   = make (negate rOne :! a) 
  ztimes z (Sum a) = make (ztimes z rOne :! a)

instance (Fibred a, Ord a, Semiring r, Commutative r) => Vectorial (Sum r a) where
  type Scalar (Sum r a) = r
  r ! (Sum a) = make (r :! a)
  
--------------------------------------------------------------------------------
-- smlc -

smlc :: Semiring r => Sum r a -> LinearCombination r a
smlc = restrict smflc

--------------------------------------------------------------------------------
-- smJoin -

smJoin :: (Semiring r, Commutative r, Fibred a, Ord a) => Sum r (Sum r a) -> Sum r a
smJoin = make . smfJoin . restrict (smfSum Zero (:!) (:+) (S . form))

--------------------------------------------------------------------------------
-- smMap -

smMap :: (Singleton (Root y), Fibred y, Ord y, Semiring r, Commutative r)
  => (x -> y) -> Sum r x -> Sum r y
smMap f (Sum s) = make (smfMap f s)

--------------------------------------------------------------------------------
-- nSum -

nSum :: (Hom Fbr h,Additive x) => h a x -> Sum N a -> x
nSum h = restrict (smfSum (zero . rmap h) ntimes (+) (amap h))

--------------------------------------------------------------------------------
-- zSum -

zSum :: (Hom Fbr h,Abelian x) => h a x -> Sum Z a -> x
zSum h = restrict (smfSum (zero . rmap h) ztimes (+) (amap h))

