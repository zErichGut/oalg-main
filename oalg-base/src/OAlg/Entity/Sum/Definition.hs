
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
    Sum(), smwrd

    -- * Form
  , SumForm(..), smfLength, smfwrd, wrdsmf
  , fromWord, wrdAggr, wrdSort, wrdSclFilter, Word(..)

    -- **
  , smfReduce
  ) where

import Data.List (map,groupBy,(++),filter)
import Data.Foldable
import Data.Monoid hiding (Sum)

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Reducible
import OAlg.Data.Constructable

import OAlg.Structure.Exception
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Ring.Definition
import OAlg.Structure.Number
import OAlg.Structure.Vectorial

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
-- Word -

-- | list of symbols in @__a__@ together with a scalar in @__r__@.
newtype Word r a = Word [(r,a)] deriving (Show,Eq,Validable)

instance (Entity a, Entity r) => Entity (Word r a)

--------------------------------------------------------------------------------
-- fromWord -

-- | the underlying list of symbols with their scalar.
fromWord :: Word r a -> [(r,a)]
fromWord (Word as) = as

--------------------------------------------------------------------------------
-- wrdAggr -

-- | aggregating words with same symbols.
wrdAggr :: (Eq a, Semiring r) => Word r a -> Word r a
wrdAggr = Word . map aggr . groupBy (<=>) . fromWord where
  a <=> b = snd a == snd b
  aggr as@((_,a):_) = (foldr (+) rZero $ map fst as,a)

--------------------------------------------------------------------------------
-- wrdSort -

-- | sorting a word according to its symbols.
wrdSort :: Ord a => Word r a -> Word r a
wrdSort (Word as) = Word (sortSnd as)

--------------------------------------------------------------------------------
-- wrdSclFilter -

-- | filtering a word according to the scalars.
wrdSclFilter :: (r -> Bool) -> Word r a -> Word r a
wrdSclFilter p (Word ws) = Word $ filter (p . fst) ws

--------------------------------------------------------------------------------
-- smfwrd -

-- | transforming a sum form to its corresponding word.
smfwrd :: Semiring r => SumForm r a -> Word r a
smfwrd sf = Word (tow sf) where
  tow sf = case sf of
    Zero _        -> []
    S a           -> [(rOne,a)]
    r :! a        -> map (\(s,a) -> (r*s,a)) $ tow a
    S a :+ b      -> (rOne,a):tow b
    r :! S a :+ b -> (r,a):tow b
    a :+ b        -> tow a ++ tow b
                   
--------------------------------------------------------------------------------
-- wrdsmf -

-- | transforming a word to its corresponding sum form.
wrdsmf :: Semiring r => Root a -> Word r a -> SumForm r a
wrdsmf e (Word ws) = smf e ws where
  smf e ws = case ws of
    []      -> Zero e
    [(r,a)] -> if r == rOne then S a else (r :! S a)
    w:ws    -> smf e [w] :+ smf e ws

--------------------------------------------------------------------------------
-- smfReduce -

-- | reducing a sum form to its canonical form,
smfReduce :: (Fibred a, Ord a, Semiring r, Commutative r) => SumForm r a -> SumForm r a
smfReduce sf = wrdsmf (root sf) $ wrdSclFilter (not . isZero) $ wrdAggr $ wrdSort $ smfwrd sf

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
-- smwrd -

smwrd :: Semiring r => Sum r a -> Word r a
smwrd = restrict smfwrd
