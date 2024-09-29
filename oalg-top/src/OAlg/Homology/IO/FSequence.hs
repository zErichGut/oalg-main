
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
           , DeriveFoldable
           , DeriveFunctor
#-}


-- |
-- Module      : OAlg.Homology.IO.FSequence
-- Description : sequneces with finite support
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Sequences with finite support, i.e total sequences of values according to a totally ordered index
-- where only finitely many values are unequal to the default value.
--
-- The implementation is optimized for:
--
-- - retrieving the values by an index.
--
-- - values which may have a very time consuming evaluation. 
module OAlg.Homology.IO.FSequence
  ( -- * FSequence
    FSequence(),fsq, fsqD, fsqForm, fsqMake

    -- * Form
  , FSequenceForm(..), rdcFSequenceForm

    -- * Default Value
  , DefaultValue(..)
  ) where

import Control.Monad

import Data.List (head,(++),filter,splitAt)
import Data.Foldable

import Data.Maybe

import OAlg.Prelude

import OAlg.Data.Constructable
import OAlg.Entity.Sequence.PSequence

--------------------------------------------------------------------------------
-- DefaultValue -

class DefaultValue d i x where
  defaultValue :: d -> i -> x

--------------------------------------------------------------------------------
-- isDefaultValue -

isDefaultValue :: (DefaultValue d i x, Eq x) => d -> (x,i) -> Bool
isDefaultValue d (x,i) = x == defaultValue d i

--------------------------------------------------------------------------------
-- Tree -

data Tree i x
  = Leaf i x
  | Node i (Tree i x) (Tree i x)
  deriving (Show,Eq,Ord,Foldable,Functor)

--------------------------------------------------------------------------------
-- psqTree -

psqTree :: PSequence i x -> Maybe (Tree i x)
psqTree (PSequence [])  = Nothing
psqTree (PSequence xis) = Just $ toTree xis where
  toTree [(x,i)] = Leaf i x
  toTree xis     = Node (snd $ head r) (toTree l) (toTree r) where
    (l,r) = splitAt (length xis `divInt` 2) xis

--------------------------------------------------------------------------------
-- psqFromTree -

psqFromTree :: Maybe (Tree i x) -> PSequence i x
psqFromTree Nothing  = psqEmpty
psqFromTree (Just t) = PSequence (ft t) where
  ft (Leaf i x)   = [(x,i)]
  ft (Node _ l r) = ft l ++ ft r

--------------------------------------------------------------------------------
-- Entity - Tree -

instance (Entity i, Entity x, Ord i) => Validable (Tree i x) where
  valid t = Label "Tree" :<=>: vld t where
    vld (Node i l r)  = valid i && vldl i l && vldr i r
    vld (Leaf i x)    = valid i && valid x

    vldl i t = Label "l" :<=>: case t of
      Leaf i' _   -> And [ vld t
                         , (i' < i) :?> Params ["i":=show i,"i'":=show i']
                         ]
      Node i' l r -> valid i' && vldl i' l && vldr i' r
      
    vldr i t = Label "r" :<=>: case t of
      Leaf i' _   -> And [ vld t
                         , (i <= i') :?> Params ["i":=show i,"i'":=show i']
                         ]
      Node i' l r -> valid i' && vldl i' l && vldr i' r
    
--------------------------------------------------------------------------------
-- lookup -

lookup :: Ord i => i -> Maybe (Tree i x) -> Maybe x
lookup _ Nothing  = Nothing
lookup i (Just t) = lk i t where
  lk i (Leaf i' x)   = if i == i' then Just x else Nothing
  lk i (Node i' l r) = if i <  i' then lk i l else lk i r

--------------------------------------------------------------------------------
-- FSeqenceForm -

data FSequenceForm d i x = FSequenceForm d (PSequence i x)
  deriving (Show,Eq,Ord)

instance (Validable d, Entity i, Ord i, Entity x) => Validable (FSequenceForm d i x) where
  valid (FSequenceForm d xs) = Label "FSequence"
    :<=>: And [ valid d
              , valid xs
              ]

instance (Entity d, Entity i, Ord i, Entity x) => Entity (FSequenceForm d i x)

--------------------------------------------------------------------------------
-- rdcFSequenceForm -

rdcFSequenceForm :: (DefaultValue d i x, Eq x) => FSequenceForm d i x -> FSequenceForm d i x
rdcFSequenceForm (FSequenceForm d (PSequence xis)) = FSequenceForm d (PSequence xis') where
  xis' = filter (not . isDefaultValue d) xis

--------------------------------------------------------------------------------
-- FSequcne -

data FSequence d i x = FSequence d (Maybe (Tree i x)) deriving (Foldable, Functor)

--------------------------------------------------------------------------------
-- fsqD -

fsqD :: FSequence d i x -> d
fsqD (FSequence d _) = d

--------------------------------------------------------------------------------
-- fsq -

fsq :: (DefaultValue d i x, Ord i) => FSequence d i x -> i -> x
fsq (FSequence d t) i = case i `lookup` t of
  Just x  -> x
  Nothing -> defaultValue d i

--------------------------------------------------------------------------------
-- fsqForm -

fsqForm :: (DefaultValue d i x, Eq x) => FSequence d i x -> FSequenceForm d i x
fsqForm (FSequence d t) = rdcFSequenceForm $ FSequenceForm d (psqFromTree t)

--------------------------------------------------------------------------------
-- fsqMake -

fsqMake :: FSequenceForm d i x -> FSequence d i x
fsqMake (FSequenceForm d xis) = FSequence d (psqTree xis)

--------------------------------------------------------------------------------
-- FSequence - Entity -

instance (DefaultValue d i x,Eq x, Show d, Show i, Show x) => Show (FSequence d i x) where
  show f@(FSequence d _) = "FSequence (" ++ show d ++ ") (" ++ show xis ++ ")" where
    FSequenceForm _ xis = fsqForm f

instance (DefaultValue d i x,Eq d, Eq i,Eq x) => Eq (FSequence d i x) where
  f == g = fsqForm f == fsqForm g

instance (DefaultValue d i x,Ord d, Ord i,Ord x) => Ord (FSequence d i x) where
  compare f g = compare (fsqForm f) (fsqForm g)

instance (Entity d, Entity i, Entity x, Ord i) => Validable (FSequence d i x) where
  valid (FSequence d t) = Label "FSequence" :<=>: valid d && valid t

instance (DefaultValue d i x, Entity d, Entity i, Entity x, Ord i) => Entity (FSequence d i x)

--------------------------------------------------------------------------------
-- FSequence - Constructable -

instance (DefaultValue d i x, Eq x) => Exposable (FSequence d i x) where
  type Form (FSequence d i x) = FSequenceForm d i x
  form = fsqForm

instance (DefaultValue d i x, Eq x) => Constructable (FSequence d i x) where
  make = fsqMake
