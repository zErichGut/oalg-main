
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
  ( 
  ) where

import Control.Monad

import Data.List ((++),filter,splitAt)
import Data.Foldable

import Data.Maybe

import OAlg.Prelude

import OAlg.Entity.Sequence.PSequence

--------------------------------------------------------------------------------
-- DefaultValue -

class DefaultValue d i x where
  defaultValue :: d -> i -> x

--------------------------------------------------------------------------------
-- isDefaultValue -

isDefaultValue :: (DefaultValue d i x, Eq x) => d -> i -> x -> Bool
isDefaultValue d i x = x == defaultValue d i

--------------------------------------------------------------------------------
-- Tree -

data Tree i x
  = Empty
  | Leaf x
  | Node i (Tree i x) (Tree i x)
  deriving (Show,Eq,Ord,Foldable)

--------------------------------------------------------------------------------
-- psqTree -

psqTree :: PSequence i x -> Tree i x
psqTree (PSequence xis) = toTree xis where
  toTree []      = Empty
  toTree [(x,i)] = Node i Empty (Leaf x)
  toTree xis     = Node i (toTree l) (toTree r) where
    (l,r@((_,i):_)) = splitAt (length xis `divInt` 2) xis

--------------------------------------------------------------------------------
-- psqFromTree -

psqFromTree :: Tree i x -> PSequence i x
psqFromTree = error "nyi"

--------------------------------------------------------------------------------
-- lookup -

lookup :: Ord i => i -> Tree i x -> Maybe x
lookup i t = lk i t where
  lk i t = case (i,t) of
    (_,Empty)                  -> Nothing
    (i,Node i' Empty (Leaf x)) -> if i == i' then Just x else Nothing
    (i,Node i' l r)            -> if i <  i' then lk i l else lk i r

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
rdcFSequenceForm f@(FSequenceForm d (PSequence xis)) = FSequenceForm d (PSequence xis') where
  xis' = filter (notIsDefault f d) xis

  notIsDefault :: (DefaultValue d i x, Eq x) => f d i x -> d -> (x,i) -> Bool
  notIsDefault _ d (x,i) = not $ isDefaultValue d i x
                     
--------------------------------------------------------------------------------
-- FSequcne -

data FSequence d i x = FSequence d (Tree i x)

--------------------------------------------------------------------------------
-- fsq -

fsq :: (DefaultValue d i x, Ord i) => FSequence d i x -> i -> x
fsq (FSequence d t) i = case i `lookup` t of
  Just x  -> x
  Nothing -> defaultValue d i
  
--------------------------------------------------------------------------------
-- fsqForm -

fsqForm :: (DefaultValue d i x, Eq x) => FSequence d i x -> FSequenceForm d i x
fsqForm (FSequence d t) = FSequenceForm d (PSequence xis) where
  xis = filter (notIsDefault d)
      $ psqxs
      $ psqFromTree t

  notIsDefault :: (DefaultValue d i x, Eq x) => d -> (x,i) -> Bool
  notIsDefault d (x,i) = not $ isDefaultValue d i x

{-
--------------------------------------------------------------------------------
-- psqFromTree -

psqFromTree :: Tree i (Maybe (x,i)) -> PSequence i x
psqFromTree = PSequence . amap1 fromJust . filter isJust . toList

--------------------------------------------------------------------------------
-- psqTree -

psqTree :: PSequence i x -> Maybe (Tree i (x,i))
psqTree (PSequence [])  = Nothing
{-
psqTree (PSequence xis) = Just $ toTree xis where
  toTree :: [(x,i)] -> Tree i x
  toTree [(x,_)] = Leaf x
  toTree xis     = Node i (toTree l) (toTree r) where
    (l,r@((_,i):_)) = splitAt (length xis `divInt` 2) xis
-}

--------------------------------------------------------------------------------
-- fsqTree -

fsqTree :: (DefaultValue d i x, Eq x) => d -> PSequence i x -> Maybe (Tree i (Maybe (x,i)))
fsqTree d xis
  = psqTree
  $ PSequence
  $ amap1 (\(x,i) -> (if isDefaultValue d i x then Nothing else Just (x,i),i))
  $ psqxs xis

--------------------------------------------------------------------------------
-- fsqForm -

fsqForm :: FSequence d i x -> FSequenceForm d i x
fsqForm (FSequence d xs) = FSequenceForm d xs' where
  xs' = case xs of
          Nothing -> PSequence []
          Just t  -> psqFromTree t

--------------------------------------------------------------------------------
-- fsqMake -

fsqMake :: (DefaultValue d i x, Eq x) => FSequenceForm d i x -> FSequence d i x
fsqMake (FSequenceForm d xs) = FSequence d (fsqTree d xs)

--------------------------------------------------------------------------------
-- Entity -

instance (DefaultValue d i x, Eq x, Show d, Show i, Show x) => Show (FSequence d i x) where
  show s = "FSequence " ++ show d ++ "(" ++ show xis ++ ")" where
    FSequenceForm d xis = fsqForm s

instance (DefaultValue d i x, Eq d, Eq i,Eq x) => Eq (FSequence d i x) where
  s == t = fsqForm s == fsqForm t

instance (DefaultValue d i x, Ord d, Ord i,Ord x) => Ord (FSequence d i x) where
  compare s t = compare (fsqForm s) (fsqForm t)


-}
