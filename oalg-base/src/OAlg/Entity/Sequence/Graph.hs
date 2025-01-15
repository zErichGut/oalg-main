
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : OAlg.Entity.Sequence.Graph
-- Description : graphs of entities
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- graphs of entities in @__x__@.
module OAlg.Entity.Sequence.Graph
  ( -- * Graph
    Graph(..), gphLength, gphxs, gphSqc, gphLookup, gphTakeN

    -- ** Lattice
  , gphUnion, gphIntersection, gphDifference, isSubGraph

    -- * Conversions
  , gphset, setgph
  ) where

import Control.Monad hiding (sequence)

import Data.List (head,map,filter,groupBy)

import OAlg.Prelude

import OAlg.Entity.Sequence.Set

import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Lattice

--------------------------------------------------------------------------------
-- Graph -

-- | mapping from an ordered /index/ type @__i__@ to a 'Entity' type @__x__@.
--
--  __Property__ Let @g = 'Graph' ixs@ be in @'Graph' __i__ __x__@ for a ordered 'Entity'
-- type @__i__@ and 'Entity' type @__x__@, then holds:
--
-- (1) For all @..(i,_)':'(j,_)..@ in @ixs@ holds: @i '<' j@.
--
-- (2) @'lengthN' g '==' 'lengthN' ixs@.
newtype Graph i x = Graph [(i,x)] deriving (Show,Eq,Ord,LengthN)

relGraph :: (Entity x, Entity i, Ord i) => Graph i x -> Statement
relGraph (Graph [])       = SValid
relGraph (Graph (ix:ixs)) = valid ix && vld (0::N) ix ixs where
  vld _ _ []                 = SValid
  vld k (i,_) (jx@(j,_):ixs) = And [ valid jx
                                   , (i<j) :?> Params ["k":=show k,"(i,j)":=show (i,j)]
                                   , vld (succ k) jx ixs
                                   ]

instance (Entity x, Entity i, Ord i) => Validable (Graph i x) where
  valid g = Label "Graph" :<=>: relGraph g

instance (Entity x, Entity i, Ord i) => Entity (Graph i x)

instance Functor (Graph i) where
  fmap f (Graph ixs) = Graph $ map (\(i,x) -> (i, f x)) ixs
  
--------------------------------------------------------------------------------
-- gphLookup -

-- | looks up the mapping of an index.
gphLookup :: Ord i => Graph i x -> i -> Maybe x
gphLookup (Graph ixs) = lookup ixs where
  lookup [] _           = Nothing
  lookup ((i',x):ixs) i = case i `compare` i' of
    LT -> Nothing
    EQ -> Just x
    GT -> lookup ixs i

--------------------------------------------------------------------------------
-- gphLength -

-- | the length of a graph.
gphLength :: Graph i x -> N
gphLength (Graph ixs) = lengthN ixs

--------------------------------------------------------------------------------
-- gphxs -

-- | the underlying associations.
gphxs :: Graph i x -> [(i,x)]
gphxs (Graph ixs) = ixs

--------------------------------------------------------------------------------
-- gphSqc -

-- | the induced graph given by a set of indices and a mapping.
gphSqc :: (i -> Maybe x) -> Set i -> Graph i x
gphSqc mx (Set is)
  = Graph
  $ map (\(i,jx) -> (i,fromJust jx))
  $ filter (isJust . snd)
  $ map (\i -> (i,mx i)) is

--------------------------------------------------------------------------------
-- gphTakeN -

-- | takes the first @n@ elements.
gphTakeN :: N -> Graph i x -> Graph i x
gphTakeN n (Graph ixs) = Graph $ takeN n ixs

--------------------------------------------------------------------------------
-- gphset -

-- | converts a graph of sets to a set of pairs. The /inverse/ is given by 'setgph'.
--
-- __Note__
--
-- (1) This works also with infinite graphs of sets.
--
-- (2) It is not true that 'setgph' and 'gphset' are inverse in the strict sense, but almost, i.e.
-- only in one restricts the graph to not empty associations. For example
-- @'Graph' [(1,'Set' []) :: 'Graph' 'N' ('Set' Char)@ and @'Graph' [] :: 'Graph' 'N' ('Set' Char)@
-- both are mapped under 'gphset' to @'Set' [] :: 'Set' ('N',Char)@.
gphset :: Graph a (Set b) -> Set (a,b)
gphset (Graph asb) = Set $ join $ amap1 (\(a,Set bs) -> amap1 (a,) bs) asb

--------------------------------------------------------------------------------
-- setgph -

-- | converts a set of pairs to a graph of sets. The /inverse/ is given by 'gphset'.
--
-- __Note__ This works also with infinite sets of pairs..
setgph :: Eq a => Set (a,b) -> Graph a (Set b)
setgph (Set ab) = Graph $ amap1 aggr $ groupBy (~) ab
  where (x,_) ~ (y,_) = x == y
        aggr abs = (fst $ head abs,Set $ amap1 snd abs)

--------------------------------------------------------------------------------
-- gphUnion -

gphUnion :: (Ord a, Ord b) => Graph a (Set b) -> Graph a (Set b) -> Graph a (Set b)
gphUnion (Graph xxs) (Graph yys) = Graph $ uni xxs yys where
  uni [] yys = yys
  uni xxs [] = xxs
  uni ((x,xs):xxs) ((y,ys):yys) = case x `compare` y of
    LT -> (x,xs) : uni xxs ((y,ys):yys)
    EQ -> (x,xs || ys) : uni xxs yys
    GT -> (y,ys) : uni ((x,xs):xxs) yys

--------------------------------------------------------------------------------
-- gphIntersection -

gphIntersection :: (Ord a, Ord b) => Graph a (Set b) -> Graph a (Set b) -> Graph a (Set b)
gphIntersection (Graph xxs) (Graph yys) = Graph $ intr xxs yys where
  intr ((x,xs):xxs) ((y,ys):yys) = case x `compare` y of
    LT -> intr xxs ((y,ys):yys)
    EQ -> (x,xs && ys) : intr xxs yys
    GT -> intr ((x,xs):xxs) yys
  intr _ _ = []

--------------------------------------------------------------------------------
-- ghpDifference -

gphDifference :: (Ord a, Ord b) => Graph a (Set b) -> Graph a (Set b) -> Graph a (Set b)
gphDifference (Graph xxs) (Graph yys) = Graph $ diff xxs yys where
  diff [] _   = []
  diff xxs [] = xxs
  diff ((x,xs):xxs) ((y,ys):yys) = case x `compare` y of
    LT -> (x,xs) : diff xxs ((y,ys):yys)
    EQ -> (x,xs // ys) : diff xxs yys
    GT -> diff ((x,xs):xxs) yys

--------------------------------------------------------------------------------
-- isSubGraph -

isSubGraph :: (Ord a, Ord b) => Graph a (Set b) -> Graph a (Set b) -> Bool
isSubGraph (Graph xxs) (Graph yys) = sub xxs yys where
  sub [] _ = True
  sub _ [] = False
  sub ((x,xs):xxs) ((y,ys):yys) = case x `compare` y of
    LT -> False
    EQ -> (xs <<= ys) && sub xxs yys 
    GT -> sub ((x,xs):xxs) yys
  
--------------------------------------------------------------------------------
-- Graph a (Set b) - Lattice -

instance (Ord a, Ord b) => Logical (Graph a (Set b)) where
  (||) = gphUnion
  (&&) = gphIntersection

instance (Ord a, Ord b) => Erasable (Graph a (Set b)) where (//) = gphDifference

instance (Ord a, Ord b) => PartiallyOrdered (Graph a (Set b)) where (<<=) = isSubGraph
instance (Ord a, Ord b) => Empty (Graph a (Set b)) where empty = Graph []

instance (Ord a, Ord b) => Lattice (Graph a (Set b))
