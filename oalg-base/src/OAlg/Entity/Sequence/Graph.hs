
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
    Graph(..), gphLength, gphxs, gphSqc, gphLookup
  ) where

import Control.Monad hiding (sequence)

import Data.List (map,filter)

import OAlg.Prelude

import OAlg.Entity.Sequence.Set

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
