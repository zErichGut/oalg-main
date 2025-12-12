
{-# LANGUAGE
  DeriveFoldable, DeriveFunctor
#-}

-- |
-- Module      : OAlg.Data.Tree
-- Description : binary trees for lookup
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- binary trees for lookup.
module OAlg.Data.Tree
  ( Tree(..), trLookup, trFilter
  )
  where

import Prelude

--------------------------------------------------------------------------------
-- Tree -

-- | binary tree with node element in @__i__@ and leaf element in @__x__@.
data Tree i x = Node i (Tree i x) (Tree i x) | Leaf x
  deriving (Show,Eq,Ord,Foldable,Functor)

--------------------------------------------------------------------------------
-- trLookup -

-- | lookup a value in a binary tree.
trLookup :: Ord i => Tree i x -> i -> x
trLookup (Leaf x) _     = x
trLookup (Node i l r) j = if j < i then trLookup l j else trLookup r j

--------------------------------------------------------------------------------
-- trFilter -

-- | the sub tree containing all leafs satisfying the given predicate.
trFilter :: (x -> Bool) -> Tree i x -> Maybe (Tree i x)
trFilter p t = fltr t where
  fltr (Leaf x)     = if p x then Just (Leaf x) else Nothing
  fltr (Node i l r) = case (fltr l,fltr r) of
    (Nothing,Just r') -> Just r'
    (Just l',Nothing) -> Just l'
    (Just l',Just r') -> Just $ Node i l' r'
    _                 -> Nothing
