
-- |
-- Module      : OAlg.Data.Tree
-- Description : binary trees for lookup
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- binary trees for lookup.
module OAlg.Data.Tree
  ( Tree(..), lookup
  )
  where

import Prelude hiding (lookup)

--------------------------------------------------------------------------------
-- Tree -

-- | binary tree with node element in @__i__@ and leaf element in @__x__@.
data Tree i x = Node i (Tree i x) (Tree i x) | Leaf x


-- | lookup a value in a binary tree.
lookup :: Ord i => Tree i x -> i -> x
lookup (Leaf x) _     = x
lookup (Node i l r) j = if j < i then lookup l j else lookup r j

