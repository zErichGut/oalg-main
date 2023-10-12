
-- |
-- Module      : OAlg.Entity.Sequence
-- Description : sequences of indexed items
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Sequences of indexed items in a type @__x__@ with an index type @__i__@ and there
-- permutations. We consider two kinds of sequences:
--
-- [Complete] Sequences @x 0,x 1,x 2,..@ with an integral index type @__i__@ where there
-- indices don't have /wholes/ and start at @0@, e.g. @[__x__]@ or free products
-- of symbols in @__x__@ i.e. 'ProductSymbol'.
--
-- [Partial] Sequences @x i0,x i1,x i2,..@ with a totally ordered index type @__i__@  where
-- there indices allow /wholes/, e.g. 'PSequence', 'Set', 'Graph'.
--
-- Furthermore there are total right operations of 'Permutation' defined on them which
-- permutes the corresponding indices to yield a new sequence.
module OAlg.Entity.Sequence
  (   module D
    , module C
    , module P
    , module S
    , module G
    , module Prm
  ) where

import OAlg.Entity.Sequence.Set as S
import OAlg.Entity.Sequence.Graph as G
import OAlg.Entity.Sequence.Definition as D
import OAlg.Entity.Sequence.ProductSymbol as C
import OAlg.Entity.Sequence.PSequence as P
import OAlg.Entity.Sequence.Permutation as Prm
