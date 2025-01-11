
-- |
-- Module      : OAlg.Data.POrd
-- Description : partial orderings.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- partial orderings..
module OAlg.Data.POrd
  ( -- * Partial Ordering
    POrd(..), Empty(..), Full(..)
  )
  where

--------------------------------------------------------------------------------
-- POrd -

-- | partially ordered types.
--
--  __Properties__ Let @__a__@ be an instance of 'POrd', then holds:
--
--  (1) For all @x@ in @__a__@ holds: @x '<<=' x@.
--
--  (2) For all @x@, @y@ in @__a__@ holds: If @x '<<=' y@ and @y '<<=' x@ then
--  @x '==' y@.
--
--  (3) For all @x@, @y@, @z@ in @__a__@ holds: If @x '<<=' y@ and @y '<<=' z@ then
--  @x '<<=' z@.
class Eq a => POrd a where

  infix 4 <<=
  (<<=) :: a -> a -> Bool

instance POrd Bool where
  (<<=) = (<=)

--------------------------------------------------------------------------------
-- Empty -

-- | the minimal element of a patrial ordering.
--
-- __Property__ Let @__a__@ be an instance of 'Empty', then for all @x@ in @__a__@ holds:
-- @empty '<<=' x@.
class POrd a => Empty a where
  empty :: a
  isEmpty :: a -> Bool
  isEmpty x = x == empty
  
instance Empty Bool where
  empty = False

--------------------------------------------------------------------------------
-- Full -

-- | the maximal element of a partial ordering.
--
-- __Property__ Let @__a__@ be an instance of 'Full', then for all @x@ in @__a__@ holds:
-- @x '<<=' full@.
class POrd a => Full a where
  full :: a
  isFull :: a -> Bool
  isFull x = x == full
  
instance Full Bool where
  full = True
