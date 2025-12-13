{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}


-- |
-- Module      : OAlg.Structure.PartiallyOrdered.Definition
-- Description : partial orderings.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- partial orderings..
module OAlg.Structure.PartiallyOrdered.Definition
  ( -- * Partial Ordering
    PartiallyOrdered(..), Empty(..), Full(..)
  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented.Opposite

--------------------------------------------------------------------------------
-- PartiallyOrdered -

-- | partially ordered types.
--
--  __Properties__ Let @__a__@ be an instance of 'PartiallyOrdered', then holds:
--
--  (1) For all @x@ in @__a__@ holds: @x '<<=' x@.
--
--  (2) For all @x@, @y@ in @__a__@ holds: If @x '<<=' y@ and @y '<<=' x@ then
--  @x '==' y@.
--
--  (3) For all @x@, @y@, @z@ in @__a__@ holds: If @x '<<=' y@ and @y '<<=' z@ then
--  @x '<<=' z@.
class Eq a => PartiallyOrdered a where

  infix 4 <<=
  (<<=) :: a -> a -> Bool

instance PartiallyOrdered x => PartiallyOrdered (Op x) where Op x <<= Op y = y <<= x

instance PartiallyOrdered Bool where
  (<<=) = (<=)

instance Eq x => PartiallyOrdered [x] where
  [] <<= _  = True
  _ <<= []  = False
  (x:xs) <<= (y:ys) = case x == y of
    True  -> xs <<= ys
    False -> (x:xs) <<= ys

    
--------------------------------------------------------------------------------
-- Empty -

-- | the minimal element of a patrially ordered type..
--
-- __Property__ Let @__a__@ be an instance of 'Empty', then for all @x@ in @__a__@ holds:
-- @empty '<<=' x@.
class PartiallyOrdered a => Empty a where
  empty :: a
  isEmpty :: a -> Bool
  isEmpty x = x == empty
  
instance Empty Bool where
  empty = False

instance Eq x => Empty [x] where
  empty = []
  isEmpty [] = True
  isEmpty _  = False
  
--------------------------------------------------------------------------------
-- Full -

-- | the maximal element of a partially ordered type.
--
-- __Property__ Let @__a__@ be an instance of 'Full', then for all @x@ in @__a__@ holds:
-- @x '<<=' full@.
class PartiallyOrdered a => Full a where
  full :: a
  isFull :: a -> Bool
  isFull x = x == full
  
instance Full Bool where
  full = True

