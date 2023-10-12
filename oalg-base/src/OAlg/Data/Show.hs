
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : OAlg.Data.Show
-- Description : showing data
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- showing data with some auxiliary functions.
module OAlg.Data.Show
  (  -- * Show
    Show(..), tween, jtween, Show1(..), Show2(..)
  , String, Char
  
     -- * Read
  , Read, read
  )
  where

import Control.Monad (join)
import Data.Proxy

--------------------------------------------------------------------------------
-- tween -

-- | inserting the given value in between the elements of the given list.
--
--  __Examples__
--
-- >>> tween ',' "12345"
-- "1,2,3,4,5"
--
-- >>> tween ',' ""
-- ""
--
-- >>> tween ',' "1"
-- "1"
tween :: a -> [a] -> [a]
tween d (x:ys@(_:_)) = x:d:tween d ys
tween _ xs           = xs

--------------------------------------------------------------------------------
-- jtween

-- | inserting the given list in between the elements of the given list and joining the result.
--
-- __ Example__
--
-- >>> jtween ";" ["abcd","efg"]
-- "abcd;efg"
jtween :: [a] -> [[a]] -> [a]
jtween ds xs = join (tween ds xs)

--------------------------------------------------------------------------------
-- Show1 -

-- | showable for one parameterized types.
class Show1 p where
  show1 :: p x -> String
  default show1 :: Show (p x) => p x -> String
  show1 = show

instance Show1 Proxy
--------------------------------------------------------------------------------
-- Show2 -

-- | showable for two parameterized types.
--
--  __Note__ We use this class mearly in the context of 'OAlg.Category.Path'.
class Show2 h where
  show2 :: h a b -> String
  default show2 :: Show (h a b) => h a b -> String
  show2 = show

