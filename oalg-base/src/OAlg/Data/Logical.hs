
-- |
-- Module      : OAlg.Data.Logical
-- Description : logical connectives.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Types admitting logical connectives.
module OAlg.Data.Logical
  ( -- * Logical Operators
    Logical(..), Erasable(..)
  )
  where

import Prelude hiding ((||),(&&))
import qualified Data.Bool as P

--------------------------------------------------------------------------------
-- Lagical -

-- | logical structures admitting a general definition for /disjunctions/ and /conjunctions/.
class Logical a where
  infixr 2 ||
  -- | disjunction
  (||) :: a -> a -> a
  
  infixr 3 &&  
  -- | conjunction
  (&&) :: a -> a -> a

instance Logical Bool where
  (||)  = (P.||)
  (&&)  = (P.&&)

instance Logical b => Logical (x -> b) where
  f || g = \x -> f x || g x
  f && g = \x -> f x && g x

--------------------------------------------------------------------------------
-- Erasable -

-- | erasor-operator.
class Erasable a where
  infixl 4 //
  -- | difference
  (//) :: a -> a -> a

instance Erasable Bool where a // b = a && not b

instance Eq x => Erasable [x] where
  xs // [] = xs
  [] // _  = []
  (x:xs) // (y:ys) = case x == y of
    True  -> xs // ys
    False -> x : (xs // (y:ys))


