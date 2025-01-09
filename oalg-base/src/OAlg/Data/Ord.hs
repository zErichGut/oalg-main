
-- |
-- Module      : OAlg.Data.Ord
-- Description : ordering
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- "Data.Ord" enriched with some additional elements.
module OAlg.Data.Ord
  ( -- * Total Ordering
    module Ord
  , fcompare, wcompare, coCompare, compare2
  , sortFst, sortFstBy, sortSnd, sortSndBy
  , Closure(..), cmin, cmax, cspan, Span, enumSpan

    -- * Partial Ordering
  , POrd(..)

    -- * Lattices
  , Lattice, ErasabelLattice(..)
  )
  where
import Prelude as P hiding ((||),(&&))

import Data.List (sortBy)
import Data.Ord as Ord

import OAlg.Data.Boolean.Definition

--------------------------------------------------------------------------------
-- fcompare -

-- | comparing according to the mapped values.
fcompare :: Ord i => (a -> i) -> a -> a -> Ordering
fcompare f x y = compare (f x) (f y)

--------------------------------------------------------------------------------
-- wcompare -

-- | comparing according to the given ordering relation on the mapped values.
wcompare :: (w -> w -> Ordering) -> (a -> w) -> a -> a -> Ordering
wcompare cmp f x y = cmp (f x) (f y)

--------------------------------------------------------------------------------
-- coCompare -

-- | the /reverse/ ordering
coCompare :: (a -> a -> Ordering) -> a -> a -> Ordering
coCompare cmp x y = cmp y x

--------------------------------------------------------------------------------
-- compare2 -

-- | comparing of pairs.
compare2 :: (a -> a -> Ordering) -> (b -> b -> Ordering) -> (a,b) -> (a,b) -> Ordering
compare2 acmp bcmp (a,b) (a',b') = case a `acmp` a' of
  EQ -> b `bcmp` b'
  o  -> o

--------------------------------------------------------------------------------
-- sortFstBy -

-- | sorting according to the first component.
sortFstBy :: (a -> a -> Ordering) -> [(a,b)] -> [(a,b)]
sortFstBy cmp = sortBy (wcompare cmp fst)

--------------------------------------------------------------------------------
-- sortFst -

-- | sorting according to the first component.
sortFst :: Ord a => [(a,b)] -> [(a,b)]
sortFst = sortFstBy compare

--------------------------------------------------------------------------------
-- sortSndBy -

-- | sorting according to the second component.
sortSndBy :: (b -> b -> Ordering) -> [(a,b)] -> [(a,b)]
sortSndBy cmp = sortBy (wcompare cmp snd)

--------------------------------------------------------------------------------
-- sortSnd -

-- | sorting according to the second component.
sortSnd :: Ord b => [(a,b)] -> [(a,b)]
sortSnd = sortSndBy compare

--------------------------------------------------------------------------------
-- Closure -

-- | the closer of a linear ordered @__x__@.
data Closure x
  = NegInf
  | It x
  | PosInf
  deriving (Show,Read,Eq,Ord)

--------------------------------------------------------------------------------
-- cmax -

-- | the maximum of the items of a list, i.e. the smallest upper bound.
--
--  __Property__ Let @xs@ be in @[__x__]@ for a linear ordered @__x__@, then holds:
--  For all @x@ in @xs@ holds: @'It' x '<=' 'cmax' xs@.
cmax :: Ord x => [x] -> Closure x
cmax []     = NegInf
cmax (x:xs) = max (It x) (cmax xs)

--------------------------------------------------------------------------------
-- cmin -

-- | the minimum of the items of a list, i.e. the biggest lower bound.
--
--  __Property__ Let @xs@ be in @[__x__]@ for a linear ordered @__x__@, then holds:
--  For all @x@ in @xs@ holds: @'cmin' xs '<=' 'It' x@.
cmin :: Ord x => [x] -> Closure x
cmin []     = PosInf
cmin (x:xs) = min (It x) (cmin xs)

--------------------------------------------------------------------------------
-- Span -

-- | the span type.
type Span x = (Closure x,Closure x)

--------------------------------------------------------------------------------
-- cspan -

-- | @(l,u) = 'cspan' xs@ where @l@ is the minimum and @u@ the maximum of the items in
--   @xs@.
--
--  __Example__
--
-- >>> cspan "aeb"
-- (It 'a',It 'e')
--
-- >>> cspan ""
-- (PosInf,NegInf)
cspan :: Ord x => [x] -> Span x
cspan []     = (PosInf,NegInf)
cspan (x:xs) = (min (It x) l,max (It x) u) where (l,u) = cspan xs

--------------------------------------------------------------------------------
-- enumSpan -

-- | @'enumSpan' i0 h@ enumerates the index, starting by @i0@ to @h@. 
enumSpan :: (Enum i, Ord i) => i -> Closure i -> [i]
enumSpan i0 h | h < It i0 = []
enumSpan i0 PosInf        = [i0..]
enumSpan i0 (It h)        = [i0..h]
enumSpan _ NegInf         = []

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

--------------------------------------------------------------------------------
-- Lattice -

-- | lattices on partially orderd sets.
--
-- __Properties__ Let @__a__@ be an instance of 'Lattice', then holds:
--
-- (1) For all @x@ and @y@ in @__a__@ holds:
--
--     (1) @x '<<=' (x '||' y)@ and @y '<<=' (x '||' y)@.
--
--     (2) For all @z@ with @x '<<=' z@ and @y '<<=' z@ holds: @(x '||' y) '<<=' z@. 
--
-- (2) For all @x@ and @y@ in @__a__@ holds:
--
--     (1) @x '&&' y '<<=' x@ and @x '&&' y '<<=' y@
--
--     (2) For all @z@ with @z '<<=' x@ and @z '<<=' y@ holds: @z '<<=' (x '&&' y) @. 
class (POrd a, Logical a) => Lattice a 

instance POrd Bool where
  (<<=) = (<=)

instance Lattice Bool

--------------------------------------------------------------------------------
-- ErasableLattice -


-- | lattices admitting an erasor-operator.
--
-- __Properties__ Let @__a__@ be an instance of 'ErasabelLattice', then
-- for all @x@ and @y@ in @__a__@ holds:
--
-- (1) @x // y '<<=' x@.
class Lattice a => ErasabelLattice a where
  infixl 4 //
  -- | difference
  (//) :: a -> a -> a
