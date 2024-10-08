{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


-- |
-- Module      : OAlg.Entity.Sum.SumSymbol
-- Description : free sums over symbols.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- free sums with symbols in @__a__@.
module OAlg.Entity.Sum.SumSymbol
  ( -- * SumSymbol
    SumSymbol(..), ssypsq, ssylc, sumSymbol, sy, ssyMap, ssySum, ssyJoin
  , ssyprj

    -- * R
  , R(..)
  
  ) where

import Control.Monad

import Data.List (map,repeat,zip,(++))
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Constructable

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
import OAlg.Structure.Vectorial

import OAlg.Entity.Sequence hiding (sy)
import OAlg.Entity.Sum.Definition

--------------------------------------------------------------------------------
-- R -

-- | adjoining the root @()@.
newtype R a = R a deriving (Show,Eq,Ord,Validable)

instance Entity a => Entity (R a)

instance Entity a => Fibred (R a) where
  type Root (R a) = ()
  root _ = ()

instance OrdRoot (R a)

--------------------------------------------------------------------------------
-- SumSymbol -

-- | free sum with symbols in @__a__@.
newtype SumSymbol r a = SumSymbol (Sum r (R a)) deriving (Eq,Ord,Validable,Additive,Abelian)

--------------------------------------------------------------------------------
-- ssylc -

-- | the underlying linear combination.
ssylc :: Semiring r => SumSymbol r a -> LinearCombination r a
ssylc (SumSymbol s) = LinearCombination $ map (\(r,R a) -> (r,a)) $ lcs $ smlc s

--------------------------------------------------------------------------------
-- ssypsq -

-- | the underlying partial sequence.
ssypsq :: Semiring r => SumSymbol r a -> PSequence a r
ssypsq x = PSequence $ lcs $ ssylc x

--------------------------------------------------------------------------------
-- SumSymbol - Entity -

ssyShow :: (Semiring r, Show a) => SumSymbol r a -> String
ssyShow s = shws $ lcs $ ssylc s where
  shws ss = join $ tween "+" $ map shw ss
  shw (r,a) | r == rOne = show a
            | otherwise = show r ++ "!" ++ show a

instance (Semiring r, Show a) => Show (SumSymbol r a) where
  show s = "SumSymbol[" ++ ssyShow s ++ "]"

instance (Semiring r, Commutative r, Entity a) => Entity (SumSymbol r a)

--------------------------------------------------------------------------------
-- SumSymbol - Fibred - Vectorial -

instance (Semiring r, Commutative r, Entity a) => Fibred (SumSymbol r a) where
  type Root (SumSymbol r a) = ()
  root _ = ()

instance (Semiring r, Commutative r, Entity a, Ord a) => Vectorial (SumSymbol r a) where
  type Scalar (SumSymbol r a) = r
  r ! (SumSymbol a) = SumSymbol (r ! a)

instance (Semiring r, Commutative r, Entity a, Ord a) => Euclidean (SumSymbol r a) where
  x <!> y
    = foldl (+) rZero
    $ map fst
    $ psqxs
    $ psqInterlace (*) (const rZero) (const rZero) (ssypsq x) (ssypsq y)

--------------------------------------------------------------------------------
-- Canonical -

instance (Entity a, Ord a, Semiring r, Commutative r) => Projectible (SumSymbol r a) [a] where
  prj = SumSymbol . prj . Sheaf () . amap1 R

instance (Entity a, Ord a, Semiring r, Commutative r)
  => Projectible (SumSymbol r a) (LinearCombination r a) where
  prj = SumSymbol . make . foldr (+!) (Zero ()) . lcs where (x,a) +! b = x :! S (R a) :+ b

instance (Entity a, Ord a, Semiring r, Commutative r)
  => Projectible (SumSymbol r a) (LinearCombination r (SumSymbol r a)) where
  prj xs = SumSymbol
         $ make
         $ smfJoin
         $ lcsmf ()
         $ amap1 (\(SumSymbol s) -> form s) xs
    
--------------------------------------------------------------------------------
-- sumSymbol -

-- | the induced free sum given by a list of scalars and symbols.
sumSymbol :: (Semiring r, Commutative r, Entity a, Ord a) => [(r,a)] -> SumSymbol r a
sumSymbol = prj . LinearCombination

--------------------------------------------------------------------------------
-- sy -

-- | the induced free sum given by the symbol.
sy :: (Semiring r, Commutative r, Entity a, Ord a) => a -> SumSymbol r a
sy a = sumSymbol [(rOne,a)]

--------------------------------------------------------------------------------
-- ssyMap -

-- | mapping of free sums
ssyMap :: (Semiring r, Commutative r, Entity y, Ord y) => (x -> y) -> SumSymbol r x -> SumSymbol r y
ssyMap f (SumSymbol s) = SumSymbol (smMap f' s) where
  f' (R x) = R (f x)

--------------------------------------------------------------------------------
-- ssySum -

-- | additive homomorphism given by a mapping of a symbol in @__x__@ to a linear combination of
-- @__y__@.
ssySum :: (Semiring r, Commutative r, Entity y, Ord y)
  => (x -> LinearCombination r y) -> SumSymbol r x -> SumSymbol r y
ssySum f (SumSymbol s) = SumSymbol $ make $ smfJoin $ smfMap (f' f) $ form s where
  f' :: Semiring r => (x -> LinearCombination r y) -> R x -> SumForm r (R y)
  f' f (R x) = lcsmf () $ LinearCombination $ amap1 (\(r,y) -> (r,R y)) $ lcs $ f x

--------------------------------------------------------------------------------
-- ssyJoin -

-- | joining a free sum of free sums to a free sum.
ssyJoin :: (Semiring r, Commutative r, Entity x, Ord x)
  => SumSymbol r (SumSymbol r x) -> SumSymbol r x
ssyJoin (SumSymbol s) = SumSymbol $ make $ smfJoin $ smfMap f $ form s where
  f :: R (SumSymbol r x) -> SumForm r (R x)
  f (R (SumSymbol s)) = form s

--------------------------------------------------------------------------------
-- ssyprj -

-- | the projectin of a free sum according to the given set of symbols.
--
-- __Definition__ Let @x@ be in @'SumSymbol' __r__ __a__@ and @s@ a 'Set' of symbols in
-- @__a__@, then @x@ is called __/representable according to/__ @s@ iff all symbols of @'ssylc' x@
-- are elements of @s@.
--
-- __Property__ Let @s@ be a set of symbols in @__a__@ and @x@ be representable in
-- @'SumSymbol' __r__ __a__@ according to @s@, then @'ssyprj' x '==' x@.
--
-- __Examples__ 
--
-- >>> ssyprj (Set [A,D,E]) (3!sy D) :: SumSymbol Z Symbol
-- SumSymbol[3!D]
--
-- >>> ssyprj (Set [A,D,E]) (2!sy B) :: SumSymbol Z Symbol
-- SumSymbol[]
--
-- >>> ssyprj (Set [A,D,E]) (3!sy D + sy A - 5!sy E) :: SumSymbol Z Symbol
-- SumSymbol[A+3!D+-5!E]
--
-- >>> ssyprj (Set [A,D,E]) (2!sy D + 7!sy B - sy E + sy F) :: SumSymbol Z Symbol
-- SumSymbol[2!D+-1!E]
ssyprj :: (Semiring r, Commutative r, Ord a, Entity a) => Set a -> SumSymbol r a -> SumSymbol r a
ssyprj xs x = sumSymbol $ psqxs $ psqInterlace (*) (const rZero) (const rZero) xs' (ssypsq x)
  where xs' = PSequence (repeat rOne `zip` setxs xs )

