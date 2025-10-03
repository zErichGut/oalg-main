
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Sequence.ProductSymbol
-- Description : free products of symbols
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- free products of symbols in @__x__@ with index type 'N'.
module OAlg.Entity.Product.ProductSymbol
  (
    -- * ProductSymbol
    ProductSymbol(..), sy, psyShow
  , psyxs, psywrd,wrdpsy, nProxy
  , psyJoin
  , productSymbol, psyLength, psyFactor
  , psyMap
  
    -- * X
  , xProductSymbol
  ) where

import Control.Monad

import Data.Typeable
import Data.Foldable
import Data.List (map,(++),filter)

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Constructable

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential

import OAlg.Entity.Product.Definition
import OAlg.Entity.Sequence.Definition
import OAlg.Entity.Sequence.Set

--------------------------------------------------------------------------------
-- ProductSymbol -

-- | free product of symbols in @__x__@ with index type 'N'.
--
--  __Example__
--
-- The expression @'sy' \'a\'@ constructs a free product of exactly one symbol in 'Char'
-- consisting just of the character @\'a\'@.
--
-- >>> sy 'a'
-- ProductSymbol['a']
--
-- they are 'Total' 'Multiplicative'
--
-- >>> sy 'a' * sy 'b' * sy 'c'
-- ProductSymbol['a'*'b'*'c']
--
-- and admit a listing
--
-- >>> list (Proxy :: Proxy N) (sy 'a' * sy 'b' * sy 'c')
-- [('a',0),('b',1),('c',2)]
--
-- they have a compact representation for repetitions
--
-- >>> sy 'a' * sy 'b' * sy 'b' * sy 'a' * sy 'c'
-- ProductSymbol['a'*'b'^2*'a'*'c']
--
-- >>> sy 'a' * sy 'b' * sy 'b' * sy 'a' * sy 'c' == sy 'a' * sy 'b' ^ 2 * sy 'a' * sy 'c'
-- True
--
-- but they are not 'Commutative'
--
-- >>> sy 'a' * sy 'b' ^ 2 * sy 'a' * sy 'c' == sy 'a' ^ 2 * sy 'b' ^ 2 * sy 'c'
-- False
--
-- and they admit a total right operation 'OAlg.Structure.Operational.<*' of
-- @t'OAlg.Entity.Sequence.Permutation.Permutation' 'N'@
--
-- >>> (sy 'a' * sy 'b' ^ 2 * sy 'a' * sy 'c') <* (pmtSwap 1 3 :: Permutation N)
-- ProductSymbol['a'^2*'b'^2*'c']
--
--  __Note__
--
-- (1) Free products of symbols are finite complete sequences and allow a compact
-- representation for repetitions and serve merely as dimensions for matrices
-- (see "OAlg.Entity.Matrix.Dim").
--
-- (2) Possibly infinite complete sequences are represented by @[__x__]@.  
newtype ProductSymbol x = ProductSymbol (Product N (U x))
  deriving (Eq,Ord,Validable,Multiplicative,Foldable,LengthN)

-- | showing as a product of symbols.
psyShow :: Entity x => ProductSymbol x -> String
psyShow (ProductSymbol xs) = shws $ map (\(U p,n) -> (p,n)) $ fromWord $ prwrd xs where
  shws ps = join $ tween "*" $ map shw ps
  shw (p,1) = show p
  shw (p,n) = show p ++ "^" ++ show n

instance Entity x => Show (ProductSymbol x) where
  show p = "ProductSymbol[" ++ psyShow p ++ "]"

type instance Point (ProductSymbol x) = ()
instance ShowPoint (ProductSymbol x)
instance EqPoint (ProductSymbol x)
instance ValidablePoint (ProductSymbol x)
instance TypeablePoint (ProductSymbol x)

instance Entity x => Oriented (ProductSymbol x) where
  orientation = const (():>())

instance Entity x => Exponential (ProductSymbol x) where
  type Exponent (ProductSymbol x) = N
  ProductSymbol xs ^ n = ProductSymbol (xs ^ n)

instance Exposable (ProductSymbol x) where
  type Form (ProductSymbol x) = ProductForm N (U x)
  form (ProductSymbol xs) = form xs
  
instance Entity x => Constructable (ProductSymbol x) where
  make p = ProductSymbol $ make p

--------------------------------------------------------------------------------
-- Canonical -

instance Entity x => Projectible (ProductSymbol x) [x] where
  prj = ProductSymbol . prj . Word . amap1 (\x -> (U x,1 :: N))

instance Entity x => Projectible (ProductSymbol x) (Word N x) where
  prj = ProductSymbol . prj  . amap1 U

--------------------------------------------------------------------------------
-- nProxy -

-- | proxy for 'N'.
nProxy :: Proxy N
nProxy = Proxy

--------------------------------------------------------------------------------
-- psyxs -

-- | the indexed listing of the symbols.
psyxs :: ProductSymbol x -> [(x,N)]
psyxs = list nProxy

--------------------------------------------------------------------------------
-- psywrd -

-- | the underlying word.
psywrd :: Entity x => ProductSymbol x -> Word N x
psywrd (ProductSymbol p) = Word $ map (\(U x,n) -> (x,n)) $ fromWord $ prwrd p

--------------------------------------------------------------------------------
-- wrdpsy -

-- | from word.
wrdpsy :: Entity x => Word N x -> ProductSymbol x
wrdpsy (Word ws) = make $ wrdprf () $ Word $ map (\(x,n) -> (U x,n)) $ ws
--------------------------------------------------------------------------------
-- productSymbol -

-- | the induced product of symbols.
productSymbol :: Entity x => [x] -> ProductSymbol x
productSymbol xs = ProductSymbol $ make $ foldl (:*) (One ()) $ map (P . U) xs

--------------------------------------------------------------------------------
-- csqSqc -

-- | the induce product of symbols given by a partial map and a support set.
csqSqc :: Entity x => (i -> Maybe x) -> Set i -> ProductSymbol x
csqSqc mx (Set is)
  = productSymbol
  $ map fromJust
  $ filter isJust
  $ map mx is

--------------------------------------------------------------------------------
-- ProductSymbol - Sequence -

instance Sequence ProductSymbol N x where
  list f (ProductSymbol p) = map (\(U x,i) -> (x,i)) $ list f p 
  ProductSymbol p ?? i = amap1 fromU (p ?? i)

instance Entity x => ConstructableSequence ProductSymbol N x where
  sequence = csqSqc
  
--------------------------------------------------------------------------------
-- sy -

-- | symbol of an entity, i.e. the complete sequence of 'psyLength' one consisting
--   just of it.
--
--  __Example__
--
-- >>> sy 'a'
-- ProductSymbol['a']
--
-- >>> sy 'a' * sy 'b' * sy 'b' ^ 5 * sy 'c'
-- ProductSymbol['a'*'b'^6*'c']
sy :: Entity x => x -> ProductSymbol x
sy x = productSymbol [x]

--------------------------------------------------------------------------------
-- psyLength -

-- | the length of a complete sequence.
psyLength :: ProductSymbol x -> N
psyLength (ProductSymbol xs) = prLength xs


--------------------------------------------------------------------------------
-- psyFactor -

-- | the symbol for the given index.
psyFactor :: ProductSymbol x -> N -> x
psyFactor (ProductSymbol xs) = (\(U x) -> x) . prFactor xs

--------------------------------------------------------------------------------
-- psyMap -

-- | mapping free products of symbols. 
psyMap :: Entity y => (x -> y) -> ProductSymbol x -> ProductSymbol y
psyMap f (ProductSymbol xs) = ProductSymbol $ prdMapTotal (fmap f) xs 


--------------------------------------------------------------------------------
-- psyJoin -

-- | joining complete sequences.
psyJoin :: Entity x => ProductSymbol (ProductSymbol x) -> ProductSymbol x
psyJoin (ProductSymbol xxs) = ProductSymbol $ make $ restrict (prfMapTotal f) xxs where
  f (U p) = restrict id p


--------------------------------------------------------------------------------
-- xProductSymbol -

-- | random variable of complete sequences with the given maximal length.
xProductSymbol :: Entity x => N -> X x -> X (ProductSymbol x)
xProductSymbol n xx = do
  n' <- xNB 0 n
  xs <- xTakeN n' xx
  return $ productSymbol xs

