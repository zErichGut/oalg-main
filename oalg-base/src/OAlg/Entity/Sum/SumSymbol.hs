{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


-- |
-- Module      : OAlg.Entity.Sum.SumSymbol
-- Description : free sums over symbols.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- free sums over symbols.
module OAlg.Entity.Sum.SumSymbol
  ( -- * SumSymbol
    SumSymbol(..), ssylc, sumSymbol, sy, ssMap, ssSum, ssJoin

    -- * R
  , R(..)
  
  ) where

import Control.Monad

import Data.List (map,(++))
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Constructable

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
import OAlg.Structure.Vectorial

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

newtype SumSymbol r a = SumSymbol (Sum r (R a)) deriving (Eq,Ord,Validable,Additive,Abelian)

--------------------------------------------------------------------------------
-- ssylc -

ssylc :: Semiring r => SumSymbol r a -> LinearCombination r a
ssylc (SumSymbol s) = LinearCombination $ map (\(r,R a) -> (r,a)) $ lcs $ smlc s

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

--------------------------------------------------------------------------------
-- sumSymbol -

sumSymbol :: (Semiring r, Commutative r, Entity a, Ord a) => [(r,a)] -> SumSymbol r a
sumSymbol xs = SumSymbol $ make $ foldr (:+) (Zero ()) $ map (\(r,a) -> r :! (S $ R a)) xs

--------------------------------------------------------------------------------
-- sy -

sy :: (Semiring r, Commutative r, Entity a, Ord a) => a -> SumSymbol r a
sy a = sumSymbol [(rOne,a)]

--------------------------------------------------------------------------------
-- ssMap -

ssMap :: (Semiring r, Commutative r, Entity y, Ord y) => (x -> y) -> SumSymbol r x -> SumSymbol r y
ssMap f (SumSymbol s) = SumSymbol (smMap f' s) where
  f' (R x) = R (f x)

--------------------------------------------------------------------------------
-- ssSum -

ssSum :: (Ring r, Commutative r, Entity y, Ord y)
  => (x -> LinearCombination r y) -> SumSymbol r x -> SumSymbol r y
ssSum f (SumSymbol s) = SumSymbol $ make $ smfJoin $ smfMap (f' f) $ form s where
  f' :: Semiring r => (x -> LinearCombination r y) -> R x -> SumForm r (R y)
  f' f (R x) = lcsmf () $ LinearCombination $ amap1 (\(r,y) -> (r,R y)) $ lcs $ f x

--------------------------------------------------------------------------------
-- ssJoin -

ssJoin :: (Semiring r, Commutative r, Entity x, Ord x)
  => SumSymbol r (SumSymbol r x) -> SumSymbol r x
ssJoin (SumSymbol s) = SumSymbol $ make $ smfJoin $ smfMap f $ form s where
  f :: R (SumSymbol r x) -> SumForm r (R x)
  f (R (SumSymbol s)) = form s



  
