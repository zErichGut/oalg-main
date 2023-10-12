
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Sequence.Set
-- Description : sets of ordered entities
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- sets of ordered entities.
module OAlg.Entity.Sequence.Set
  ( 
    -- * Set
    Set(..), setSpan, setxs, setSqc, setMap, isSubSet

    -- * X
  , xSet

  ) where

import Control.Monad

import Data.List (head,sort,group,map,filter)

import OAlg.Prelude

--------------------------------------------------------------------------------
-- Set -

-- | set of ordered entities in @__x__@.
--
--  __Property__ Let @s = 'Set' xs@ be in @'Set' __x__@ for a ordered 'Entity' type @__x__@,
--  then holds:
--
--  (1) For all @..x':'y..@ in @xs@ holds: @x '<' y@.
--
--  (2) @'lengthN' s '==' 'lengthN' xs@.
newtype Set x = Set [x] deriving (Show,Eq,LengthN)

relSet :: (Entity x, Ord x) => Set x -> Statement
relSet (Set [])     = SValid
relSet (Set (x:xs)) = valid x && vld (0::N) x xs where
  vld _ _ []     = SValid
  vld i x (y:xs) = And [ valid y
                       , (x<y) :?> Params ["i":=show i,"(x,y)":=show (x,y)]
                       , vld (succ i) y xs
                       ]

instance (Entity x, Ord x) => Validable (Set x) where
  valid xs = Label "Set" :<=>: relSet xs

instance (Entity x, Ord x) => Entity (Set x)

--------------------------------------------------------------------------------
-- setxs -

-- | the elements of a set.
setxs :: Set x -> [x]
setxs (Set xs) = xs

--------------------------------------------------------------------------------
-- setSpan -

-- | the span of a set.
setSpan :: Set x -> Span x
setSpan (Set [])     = (PosInf,NegInf)
setSpan (Set (x:xs)) = (It x,last x xs) where
  last x []     = It x
  last _ (x:xs) = last x xs

--------------------------------------------------------------------------------
-- setMap -

-- | mapping of sets.
--
--  __Note__ This works only for finite sets!
setMap :: Ord y => (x -> y) -> Set x -> Set y
setMap f (Set xs) = Set $ sort $ map f xs

--------------------------------------------------------------------------------
-- setSqc -

-- | mapping a set.
setSqc :: Ord x => (i -> Maybe x) -> Set i -> Set x
setSqc mx (Set is)
  = Set
  $ sort
  $ map fromJust
  $ filter isJust
  $ map mx is

--------------------------------------------------------------------------------
-- xSet -

-- | random variable of sets with maximal the given length.
xSet :: Ord x => N -> X x -> X (Set x)
xSet n xx = do
  xs <- xTakeN n xx
  return $ Set $ map head $ group $ sort xs

--------------------------------------------------------------------------------
-- isSubSet -

-- | checks for being a sub set.
isSubSet :: Ord x => Set x -> Set x -> Bool
isSubSet (Set xs) (Set ys) = sbs xs ys where
  sbs [] _             = True
  sbs _ []             = False
  sbs xs@(x:xs') (y:ys') = case x `compare` y of
    LT -> False
    EQ -> sbs xs' ys'
    GT -> sbs xs ys'

--------------------------------------------------------------------------------
-- Set - POrd -

instance Ord x => POrd (Set x) where
  (<<=) = isSubSet  
