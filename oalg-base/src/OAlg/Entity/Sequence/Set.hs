
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
    Set(..), set, setSpan, setxs, setSqc, setMap, isSubSet

    -- * Operations
  , setEmpty, setUnion

    -- * Lookup
  , setIndex 

    -- * X
  , xSet

    -- * Propositions
  , prpSetUnion

  ) where

import Control.Monad

import Data.Foldable
import Data.List (head,sort,group,map,filter,zip)

import OAlg.Prelude

import OAlg.Data.Tree

import OAlg.Structure.Number

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
--
--  __Note__ The canonical ordering 'Ord' and the subset ordering 'POrd' are not equivalent.
newtype Set x = Set [x] deriving (Show,Eq,Ord,LengthN,Foldable)

relSet :: (Validable x, Ord x, Show x) => Set x -> Statement
relSet (Set [])     = SValid
relSet (Set (x:xs)) = valid x && vld (0::N) x xs where
  vld _ _ []     = SValid
  vld i x (y:xs) = And [ valid y
                       , (x<y) :?> Params ["i":=show i,"(x,y)":=show (x,y)]
                       , vld (succ i) y xs
                       ]

instance (Validable x, Ord x, Show x) => Validable (Set x) where
  valid xs = Label "Set" :<=>: relSet xs

instance (Entity x, Ord x) => Entity (Set x)

--------------------------------------------------------------------------------
-- set -

-- | makes a set from the given list.
set :: Ord x => [x] -> Set x
set = Set . amap1 head . group . sort

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
-- setEmpty -

-- | the empty set.
setEmpty :: Set x
setEmpty = Set []

--------------------------------------------------------------------------------
-- setUnion -

-- | the union of two sets.
setUnion :: Ord x => Set x -> Set x -> Set x
setUnion (Set xs) (Set ys) = Set $ un xs ys where
  un [] ys = ys
  un xs [] = xs
  un xs@(x:xs') ys@(y:ys') = case x `compare` y of
    LT -> x:un xs' ys
    EQ -> x:un xs' ys'
    GT -> y:un xs  ys'

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
-- setIndex -

-- | the index of an element, where the elements of the given set are indexed from @0@.
--
--  __Examples__
--
-- >>> setIndex (Set ['a'..'x']) 'c'
-- Just 2
setIndex :: Ord x => Set x -> x -> Maybe N
setIndex (Set []) = const Nothing
-- setIndex (Set xs) = \x -> let (x',i) = trLookup xs' x in if x' == x then Just i else Nothing
setIndex (Set xs) = lp (lt (xs `zip` [0..]))
  where
    -- xs' = lt (xs `zip` [0..])
    lt :: Ord x => [(x,N)] -> Tree x (x,N)
    lt [xi] = Leaf xi
    lt xis  = Node (fst $ head xisR) (lt xisL) (lt xisR) where
      (xisL,xisR) = splitAtN (lengthN xis `div` 2) xis

lp :: Ord x => Tree x (x,y) -> x -> Maybe y
lp t x = let (x',y) = trLookup t x in if x' == x then Just y else Nothing
--------------------------------------------------------------------------------
-- Set - POrd -

instance Ord x => POrd (Set x) where
  (<<=) = isSubSet  

--------------------------------------------------------------------------------
-- xSet -

-- | random variable of sets with a maximal length of the given length.
xSet :: Ord x => N -> X x -> X (Set x)
xSet n xx = do
  xs <- xTakeN n xx
  return $ Set $ map head $ group $ sort xs


--------------------------------------------------------------------------------
-- prpSetUnion -

-- | validity for the union operator of sets.
prpSetUnion :: (Ord x, Show x) => X (Set x) -> Statement
prpSetUnion x = Prp "SetUnion" :<=>:
  Forall xy (\(x,y)
             -> let xy = x `setUnion` y in
                  And [ Label "x"
                        :<=>: (x `isSubSet` xy) :?> Params ["x":=show x, "xy":=show xy]
                      , Label "y"
                        :<=>: (y `isSubSet` xy) :?> Params ["y":=show y, "xy":=show xy]
                      ]
            ) 
  where xy = xTupple2 x x
