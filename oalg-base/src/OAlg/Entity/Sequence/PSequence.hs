
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable, GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Sequence.PSequence
-- Description : partially defined sequences
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- partially defined sequences of items in @__x__@ with a totally ordered index type @__i__@.
module OAlg.Entity.Sequence.PSequence
  ( -- * Sequence
    PSequence(..), iProxy
  , psqSpan
  , psqEmpty, psqIsEmpty, psqxs, psequence
  , psqHead, psqTail
  , psqMap, psqMapShift
  , psqFilter
  , psqSplitWhile
  , psqInterlace
  , psqCompose
  , psqAppend
  , psqShear
  , psqSwap

    -- * X
  , xPSequence
  ) where

import Control.Monad 

import Data.Foldable
import Data.Typeable

import Data.List (map,sortBy,groupBy,filter,head,tail,(++),zip)

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Structure.Additive
import OAlg.Structure.Number

import OAlg.Entity.Sequence.Definition
import OAlg.Entity.Sequence.Set

--------------------------------------------------------------------------------
-- PSequence -

-- | partially defined sequences @(x0,i0),(x1,i1)..@ of index items in @__x__@ with a
-- totally ordered index type @__i__@.
--
-- __Property__ Let @'PSequence' xis@ be in @'PSequence' __i__ __x__@ then holds:
-- @i '<' j@ for all @..(_,i)':'(_,j)..@ in @xis@.
--
--  __Examples__
--
-- >>> PSequence [('a',3),('b',7),('c',12)] :: PSequence N Char
-- PSequence [('a',3),('b',7),('c',12)]
--
-- and
--
-- >>> validate (valid (PSequence [('a',3),('b',7),('c',12)] :: PSequence N Char))
-- Valid
--
-- but
--
-- >>> validate (valid (PSequence [('a',3),('b',15),('c',12)] :: PSequence N Char))
-- Invalid
--
-- as 'Char' is a totally ordered type it can serve as index type
--
-- >>> validate (valid (PSequence [(12,'c'),(3,'e'),(8,'x')] :: PSequence Char Z))
-- Valid
--
-- and they admit a total right operation 'OAlg.Structure.Operational.<*' of
-- @t'OAlg.Entity.Sequence.Permutation.Permutation' __i__@
--
-- >>> (PSequence [(12,'c'),(3,'e'),(8,'x')] :: PSequence Char Z) <* pmtSwap 'e' 'x'
-- PSequence [(12,'c'),(8,'e'),(3,'x')]
--
--
--  __Note__ As we keep the constructor public, it is crucial for there further use to
--  ensure that they are 'valid'!
newtype PSequence i x = PSequence [(x,i)] deriving (Show,Eq,Ord,LengthN,Foldable)

instance Embeddable [x] (PSequence N x) where
  inj xs = PSequence (xs `zip` [0..])

instance Projectible [x] (PSequence N x) where
  prj (PSequence xis) = map fst xis
  
--------------------------------------------------------------------------------
-- psqxs -

-- | the underlying list of indexed values.
psqxs :: PSequence i x -> [(x,i)]
psqxs (PSequence xs) = xs

--------------------------------------------------------------------------------
-- psqSqc -

-- | @'psqSqc' f is@ maps the index set @is@ according to @f@ and strips out all 'Nothing'
--   items.
psqSqc :: (i -> Maybe x) -> Set i -> PSequence i x
psqSqc mx (Set is)
  = PSequence
  $ map (\(mx,i) -> (fromJust mx,i))
  $ filter (isJust . fst)
  $ map (\i -> (mx i,i)) is

--------------------------------------------------------------------------------
-- PSequence - Sequence -

instance Ord i => Sequence (PSequence i) i x where
  list _ = psqxs

instance (Entity x, Entity i, Ord i) => ConstructableSequence (PSequence i) i x where
  sequence = psqSqc
  
--------------------------------------------------------------------------------
-- psqFromMap -

-- | constructs a partially defined sequence according to the given map and the bounds.
psqFromMap :: (Enum i, Ord i) => i -> Closure i -> (i -> Maybe x) -> PSequence i x
psqFromMap i0 h f
  = PSequence
  $ map (\(mx,i) -> (fromJust mx,i)) 
  $ filter (isJust . fst)
  $ map (\i -> (f i,i))
  $ enumSpan i0 h


--------------------------------------------------------------------------------
-- iProxy -

-- | proxy of the second type valiable @__i__@.
iProxy :: s i x -> Proxy i
iProxy _ = Proxy
  
--------------------------------------------------------------------------------
-- psqSpan -

-- | the span.
psqSpan :: Ord i => PSequence i x -> Span i
psqSpan (PSequence xs) = cspan $ map snd xs

--------------------------------------------------------------------------------
-- psqEmpty -

-- | the empty partially defined sequence.
psqEmpty :: PSequence i x
psqEmpty = PSequence []

--------------------------------------------------------------------------------
-- psqIsEmpty -

-- | checks of being empty.
psqIsEmpty :: PSequence i x -> Bool
psqIsEmpty (PSequence []) = True
psqIsEmpty _              = False

--------------------------------------------------------------------------------
-- psqMap -

-- | maps the entries, where the indices are preserved.
psqMap :: (x -> y) -> PSequence i x -> PSequence i y
psqMap f (PSequence xis) = PSequence $ map (\(x,i) -> (f x,i)) xis

instance Functor (PSequence i) where fmap = psqMap
  
--------------------------------------------------------------------------------
-- psqMapShift -

-- | maps and shifts a partial sequence.
psqMapShift :: Number i => i -> ((x,i) -> y) -> PSequence i x -> PSequence i y
psqMapShift o f (PSequence xs) = PSequence $ map f' xs where f' xi = (f xi,snd xi + o)

--------------------------------------------------------------------------------
-- PSequence - Entity -

relPSequence :: (Entity x, Entity i, Ord i) => PSequence i x -> Statement
relPSequence (PSequence [])       = SValid
relPSequence (PSequence (xi:xis)) = vld (0::N) xi xis where
    vld _ xi [] = valid xi
    vld l xi@(_,i) (xj@(_,j):xis) = And [ (i<j):?>Params ["l":=show l,"(i,j)":=show (i,j)]
                                        , valid xi
                                        , vld (succ l) xj xis
                                        ]

instance (Entity x, Entity i, Ord i) => Validable (PSequence i x) where
  valid xs = Label "PSequence" :<=>: valid (graph (iProxy xs) xs)

instance (Entity x, Entity i, Ord i) => Entity (PSequence i x)

--------------------------------------------------------------------------------
-- psequence -

-- | the partial sequenc given by a aggregation function an a list of value index pairs,
--   which will be sorted and accordingly aggregated by thegiven aggregation function.
psequence :: Ord i => (x -> x -> x) -> [(x,i)] -> PSequence i x
psequence (+) xis = PSequence
             $ map (aggrBy (+))
             $ groupBy (eql (fcompare snd))
             $ sortBy (fcompare snd)
             $ xis where

  aggrBy :: (x -> x -> x) -> [(x,i)] -> (x,i)
  aggrBy (+) ((x,i):xis) = (foldl (+) x (map fst xis),i)

--------------------------------------------------------------------------------
-- psqHead -

-- | the head of a partial sequence.
psqHead :: PSequence i x -> (x,i)
psqHead (PSequence xs) = head xs

--------------------------------------------------------------------------------
-- psqTail -

-- | the tail.
psqTail :: PSequence i x -> PSequence i x
psqTail (PSequence xs) = PSequence (tail xs)

--------------------------------------------------------------------------------
-- psqFilter -

-- | filters the partially defiend sequence accordingly the given predicate.
psqFilter :: (x -> Bool) -> PSequence i x -> PSequence i x
psqFilter p (PSequence xis) = PSequence $ filter p' xis where
  p' (x,_) = p x

--------------------------------------------------------------------------------
-- psqInterlace -

-- | interlaces the tow partially defined sequences according to the given mappings.
psqInterlace :: Ord i
  => (x -> y -> z) -> (x -> z) -> (y -> z)
  -> PSequence i x -> PSequence i y -> PSequence i z
psqInterlace (+) xz yz (PSequence xis) (PSequence yjs) = PSequence (zks xis yjs) where
  zks [] yjs                  = map (\(y,j) -> (yz y,j)) yjs
  zks xis []                  = map (\(x,i) -> (xz x,i)) xis
  zks ((x,i):xis) ((y,j):yjs) = case i `compare` j of
    LT -> (xz x,i) : zks xis ((y,j):yjs)
    EQ -> (x + y,i) : zks xis yjs
    GT -> (yz y,j) : zks ((x,i):xis) yjs

--------------------------------------------------------------------------------
-- psqCompose -

-- | composition of the two partially defined sequences.
--
-- __Property__ Let @f@ be in @'PSequence' __i__ __x__@ and @g@ be in @'PSequence' __j__ __i__@ then
-- @f '`psqCompose`' g@ is given by @'join' '.' 'fmap' (('??') f) '.' ('??') g@.
psqCompose :: (Ord i, Ord j) => PSequence i x -> PSequence j i -> PSequence j x
psqCompose (PSequence xis) (PSequence ijs)
  = psqMap fromJust $ PSequence $ sortSnd $ cmp xis (sortFst ijs) where
  
  cmp [] _  = []
  cmp _ []  = []
  cmp xis@((x,i):xis') ijs@((i',j):ijs') = case i `compare` i' of
    LT -> cmp xis' ijs
    EQ -> (Just x,j):cmp xis' ijs'
    GT -> cmp xis ijs'

-- cmp :: (i -> Maybe x)  (j -> Maybe i) -> i -> Maybe x

--------------------------------------------------------------------------------
-- psqSplitWhile -

-- | splits the sequence as long as the given predicate holds.
psqSplitWhile :: ((x,i) -> Bool) -> PSequence i x -> (PSequence i x,PSequence i x)
psqSplitWhile p (PSequence xs) = (PSequence l,PSequence r) where
  (l,r) = spw p xs

  spw _ []     = ([],[])
  spw p (x:xs) = if p x then (x:l,r) else ([],x:xs) where (l,r) = spw p xs

--------------------------------------------------------------------------------
-- psqAppend -

-- | appends the second partially defined sequence to the first.
--
--  __Property__ Let @zs = 'psqAppend' xs ys@ where @..(x,l) = xs@ and
-- @(y,f).. = ys@ then holds:
--
-- [If] @l '<' f@
--
-- [Then] @zs@ is 'valid'.
psqAppend ::PSequence i x -> PSequence i x -> PSequence i x
psqAppend (PSequence xs) (PSequence ys) = PSequence (xs ++ ys)

--------------------------------------------------------------------------------
-- //: -

-- | cone.
(//:) :: (Maybe a,i) -> [(a,i)] -> [(a,i)]
(Just a,i) //: ais  = (a,i):ais
(Nothing,_) //: ais = ais

--------------------------------------------------------------------------------
-- psqShear -


-- | shears the two entries at the given position and leafs the others untouched.
--
-- __Property__ Let @x' = psqShear (sk,k) (sl,l) x@, then holds
--
-- [If] @k '<' l@
--
-- [Then]
--
-- (1) @x' k '==' sk (x k) (x l)@ and @x' l '==' sl (x k) (x l)@.
--
-- (2) @x' i '==' x i@ for all @i '/=' k, l@. 
psqShear :: Ord i
         => (Maybe a -> Maybe a -> Maybe a,i) -> (Maybe a -> Maybe a -> Maybe a,i)
         -> PSequence i a -> PSequence i a
psqShear (sk,k) (sl,l) (PSequence xis) = PSequence (shr xis) where
  shr []          = []
  shr ((x,i):xis) = case i `compare` k of
    LT -> (x,i) : shr xis
    EQ -> (sk xk xl,k) //: xis' where
      xk = Just x
      (xl,xis') = shr' xk xis
    GT -> (sk xk xl,k) //: xis' where
      xk        = Nothing
      (xl,xis') = shr' xk ((x,i):xis)

  shr' xk []             = shr'' xk Nothing []
  shr' xk (xi@(x,i):xis) = case i `compare` l of
    LT -> (sl,xi:xis') where (sl,xis') = shr' xk xis
    EQ -> shr'' xk (Just x) xis
    GT -> shr'' xk Nothing (xi:xis)

  shr'' xk xl xis = (xl,(sl xk xl,l) //: xis)

--------------------------------------------------------------------------------
-- psqSwap -

-- | swaps the the @k@-th and the @l@-th entry.
--
-- __Property__ Let @x' = psqSwap k l x@, then holds:
--
-- [If] @k < l@
--
-- [Then]
--
-- (1) @x' k '==' x l@ and @x' l '==' x k@.
-- 
-- (2) @x' i '==' x i@ for all @i '/=' k, l@.
psqSwap :: Ord i => i -> i -> PSequence i a -> PSequence i a
psqSwap k l = psqShear (sk,k) (sl,l) where
  sk _ x = x
  sl x _ = x

--------------------------------------------------------------------------------
-- xPSequence -

-- | @'xPSequence' n m@ random variable of partially defined sequences with maximal length
--   @'min' n m@.
xPSequence :: Ord i => N -> N -> X x -> X i -> X (PSequence i x)
xPSequence n m xx xi = do
  xs <- xTakeN n xx
  is <- xSet m xi
  return $ PSequence $ (xs `zip` setxs is)

