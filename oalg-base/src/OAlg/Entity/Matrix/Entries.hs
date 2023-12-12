
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


-- |
-- Module      : OAlg.Entity.Matrix.Entries
-- Description : entries of matrices
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- entries of matrices and viewing them as a column of rows respectively as a row
-- of columns. 
module OAlg.Entity.Matrix.Entries
  (
    -- * Entries
    Entries(..), etsxs, etsEmpty, etsAdd, etsMlt, etsJoin
  , etscr, etsrc, crets, rcets
  , etsElimZeros

    -- * Row
  , Row(..), rowxs, rowEmpty, rowIsEmpty, rowHead, rowTail
  , rowFilter, rowMapShift, rowAppend, rowInterlace
  , rowElimZeros, rowSwap, rowAdd, rowMltl, rowShear, rowScale
  
    -- * Col
  , Col(..), colxs, colEmpty, colIsEmpty, colHead, colTail
  , colFilter, colMapShift, colAppend, colInterlace
  , colElimZeros, colSwap, colAdd, colMltr, colShear, colScale

    -- * Col Row
  , crHeadColAt, crHeadRowAt

    -- * Duality
  , coEntries, coEntriesInv
 
  ) where

import Control.Monad

import Data.Foldable
import Data.List (map,sortBy,filter,(++))

import OAlg.Prelude

import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Number
import OAlg.Structure.Operational

import OAlg.Entity.Sequence


--------------------------------------------------------------------------------
-- Row -

-- | viewing a partial sequence as a row.
newtype Row j x = Row (PSequence j x) deriving (Eq,Validable,Entity,Functor,LengthN)

instance (Show x,Show j) => Show (Row j x) where
  show (Row (PSequence xs)) = "Row " ++ show xs

instance Ord j => Sequence (Row j) j x where
  list _ = rowxs
  Row xs ?? j = xs ?? j

instance Ord j => Opr (Permutation j) (Row j x) where Row xs <* p = Row (xs <* p)

instance (Entity x, Entity j, Ord j) => TotalOpr (Permutation j) (Row j x)

instance (Entity x, Entity j, Ord j) => PermutableSequence (Row j) j x where
  permuteBy f c w (Row xs) = (Row xs',p) where (xs',p) = permuteBy f c w xs

--------------------------------------------------------------------------------
-- rowxs -

-- | underlying list of indexed entries.
rowxs :: Row j x -> [(x,j)]
rowxs (Row xs) = psqxs xs

--------------------------------------------------------------------------------
-- rowEmpty -

-- | the empty row.
rowEmpty :: Row j x
rowEmpty = Row psqEmpty

--------------------------------------------------------------------------------
-- rowIsEmpty -

-- | check for being empty.
rowIsEmpty :: Row j x -> Bool
rowIsEmpty (Row rw) = psqIsEmpty rw

--------------------------------------------------------------------------------
-- rowHead -

-- | head.
rowHead :: Row j x -> (x,j)
rowHead (Row xs) = psqHead xs

--------------------------------------------------------------------------------
-- rowTail -

-- | tail.
rowTail :: Row j x -> Row j x
rowTail (Row xs) = Row (psqTail xs)

--------------------------------------------------------------------------------
-- rowFilter -

-- | filtering a row by the given predicate.
rowFilter :: (x -> Bool) -> Row j x -> Row j x
rowFilter p (Row xs) = Row $ psqFilter p xs

--------------------------------------------------------------------------------
-- rowMapShift -

-- | mapping and shifting of a row.
rowMapShift :: Number j => j -> ((x,j) -> y) -> Row j x -> Row j y
rowMapShift o f (Row xs) = Row $ psqMapShift o f xs

--------------------------------------------------------------------------------
-- rowAppend -

-- | appending a row.
--
--  __Property__ Let @zs = 'rowAppend' xs ys@ where @..(x,l) = xs@ and
-- @(y,f).. = ys@ then holds:
--
-- [If] @l '<' f@
--
-- [Then] @zs@ is 'valid'.
rowAppend :: Row j x -> Row j x -> Row j x
rowAppend (Row xs) (Row ys) = Row $ psqAppend xs ys

--------------------------------------------------------------------------------
-- rowInterlace -

-- | interlacing two rows.
rowInterlace :: Ord j
  => (x -> y -> z) -> (x -> z) -> (y -> z) -> Row j x -> Row j y -> Row j z
rowInterlace (+) xz yz (Row xs) (Row ys) = Row $ psqInterlace (+) xz yz xs ys

--------------------------------------------------------------------------------
-- rowElimZeros -

-- | elimination of 'zero's.
rowElimZeros :: Additive a => Row i a -> Row i a
rowElimZeros (Row rw) = Row $ psqFilter (not.isZero) rw

--------------------------------------------------------------------------------
-- rowAdd - 

-- | adding two rows.
rowAdd :: (Additive a, Ord j) => Row j a -> Row j a -> Row j a
rowAdd (Row a) (Row b) = rowElimZeros $ Row $ psqInterlace (+) id id a b

--------------------------------------------------------------------------------
-- rowSwap -

-- | swapping two entries of a row.
--
-- __Pre__ @k < l@.
rowSwap :: Ord j => j -> j -> Row j x -> Row j x
rowSwap k l (Row rw) = Row $ psqSwap k l rw

--------------------------------------------------------------------------------
-- rowMltl -

-- | multiplies each element of the row by the given factor from the left.
rowMltl :: Distributive a => a -> Row j a -> Row j a
rowMltl a = rowElimZeros . fmap (a*)

--------------------------------------------------------------------------------
-- rowShear -

-- | shears two entries of a row.
--
--  __Property__ Let @r' = 'rowShear' (<*) (+) k l s t u v r@, then holds:
--
--  [Pre] @k '<' l@.
--
--  __Note__ 'rowShear' is like /multiplying/ the given row from the right with
--  the matrix given by @k l s t u v@.
rowShear :: Ord j
  => (Maybe x -> s -> Maybe x) -> (Maybe x -> Maybe x -> Maybe x)
  -> j -> j -> s -> s -> s -> s
  -> Row j x -> Row j x
rowShear (<*) (+) k l s t u v (Row xs) = Row (psqShear (sk,k) (sl,l) xs) where
  sk xk xl = (xk<*s) + (xl<*u)
  sl xk xl = (xk<*t) + (xl<*v)

--------------------------------------------------------------------------------
-- rowScale -

-- | scales the entry at the given position by the given factor.
rowScale :: Ord j
  => (x -> s -> Maybe x)
  -> j -> s
  -> Row j x -> Row j x
rowScale (<*) j s rw
  = fmap fromJust
  $ rowFilter isJust
  $ rowInterlace (<*) Just (const Nothing) rw (Row (PSequence [(s,j)]))


--------------------------------------------------------------------------------
-- Col - 

-- | viewing a partial sequence as a column.
newtype Col i x = Col (PSequence i x) deriving (Eq,Validable,Entity,Functor,LengthN)

instance (Show x,Show i) => Show (Col i x) where
  show (Col (PSequence xs)) = "Col " ++ show xs

instance Ord i => Sequence (Col i) i x where
  list _ = colxs
  Col xs ?? i = xs ?? i

instance Ord i => Opr (Permutation i) (Col i x) where Col xs <* p = Col (xs <* p)

instance (Entity x, Entity i, Ord i) => TotalOpr (Permutation i) (Col i x)

instance (Entity x, Entity i, Ord i) => PermutableSequence (Col i) i x where
  permuteBy f c w (Col xs) = (Col xs',p) where (xs',p) = permuteBy f c w xs

--------------------------------------------------------------------------------
-- colxs -

-- | underlying list of indexed entries.
colxs :: Col i x -> [(x,i)]
colxs (Col xs) = psqxs xs

--------------------------------------------------------------------------------
-- colEmpty -

-- | the empty column.
colEmpty :: Col i x
colEmpty = Col psqEmpty

--------------------------------------------------------------------------------
-- colIsEmpty -

-- | check for being empty.
colIsEmpty :: Col i x -> Bool
colIsEmpty (Col cl) = psqIsEmpty cl

--------------------------------------------------------------------------------
-- colHead -

-- | head.
colHead :: Col i x -> (x,i)
colHead (Col xs) = psqHead xs

--------------------------------------------------------------------------------
-- colTail -

-- | tail.
colTail :: Col i x -> Col i x
colTail (Col xs) = Col (psqTail xs)

--------------------------------------------------------------------------------
-- colFilter -

-- | filtering a column by the given predicate.
colFilter :: (x -> Bool) -> Col i x -> Col i x
colFilter p (Col xs) = Col $ psqFilter p xs

--------------------------------------------------------------------------------
-- colMapShift -

-- | mapping and shifting of a column.
colMapShift :: Number i => i -> ((x,i) -> y) -> Col i x -> Col i y
colMapShift o f (Col xs) = Col $ psqMapShift o f xs

--------------------------------------------------------------------------------
-- colAppend -

-- | appending a column..
--
--  __Property__ Let @zs = 'colAppend' xs ys@ where @..(x,l) = xs@ and
-- @(y,f).. = ys@ then holds:
--
-- [If] @l '<' f@
--
-- [Then] @zs@ is 'valid'.
colAppend :: Col i x -> Col i x -> Col i x
colAppend (Col xs) (Col ys) = Col (psqAppend xs ys)

--------------------------------------------------------------------------------
-- colInterlace -

-- | interlacing two columns.
colInterlace :: Ord i
  => (x -> y -> z) -> (x -> z) -> (y -> z) -> Col i x -> Col i y -> Col i z
colInterlace (+) xz yz (Col xs) (Col ys) = Col $ psqInterlace (+) xz yz xs ys

--------------------------------------------------------------------------------
-- colElimZeros -

-- | elimination of 'zero's.
colElimZeros :: Additive a => Col i a -> Col i a
colElimZeros (Col rw) = Col $ psqFilter (not.isZero) rw

--------------------------------------------------------------------------------
-- colSwap -

-- | swapping two entries of a column.
--
-- __Pre__ @k < l@.
colSwap :: Ord i => i -> i -> Col i x -> Col i x
colSwap k l (Col rws) = Col (psqSwap k l rws)

--------------------------------------------------------------------------------
-- colAdd -

-- | adding two columns.
colAdd :: (Additive a, Ord i) => Col i a -> Col i a -> Col i a
colAdd (Col a) (Col b) = colElimZeros $ Col $ psqInterlace (+) id id a b

--------------------------------------------------------------------------------
-- colShear -

-- | shears two entries of a column.
--
--  __Property__ Let @c' = 'colShear' (<*) (+) k l s t u v c@, then holds:
--
--  [Pre] @k '<' l@.
--
--  __Note__ 'colShear' is like /multiplying/ the given column from the left with
--  the matrix given by @k l s t u v@.
colShear :: Ord i
  => (s -> Maybe x -> Maybe x) -> (Maybe x -> Maybe x -> Maybe x)
  -> i -> i -> s -> s -> s -> s
  -> Col i x -> Col i x
colShear (*>) (+) k l s t u v (Col xs) = Col (psqShear (sk,k) (sl,l) xs) where
  sk xk xl = (s*>xk) + (t*>xl)
  sl xk xl = (u*>xk) + (v*>xl)

--------------------------------------------------------------------------------
-- colScale -

-- | scales the entry at the given position by the given factor.
colScale :: Ord i
  => (s -> x -> Maybe x)
  -> i -> s
  -> Col i x -> Col i x
colScale (*>) i s cl
  = fmap fromJust
  $ colFilter isJust
  $ colInterlace (*>) (const Nothing) Just (Col (PSequence [(s,i)])) cl
  
--------------------------------------------------------------------------------
-- colMltr -

-- | multiplies each element of the column by the given factor from the right.
colMltr :: Distributive a => Col i a -> a -> Col i a
colMltr cl a = colElimZeros $ fmap (*a) cl

--------------------------------------------------------------------------------
-- Col - Duality -

-- | to the dual of a column, with inverse 'coColInv'.
coCol :: Col i x -> Row i (Op x)
coCol (Col cl) = Row $ fmap Op cl

-- | from the dual of a column, with inverse 'coCol'.
coColInv :: Row i (Op x) -> Col i x
coColInv (Row rw) = Col $ fmap fromOp rw

--------------------------------------------------------------------------------
-- Row - Col - Duality -

type instance Dual (Row j (Col i x)) = Col j (Row i (Op x))

-- | to the dual of a row of columns, with inverse 'coRowColInv'.
coRowCol :: Row j (Col i x) -> Dual (Row j (Col i x))
coRowCol (Row cls) = Col $ fmap coCol cls

-- | from the dual of a row of columns, with inverse 'coRowCol'.
coRowColInv :: Dual (Row j (Col i x)) -> Row j (Col i x)
            -- Col j (Row i (Op x))   -> Row j (Col i x)
coRowColInv (Col rws) = Row $ fmap coColInv rws

{-
coColRow :: Col i (Row j a) -> Row j (Col i (Op a))
coColRow = error "nyi"

coColRowInv :: Row j (Col i (Op a)) -> Col i (Row j a)
coColRowInv = error "nyi"
-}

--------------------------------------------------------------------------------
-- Entries -

-- | two dimensional partial sequence.
newtype Entries i j x = Entries (PSequence (i,j) x)
  deriving (Eq,Ord,Validable,Entity,Functor,LengthN)

instance (Show x, Show i, Show j) => Show (Entries i j x) where
  show ets = "Entries" ++ (show $ etsxs ets)  

--------------------------------------------------------------------------------
-- etsxs -

-- | underlying list of indexed entries.
etsxs :: Entries i j x -> [(x,i,j)]
etsxs (Entries xs) = map (\(x,(i,j)) -> (x,i,j)) $ psqxs xs
                         
--------------------------------------------------------------------------------
-- etsEmpty -

-- | the empty sequence of entries.
etsEmpty :: Entries i j x
etsEmpty = Entries psqEmpty

--------------------------------------------------------------------------------
-- etsElimZeros -

-- | elimination of 'zero's.
etsElimZeros :: Additive x => Entries i j x -> Entries i j x
etsElimZeros (Entries xs) = Entries (psqFilter (not . isZero) xs)

--------------------------------------------------------------------------------
-- etsAdd -

-- | adding two entries.
--
--   __Property__ Let @zs = 'etsAdd' xs ys@, then holds:
--
--   [Pre] For all @(i,j)@ in @(__i__,__j__)@ where there exists an @(x,i,j)@ in @xs@ and
--   a @(y,i,j)@ in @ys@ holds:
--   @'OAlg.Structure.Fibred.Definition.root' x '==' 'OAlg.Structure.Fibred.Definition.root' y@.
--
--   [Post]
--
--      (1) @zs@ is 'valid'.
--
--      (2) For all @(i,j)@ in @(__i__,__j__)@ holds:
--
--          (1) If exists a @(x,i,j)@ in @xs@ but not exists a @(y,i,j)@ in @ys@ then
--          there exists a @(z,i,j)@ in @zs@ with @z '==' x@.
--
--          (2) If exists a @(y,i,j)@ in @ys@ but not exists a @(x,i,j)@ in @xs@ then
--          there exists a @(z,i,j)@ in @zs@ with @z '==' y@.
--
--          (3) If exists a @(x,i,j)@ in @xs@ and @(y,i,j)@ in @ys@ then there
--          exists a @(z,i,j)@ in @zs@ with @z '==' x '+' y@.
etsAdd :: (Additive x, Ord i, Ord j) => Entries i j x -> Entries i j x -> Entries i j x
etsAdd (Entries xs) (Entries ys)
  = Entries $ psqFilter (not . isZero) $ psqInterlace (+) id id xs ys

--------------------------------------------------------------------------------
-- Transposable -

instance (Transposable x, Ord n) => Transposable (Entries n n x) where
  transpose (Entries xs) = Entries
                         $ PSequence
                         $ sortBy (fcompare snd)
                         $ map (\(x,(i,j)) -> (transpose x,(j,i)))
                         $ psqxs $ xs
                         
--------------------------------------------------------------------------------
-- Entrie - Duality -

type instance Dual (Entries i j x) = Entries j i (Op x)

-- | to the dual of 'Entries', with inverse 'coEntriesInv'.
coEntries :: (Ord i, Ord j) => Entries i j x -> Dual (Entries i j x)
coEntries (Entries xs) = Entries
                       $ PSequence
                       $ sortBy (fcompare snd)
                       $ map (\(x,(i,j)) -> (Op x,(j,i)))
                       $ psqxs $ xs


-- | from the dual of 'Entries', with inverse 'coEntries'.
coEntriesInv :: (Ord i, Ord j) => Dual (Entries i j x) -> Entries i j x
coEntriesInv (Entries xs') = Entries
                           $ PSequence
                           $ sortBy (fcompare snd)
                           $ map (\(Op x,(j,i)) -> (x,(i,j)))
                           $ (\(PSequence xs) -> xs) $ xs'

--------------------------------------------------------------------------------
-- etscr -

-- | the underlying column of rows.
etscr :: Eq i => Entries i j x -> Col i (Row j x)
etscr (Entries xs) = Col $ PSequence $ cr xs where
  cr (PSequence []) = []
  cr xs             = (l,i) : cr r where
    (PSequence ls,r) = psqSplitWhile ((==i) . ix) xs
    ix (_,(i,_)) = i
    i = ix $ psqHead xs
    l = Row $ PSequence $ map (\(x,(_,j)) -> (x,j)) $ ls 

--------------------------------------------------------------------------------
-- etsrc -

-- | the underlying row of columns.
etsrc :: (Ord i, Ord j) => Entries i j x -> Row j (Col i x)
etsrc = coRowColInv . etscr . coEntries

--------------------------------------------------------------------------------
-- etsMlt -

-- | multiplication.
etsMlt :: (Distributive x, Ord k) => Col i (Row k x) -> Row j (Col k x) -> Col i (Row j x)
etsMlt (Col rws) (Row cls) = Col rws' where
  rws' = fmap (<*cls) rws
  
  rw <* cls
    = Row
    $ fmap fromJust
    $ psqFilter isJust
    $ fmap (rw<*>) cls
    
  Row rw <*> Col cl
    = foldl add Nothing
    $ psqInterlace mlt (const Nothing) (const Nothing) rw cl

  mlt x y = if isZero xy then Nothing else (Just xy) where xy = x*y
  
  add Nothing y         = y
  add x Nothing         = x
  add (Just x) (Just y) = if isZero xy then Nothing else (Just xy) where xy = x+y
  
--------------------------------------------------------------------------------
-- crets -

-- | the entries given by a column of rows.
crets :: Col i (Row j x) -> Entries i j x
crets (Col rws) = Entries $ PSequence ets where
  ets = join $ map (\(rw,i) -> (xijs i rw)) $ psqxs rws
  xijs i (Row xj) = map (\(x,j) -> (x,(i,j))) $ psqxs xj

--------------------------------------------------------------------------------
-- rcets -

-- | the entries given by a row of columns.
rcets :: (Ord i, Ord j) => Row j (Col i x) -> Entries i j x
rcets = Entries . psequence (curry fst) . ets . rowxs where
  ets :: [(Col i x,j)] -> [(x,(i,j))]
  ets = join . map (\(cl,j) -> map (\(x,i) -> (x,(i,j))) $ colxs cl)

--------------------------------------------------------------------------------
-- etsJoin -

-- | joining entries of entries.
--
--  __Property__ Let @xs' = 'etsJoin' r c xs@
--
--  [Pre] For all @(xij,i,j)@ in @xs@ holds:
--
--        (1) @i '<' 'lengthN' r@ and @j '<' 'lengthN' c@
--
--        (2) For all @(_,i',j')@ in @xij@ holds: @i' '<' ri@ and @j' '<' cj@ where
--        @..ri.. = r@, @..cj.. = c@.
--
--  [Post] @xs'@ is 'valid'.
etsJoin :: (i ~ N, j ~ N)
  => ProductSymbol i -> ProductSymbol j -> Entries i j (Entries i j x) -> Entries i j x
etsJoin r c es = crets es' where
  es' = join (accum 0 (psyxs r))
             (accum 0 (psyxs c))
             (colxs $ etscr es)

  accum _ []          = []
  accum o ((d,i):dis) = (o,i):accum (o+d) dis

  join :: (i ~ N, j ~ N, o ~ N)
    => [(o,i)] -> [(o,j)]
    -> [(Row j (Entries i j x),i)] -> Col i (Row j x)
  join _ _ []                                  = colEmpty
  join ((_,i):ois) ojs rws@((_,i'):_) | i < i' = join ois ojs rws
  join ((o,_):ois) ojs ((rw,_):rws)            =  joinRow o ojs rw
                                               `colAppend` join ois ojs rws

  joinRow :: (i ~ N, j ~ N, o ~ N)
    => o -> [(o,j)] -> Row j (Entries i j x) -> Col i (Row j x)
  joinRow oi ojs rw = foldl (||) colEmpty $ rwShift oi ojs rw

  rwShift :: (i ~ N, j ~ N, o ~ N)
    => o -> [(o,j)] -> Row j (Entries i j x) -> [Col i (Row j x)]
  rwShift oi ojs rw = shRow ojs (rowxs rw) where
    shRow _ []                               = []
    shRow ((_,j):ojs) rw@((_,j'):_) | j < j' = shRow ojs rw
    shRow ((oj,_):ojs) ((xs,_):rw)           = shColRow oi oj (etscr xs) : shRow ojs rw

    shColRow oi oj = colMapShift oi (rowMapShift oj fst . fst)

  (||) :: Ord i => Col i (Row j x) -> Col i (Row j x) -> Col i (Row j x)
  (||) = colInterlace rowAppend id id

--------------------------------------------------------------------------------
-- crHeadColAt -

-- | get the head column at @j@.
--
--   __Pre__ for all @j'@ in @rws@ holds: @j '<=' j'@.
crHeadColAt :: Eq j => j -> Col i (Row j a) -> Col i a
crHeadColAt j rws
  = Col $ PSequence
  $ map (\((a,_),i) -> (a,i))
  $ filter ((j==).snd.fst)
  $ colxs
  $ fmap rowHead
  $ colFilter (not . rowIsEmpty)  rws

--------------------------------------------------------------------------------
-- crHeadRowAt -

-- | get the head row at @i@.
--
--   __Pre__ for all @i'@ in @rws@ holdst: @i '<=' i'@.
crHeadRowAt :: Eq i => i -> Col i (Row j a) -> Row j a
crHeadRowAt i rws = if i == i' then rw else rowEmpty where
  (rw,i') = colHead rws


