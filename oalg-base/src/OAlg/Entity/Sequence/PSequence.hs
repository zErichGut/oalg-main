
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
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
    PSequence(..), psqxs, iProxy
  , psqSpan
  , psqEmpty, psqIsEmpty, psequence
  , psqHead, psqTail
  , psqMap, psqMapShift, psqMapWithIndex, Monotone(..)
  , psqFilter
  , psqSplitWhile
  , psqInterlace
  , psqCompose
  , psqAppend
  , psqShear
  , psqSwap
  , psqTree
  , psqFromTree

    -- * Tree
  , PTree(..), ptrxs, ptrx
  , ptrEmpty
  , ptrMax, ptrMin, ptrSpan
  , ptrFilter, ptrFilterWithIndex
  , ptrMap, ptrMapShift, ptrMapWithIndex
  
    -- * X
  , xPSequence

    -- * Proposition
  , prpPSequence, prpPTreeFilter
  ) where

import Control.Monad 

import Data.Monoid
import Data.Foldable
import Data.Typeable

import Data.List (map,sortBy,groupBy,filter,head,tail,(++),zip,splitAt)

import OAlg.Prelude

import OAlg.Data.Tree
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
-- Monotone -


-- | predicate for strict monoton mappings.
--
-- __Property__ Let @_i__@, @__j__@ two 'Ord'-types, and @'Monotone' f@ in @'Monotone' __i__ __j__@, then
-- holds: For all @x@, @y@ in @__i__@ holds: @'compare' (f x) (f y) '==' 'compare' x y@. 
newtype Monotone i j = Monotone (i -> j)

instance (Ord i, Ord j, XStandard i, Show i) => Validable (Monotone i j) where
  valid (Monotone f) = Label "Monotone"
    :<=>: Forall xy (\(x,y)
                     -> ((compare (f x) (f y) == compare x y) :?> Params ["x":=show x,"y":=show y])
                    )
    where xy = xTupple2 xStandard xStandard

--------------------------------------------------------------------------------
-- psqMapWithIndex -

-- | maps of a 'PSequence' according to the given strict monotone mapping and the given indexed
-- mapping.  
psqMapWithIndex :: Monotone i j -> ((x,i) -> y) -> PSequence i x -> PSequence j y
psqMapWithIndex (Monotone j) y (PSequence xis) = PSequence $ map yj xis where yj xi = (y xi,j $ snd xi)
  
--------------------------------------------------------------------------------
-- psqMapShift -

-- | shifts the indices of a partial sequence.
psqMapShift :: Number i => i -> ((x,i) -> y) -> PSequence i x -> PSequence i y
psqMapShift t = psqMapWithIndex (Monotone (+t))

--------------------------------------------------------------------------------
-- psqMap -

-- | maps the entries, where the indices are preserved.
psqMap :: (x -> y) -> PSequence i x -> PSequence i y
psqMap f = psqMapWithIndex (Monotone id) (f . fst)

instance Functor (PSequence i) where fmap = psqMap

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

-- | @'xPSequence' n m@ random variable of partially defined sequences with maximal length of
--   @'min' n m@.
xPSequence :: Ord i => N -> N -> X x -> X i -> X (PSequence i x)
xPSequence n m xx xi = do
  xs <- xTakeN n xx
  is <- xSet m xi
  return $ PSequence $ (xs `zip` setxs is)

--------------------------------------------------------------------------------
-- PTree -

-- | binary tree for efficient retrieving elements of a partially defined sequence.
newtype PTree i x = PTree (Maybe (Tree i (x,i))) deriving (Show,Eq,Ord)

instance Foldable (PTree i) where
  foldMap _ (PTree Nothing)  = mempty
  foldMap f (PTree (Just t)) = fm f t where
    fm f (Leaf (x,_)) = f x
    fm f (Node _ l r) = fm f l <> fm f r
  

instance (Entity x, Entity i, Ord i) => Validable (PTree i x) where
  valid (PTree mt) = Label "PTree" :<=>: case mt of
    Nothing -> SValid
    Just t  -> vld t where
      vld (Node i l r)  = valid i && vldl i l && vldr i r
      vld (Leaf (x,i))  = valid i && valid x
  
      vldl i t = Label "l" :<=>: case t of
        Leaf (_,i') -> And [ vld t
                           , (i' < i) :?> Params ["i":=show i,"i'":=show i']
                           ]
        Node i' l r -> valid i' && vldl i' l && vldr i' r
        
      vldr i t = Label "r" :<=>: case t of
        Leaf (_,i') -> And [ vld t
                           , (i <= i') :?> Params ["i":=show i,"i'":=show i']
                           ]
        Node i' l r -> valid i' && vldl i' l && vldr i' r
    
instance (Entity x, Entity i, Ord i) => Entity (PTree i x)

--------------------------------------------------------------------------------
-- ptrEmpty -

-- | the empty 'PTree'.
ptrEmpty :: PTree i x
ptrEmpty = PTree Nothing

--------------------------------------------------------------------------------
-- psqTree -

-- | the induced tree.
psqTree :: PSequence i x -> PTree i x
psqTree (PSequence [])  = PTree Nothing
psqTree (PSequence xis) = PTree $ Just $ toTree xis where
  toTree [xi] = Leaf xi
  toTree xis  = Node (snd $ head r) (toTree l) (toTree r) where
    (l,r) = splitAt (length xis `divInt` 2) xis

--------------------------------------------------------------------------------
-- psqFromTree -

-- | the induced partially sequence.
psqFromTree :: PTree i x -> PSequence i x
psqFromTree (PTree Nothing)  = psqEmpty
psqFromTree (PTree (Just t)) = PSequence $ toList t

--------------------------------------------------------------------------------
-- ptrxs -

-- | the underlying list of indexed values.
ptrxs :: PTree i x -> [(x,i)]
ptrxs = psqxs . psqFromTree

--------------------------------------------------------------------------------
-- ptrx -

-- | retrieving a value from the tree.
ptrx :: Ord i => PTree i x -> i -> Maybe x
ptrx (PTree Nothing)  _ = Nothing
ptrx (PTree (Just t)) i = if i' == i then Just x else Nothing where (x,i') = trLookup t i

--------------------------------------------------------------------------------
-- ptrMin -

-- | the minimal index.
ptrMin :: PTree i x -> Closure i
ptrMin (PTree Nothing)  = PosInf
ptrMin (PTree (Just t)) = pmin t where
  pmin (Leaf (_,i)) = It i
  pmin (Node _ l _) = pmin l

--------------------------------------------------------------------------------
-- ptrMax -

-- | the maximal index.
ptrMax :: PTree i x -> Closure i
ptrMax (PTree Nothing)  = NegInf
ptrMax (PTree (Just t)) = pmax t where
  pmax (Leaf (_,i)) = It i
  pmax (Node _ _ r) = pmax r

--------------------------------------------------------------------------------
-- ptrSpan -

-- | the span, i.e the minimal and the maximal index of the tree.
ptrSpan :: PTree i x -> Span i
ptrSpan t = (ptrMin t,ptrMax t)

--------------------------------------------------------------------------------
-- ptrFilter -

-- | the sub tree containing all leafs satisfying the given predicate.
ptrFilter :: (x -> Bool) -> PTree i x -> PTree i x
ptrFilter p (PTree t) = PTree (t >>= trFilter (p . fst))

--------------------------------------------------------------------------------
-- ptrFilterWithIndex -

-- | the sub tree containing all leafs satisfying the given indexed predicate.
ptrFilterWithIndex :: ((x,i) -> Bool) -> PTree i x -> PTree i x
ptrFilterWithIndex p (PTree t) = PTree (t >>= trFilter p)

--------------------------------------------------------------------------------
-- ptrMapWithIndex -

-- | maps a 'PTree' according to the given strict monotone mapping and the given indexed
-- mapping.
ptrMapWithIndex :: Monotone i j -> ((x,i) -> y) -> PTree i x -> PTree j y
ptrMapWithIndex _ _ (PTree Nothing)           = PTree Nothing
ptrMapWithIndex (Monotone j) y (PTree (Just t)) = PTree $ Just $ mapwi t where
  mapwi (Leaf xi)    = Leaf (y xi,j $ snd xi)
  mapwi (Node i l r) = Node (j i) (mapwi l) (mapwi r)

--------------------------------------------------------------------------------
-- ptrMapShift -

-- | shifts the indices of a 'PTree'.
ptrMapShift :: Number i => i -> ((x,i) -> y) -> PTree i x -> PTree i y
ptrMapShift t = ptrMapWithIndex (Monotone (+t))

--------------------------------------------------------------------------------
-- ptrMap -

-- | maps a 'PTree' according to the given mapping.
ptrMap :: (x -> y) -> PTree i x -> PTree i y
ptrMap f = ptrMapWithIndex (Monotone id) (f . fst)

instance Functor (PTree i) where fmap = ptrMap

--------------------------------------------------------------------------------
-- prpTreeFilter -

-- | validates the function 'pspTreeFilter'
prpPTreeFilter :: N -> Statement
prpPTreeFilter n = Prp ("PTreeFilter " ++ show n) :<=>:
  Forall xps (\pxs -> (  (filter (p . fst) $ psqxs pxs)
                      == (psqxs $ psqFromTree $ ptrFilter p $ psqTree pxs)
                      ) :?> Params ["pxs":=show pxs]
             ) where

  xps = xOneOfXW [(1,return psqEmpty),(100,xPSequence n n (xZB (-100) 100) xN)]
  p x = x `mod` 2 == 0

--------------------------------------------------------------------------------
-- prpMapShiftPSequence -

-- | validates the shifting of a 'PSequence' and 'PTree'.
prpMapShiftPSequence :: N -> Statement
prpMapShiftPSequence n = Prp "ShiftPSequencePTree" :<=>:
  Forall xxitf (\  (xis,t,f)
               ->  let xis' = ptrMapShift t f $ psqTree xis in
                     And [ valid t
                         , (psqMapShift t f xis == psqFromTree xis')
                             :?> Params ["xis":=show xis,"t":=show t]
                         ]
               )

  where xxitf :: X (PSequence Z Z,Z,(Z,Z) -> Z)
        xxitf = xTupple3 (xPSequence n n xZ xZ) xZ xf
        xf = xOneOf [uncurry (+),uncurry (-)]
  
--------------------------------------------------------------------------------
-- prpPSequence -

-- | validity of 'PSequence'.
prpPSequence :: Statement
prpPSequence = Prp "PSequence"
  :<=>: And [ prpPTreeFilter 60
            , prpMapShiftPSequence 76
            ]

