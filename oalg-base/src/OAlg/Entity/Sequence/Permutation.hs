
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Sequence.Permutation
-- Description : permutations on totally ordered index types
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- permutations on totally ordered index types @__i__@ to permute the items of sequences.
module OAlg.Entity.Sequence.Permutation
  (
    -- * Permutation
    Permutation(), pmt, swap

    -- * Permutable
  , PermutableSequence(..), permuteByN

    -- * Signum
  , pmtSign, splitCycles, splitCycle, Cycle(..)  

    -- * Form
  , PermutationForm(..), pmf

    -- * X
  , xPermutation, xPermutationB, xPermutationN
  , xMltPermutation

    -- * Propositions
  , prpPermutation
  , prpPermutableSequence
  , prpOprPermutation
  ) where

import Control.Monad hiding (sequence)

import Data.List as L (map,zip,repeat,(++),head,tail,splitAt,reverse,span)
import Data.Foldable
import Data.Proxy

import OAlg.Prelude

import OAlg.Data.Filterable
import OAlg.Data.Canonical
import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Symbol (Symbol())

import OAlg.Entity.Product

import OAlg.Entity.Sequence.Definition as D
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.CSequence
import OAlg.Entity.Sequence.Set

import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Exponential
import OAlg.Structure.Operational
import OAlg.Structure.Number.Definition (mod)

--------------------------------------------------------------------------------
-- PermutationForm -

-- | form of a permutation from @__i__@ to @__i__@ which is given by 'pmf'.
--
--  __Property__ Let @p = 'PermutationForm' jis@ be in @'PermutationForm' __i__@, then
-- holds: @'support' z p '==' 'image' z p@ for some proxy @z@ in @__z__ __i__@.
--
-- The partial sequence @ijs@ is called the __/relevant part/__ of @p@.
newtype PermutationForm i = PermutationForm (PSequence i i) deriving (Show,Eq,LengthN)

instance Ord i => Sequence PermutationForm i i where
  list p (PermutationForm xs) = list p xs
  
--------------------------------------------------------------------------------
-- pmf -

-- | the associated function @__i__@ to @__i__@ and is given by:
--
-- __Definition__ Let @p = 'PermutationForm' jis@ be in @'PermutationForm' __i__@
-- then @'pmf' p i@ is defined by: If there exists an @(j,i')@ in @'psqxs' jis@ with
-- @i' '==' i@ then @'pmf' p i = j@ else @'pmf' p i = i@.
--
-- __Note__
--
-- (1) If the partial sequence @ijs@ is 'valid', then for all @i@ in @__i__@ there exists
-- at most one @(_,i')@ in @'psqxs' jis@ such that @i' '==' i@. As such, the function
-- @'pmf' p@ is well defined.
--
-- (2) If the permutation form @p@ itself is 'valid' than @'pmf' p@ is a bijection
-- and as such a permutation of @__i__@.
--
-- (3) The behavior of 'pmf' differs from '??' as its evaluation will not end up in a
-- 'IndexOutOfSupport'-exception.
pmf :: Ord i => PermutationForm i -> i -> i
pmf (PermutationForm jis) i = case jis ?? i of
  Just j -> j
  _      -> i

--------------------------------------------------------------------------------
-- pmfMlt -

-- | @'pmfMlt' p q@ is the composition of @p@ and @q@, which is given by the
-- composition of there associated functions @'pmf' p '.' 'pmf' q@.
pmfMlt :: Ord i => PermutationForm i -> PermutationForm i -> PermutationForm i
pmfMlt (PermutationForm kjs) (PermutationForm jis) = PermutationForm kis where
  kis = PSequence $ sortSnd $ (psqxs kjs * sortFst (psqxs jis))
  
  [] * jis = jis
  kjs * [] = kjs
  kjs@((k,j):kjs') * jis@((j',i):jis') = case j `compare` j' of
    LT -> (k,j):(kjs' * jis)
    EQ -> (k,i):(kjs' * jis')
    GT -> (j',i):(kjs * jis')

--------------------------------------------------------------------------------
-- pmfOprPsq -

-- | @'pmfOprPsq' xs p@ applies the permutation form @p@ - from right - to the partial
-- sequence @xs@, which is given by the composition of there associated functions
-- @('??') xs '.' 'pmf' p@.
pmfOprPsq :: Ord i => PSequence i x -> PermutationForm i -> PSequence i x
pmfOprPsq xjs (PermutationForm jis) = PSequence (sortSnd xis ++ xis') where
  (xis,xis') = psqxs xjs * sortFst (psqxs jis)

  [] * _                               = ([],[])
  xjs * []                             = ([],xjs)
  xjs@((x,j):xjs') * jis@((j',i):jis') = case j `compare` j' of
    LT -> ((x,j):xis,xis') where (xis,xis') = xjs' * jis
    EQ -> ((x,i):xis,xis') where (xis,xis') = xjs' * jis'
    GT -> xjs * jis'

--------------------------------------------------------------------------------
-- pmfOprLst -

-- | @'pmfOprPsq' xs p@ applies the permutation form @p@ - from right - to the list
-- @xs@, which is given by 'pmfOprPsq' applied to @'PSequence' (xs `'zip` [0..])@.
--
-- __Note__ If @'It' ('lengthN') '<=' u@ - where @(_,u) = 'span' p@ - then no
-- exception will be thrown, but the 'lengthN' of the resulting list may be smaller!
pmfOprLst :: [x] -> PermutationForm N -> [x]
pmfOprLst xs p = prj (xs' `pmfOprPsq` p) where
  xs' = (inj :: [x] -> PSequence N x) xs

--------------------------------------------------------------------------------
-- pmfOprPsy -

type I = N
type WordN x = [(x,N)]

-- | permutes the product symbol by the given permeation form.
pmfOprPsy :: Entity x => CSequence x -> PermutationForm N -> CSequence x
pmfOprPsy (ProductSymbol xjs) p = xis where
  xis = make $ wrdprf () $ Word $ opr (D.span (Just (0::N)) p) 0 (fromWord $ prwrd xjs) p

  expand :: N -> (u,N) -> [(u,I)]
  expand k (u,l) = (takeN l $ repeat u) `zip` [k..]

  opr :: Span N -> N -> WordN u -> PermutationForm N -> WordN u
  opr (l,h) _ w _ | h <= l         = w -- empty span
  opr _ _ [] _                     = []
  opr (l,h) k (w:ws) p | It k' < l = w : opr (l,h) k' ws p
                        | h < It k' = w:ws -- see the note below
                        | otherwise = opr' h k [] (w:ws) p
    where k' = k + snd w
    -- Note: the span of p is within the first word w, and as such, applying p
    -- will not alter w.

  opr' :: Closure N -> N -> [(u,I)] -> WordN u -> PermutationForm N -> WordN u
  opr' _ _ uis [] p            = opr'' (PSequence uis) p
  opr' h k uis ws p | h < It k = opr'' (PSequence uis) p ++ ws
  opr' h k uis (w:ws) p        = opr' h (k+snd w) (uis ++ expand k w) ws p

  opr'' :: PSequence N u -> PermutationForm N -> WordN u
  opr'' uis p = map (\(u,_) -> (u,1)) $ psqxs $ (uis `pmfOprPsq` p)

--------------------------------------------------------------------------------
-- pmfPsq -

-- | orders the partial sequence according to the given ordering an delivers the resulting
-- permutation form.
pmfPsq :: Ord i
  => (w -> w -> Ordering) -> (x -> w) -> PSequence i x -> (PSequence i x,PermutationForm i)
pmfPsq wcmp w (PSequence xjs) = (PSequence xjs',PermutationForm (PSequence jis)) where
  wjxs = sortFstBy cmp $ map (\(x,j) -> ((w x,j),x)) xjs
  js   = map snd xjs
  xjs' = map snd wjxs `zip` js
  jis  = map (snd.fst) wjxs `zip` js

  cmp = compare2 wcmp compare

--------------------------------------------------------------------------------
-- pmfLst -

-- | orders the list according to the given ordering an delivers the resulting
-- permutation form.
pmfLst :: (w -> w -> Ordering) -> (x -> w) -> [x] -> ([x],PermutationForm N)
pmfLst wcmp w xs = (map fst $ psqxs $ xs',p) where
  (xs',p) = pmfPsq wcmp w (inj xs)

--------------------------------------------------------------------------------
-- pmfPsy -

-- | orders the product symbol according to the given ordering an delivers the resulting
-- permutation form.
pmfPsy :: Entity x
  => (w -> w -> Ordering) -> (x -> w) -> CSequence x
  -> (CSequence x,PermutationForm N)
pmfPsy wcmp w xs = (productSymbol xs',p) where
  (xs',p) = pmfLst wcmp w (toList xs)

--------------------------------------------------------------------------------
-- PermuationForm - Entity -
  
instance (Entity i, Ord i) => Validable (PermutationForm i) where
  valid p@(PermutationForm jis) = Label "PermutationForm" :<=>:
    And [ valid jis
        , Label "1" :<=>: (support jis p == image jis p):?>Params ["p":=show p]
        ]

instance (Entity i, Ord i) => Entity (PermutationForm i)

--------------------------------------------------------------------------------
-- PermutationForm - Oriented -

instance (Entity i, Ord i) => Oriented (PermutationForm i) where
  type Point (PermutationForm i) = ()
  orientation = const (():>())

--------------------------------------------------------------------------------
-- PermutationForm - Reducible -

instance Eq i => Reducible (PermutationForm i) where
  reduce (PermutationForm (PSequence jis)) = PermutationForm (PSequence jis') where
    jis' = filter (\(j,i) -> j /= i) jis

--------------------------------------------------------------------------------
-- Permutation -

-- | permutation of a totally ordered index type @__i__@ which yield a /bijection/ 'pmt' on
--  @__i__@. They are constructed using
--
-- * 'make' of a 'valid' 'PermutationForm', which defines also the validity for
-- the constructed permutation.
--
-- * 'swap' and the 'Multiplicative' structure for permutations.
--
-- * 'permuteBy' for 'PermutableSequence'.
--
-- * 'xPermutation' to generate randomly permutations.
--
-- In the following the total right operation '<*' of a permutation on several types of
-- sequences will be defined to achieve the permutation of there items.
--
-- __Definitions__
--
-- [List] Let @xs@ be in @[__x__]@ with @'ConstructableSequence' [] __r__ [__x__]@ and @p@
-- a permutation in @'Permutation' __r__@, then @xs '<*' p@ is given by
-- @'sqcIndexMap' is ('pmt' p) xs@, where @is@ is the image of the support of @xs@
-- under the inverse of @p@.
--
-- [CSequence] Let @xs@ be in @'CSequence' __x__@ with
-- @'ConstructableSequence' 'CSequence' 'N' __x__@ and @p@ a permutation in
-- @'Permutation' 'N'@, then @xs '<*' p@ is given by
-- @'sqcIndexMap' is ('pmt' p) xs@, where @is@ is the image of the support of @xs@
-- under the inverse of @p@.
--
-- [PSequence] Let @xs@ be in @'PSequence' __i__ __x__@ with
-- @'ConstructableSequence' ('PSequence' __i__) __i__ __x__@ and @p@ a permutation in
-- @'Permutation' __i__@, then @xs '<*' p@ is given by
-- @'sqcIndexMap' is ('pmt' p) xs@, where @is@ is the image of the support of @xs@
-- under the inverse of @p@.
--
-- [Permutation] Let @xs@, @p@ be in @'Permutation' __i__@, then @xs '<*' p@ is given
-- by '*'.
--
-- __Note__ The given definitions are not very efficient and only terminate for finite
-- sequences (in fact, a more efficient implementation has been chosen that also
-- terminates for infinite sequences (see example below)). However, they serve on the one
-- hand to define the semantic and to \'prove\' the properties for 'TotalOpr' and on the
-- other hand to verify the chosen implementation for finite sequences (see
-- 'prpOprPermutation').
--
-- __Examples__
--
-- >>> "abcdef" <* (swap 2 5 :: Permutation N)
-- "abfdec"
--
-- the support of a sequence and the relevant image of a permutation may be disjoint which
-- will leave the sequence untouched
--
-- >>> "abcdef" <* (swap 7 10 :: Permutation N)
-- "abcdef"
--
-- the intersection of the support of a sequence with the relevant image of a permutation
-- may be a non empty proper sub set
--
-- >>> "abcdef" <* swap 2 10 :: Permutation N)
-- "abdefc"
--
-- the result can be interpreted as: first, put @c@ at position @10@ and 'Nothing'
-- (which is the item at position @10@) at position @2@. Second, strip all nothings form it.
--
-- Although the given definition of the permutation of sequences dose not terminate for
-- infinite sequences, its implementation will terminate
--
-- >>> takeN 5 $ (([0..] :: [N]) <* (swap 1 2 :: Permutation N)
-- [0,2,1,3,4]
newtype Permutation i = Permutation (PermutationForm i)
  deriving (Show,Eq,Validable,Entity,LengthN)

instance Exposable (Permutation i) where
  type Form (Permutation i) = PermutationForm i
  form (Permutation f) = f

instance Eq i => Constructable (Permutation i) where
  make f = Permutation $ reduce f

instance Ord i => Sequence Permutation i i where
  list f (Permutation p) = list f p
  Permutation p ?? i = p ?? i

--------------------------------------------------------------------------------
-- pmt -

-- | the bijection on @__i__@ for a given permutation and is defined via
--   @'restrict' 'pmf'@.
pmt :: Ord i => Permutation i -> i -> i
pmt = restrict pmf

--------------------------------------------------------------------------------
-- Permutation - Cayleyan -

instance (Entity i, Ord i) => Oriented (Permutation i) where
  type Point (Permutation i) = ()
  orientation = restrict orientation

instance (Entity i, Ord i) => Multiplicative (Permutation i) where
  one _ = make (PermutationForm psqEmpty)
  Permutation f * Permutation g = make (f `pmfMlt` g)

instance Total (Permutation i)

instance (Entity i, Ord i) => Invertible (Permutation i) where
  tryToInvert (Permutation (PermutationForm (PSequence jis)))
    = return (Permutation (PermutationForm (PSequence ijs)))
    where ijs = sortSnd $ map (\(j,i) -> (i,j)) jis

instance (Entity i, Ord i) => Cayleyan (Permutation i)

instance (Entity i, Ord i) => Exponential (Permutation i) where
  type Exponent (Permutation i) = Z
  (^) = zpower

--------------------------------------------------------------------------------
-- swap -

-- | swapping.
--
-- __Property__ Let @p = 'swap' n (i,j)@, then holds:
-- If @i,j '<' n@ then @p@ is the permutation given by swapping @i@ with @j@, otherwise a
-- exception will be thrown.
swap :: (Entity i, Ord i) => i -> i -> Permutation i
swap i j = case i `compare` j of
  LT -> make (PermutationForm (PSequence [(j,i),(i,j)]))
  EQ -> one ()
  GT -> swap j i

--------------------------------------------------------------------------------
-- PermutableSequence -

-- | total right operations of permutations on sequences, admitting the following
--   properties:
--
--  __Property__ Let @__s__@, @__i__@, @__x__@ be an instance of
--  @'PermutableSequence'  __s__ __i__ __x__@, then holds:
--
--  (1) Let @xs@ be in @__s__ __x__@, @p@ in @'Permutation' __i__@ with
--  @'image' z p '<<=' 'support' z xs@ for some @z@ in @__z__ __i__@, then holds:
--  @(xs '<*' p) '??' i '==' ((xs '??') '.' 'pmt' p) i@ for all @i@ in @'support' z xs@.
--
--  (2) Let @xs@ be in @__s__ __x__@, @w@ in @__x__ -> __w__@,
--  @c@ in @__w__ -> __w__ -> 'Ordering'@ and @z@ in @__z__ __i__@, then holds:
--  Let @(xs',p) = 'permuteBy' z c w xs@ in
--
--      (1) @xs' '==' xs '<*' p@.
--
--      (2) @xs'@ is ordered according to @c@ by applying @w@ to its items.
--
--      (3) @'image' z p '<<=' 'support' z xs@.
--
-- __Examples__
--
-- >>> fst $ permuteBy nProxy compare isUpper "abCd1eFgH"
-- "abd1egCFH"
--
-- as @'False' '<' 'True'@
--
-- >>> fst $ permuteBy nProxy (coCompare compare) isUpper "abCd1eFgH"
-- "CFHabd1eg"
--
-- which orders it in the reverse ordering.
class (Sequence s i x, TotalOpr (Permutation i) (s x))
  => PermutableSequence s i x where
  -- | a resulting permuation.
  permuteBy :: p i -> (w -> w -> Ordering) -> (x -> w) -> s x -> (s x,Permutation i)


--------------------------------------------------------------------------------
-- permuteByN -

-- | orders the permutable sequence according to the given ordering an delivers the resulting
-- permutation form.
permuteByN :: PermutableSequence s N x
  => (w -> w -> Ordering) -> (x -> w) -> s x -> (s x,Permutation N)
permuteByN = permuteBy (Just (0 :: N))

--------------------------------------------------------------------------------
-- PSequence N - PermutableSequence -

instance Ord i => Opr (Permutation i) (PSequence i x) where
  xs <* p = pmfOprPsq xs (form p)

instance (Entity i, Ord i, Entity x) => TotalOpr (Permutation i) (PSequence i x)

instance (Entity x, Entity i, Ord i) => PermutableSequence (PSequence i) i x where
  permuteBy _ cmp w xs = (xs',make p) where (xs',p) = pmfPsq cmp w xs

--------------------------------------------------------------------------------
-- [x] - PermutableSequence -

instance Opr (Permutation N) [x] where
  xs <* p = pmfOprLst xs (form p)

instance Entity x => TotalOpr (Permutation N) [x]

instance Entity x => PermutableSequence [] N x where
  permuteBy _ wcmp w xs = (xs',make p) where (xs',p) = pmfLst wcmp w xs

--------------------------------------------------------------------------------
-- CSequence - PermutableSequence -

instance Entity x => Opr (Permutation N) (CSequence x) where
  xs <* p = pmfOprPsy xs (form p)

instance Entity x => TotalOpr (Permutation N) (CSequence x)

instance Entity x => PermutableSequence CSequence N x where
  permuteBy _ wcmp w xs = (xs',make p) where (xs',p) = pmfPsy wcmp w xs

--------------------------------------------------------------------------------
-- Permutation - PermutableSequence -

instance (Entity i, Ord i) => Opr (Permutation i) (Permutation i) where
  (<*) = (*)

instance (Entity i, Ord i) => TotalOpr (Permutation i) (Permutation i)

instance (Entity i, Ord i) => PermutableSequence Permutation i i where
  permuteBy f wcmp w (Permutation (PermutationForm p))
    = (make (PermutationForm p'),q) where (p',q) = permuteBy f wcmp w p

--------------------------------------------------------------------------------
-- Cycle -

-- | cycle over the index @__i__@, i.e. a monomorphic list @i 0, i 1 .. i j, i (j+1)..,i (n-1),i n@
--   where @1 <= n@ and represents the permutation where @i j@ maps to @i (j+1)@ for @j = 0..n.1@ and
--   @j n@ maps to @i 0@.
--
--   __Properties__ Let @'Cycle' is@ be in @'Cycle' __i__@, then holds:
--
--  (1) @'length' is '>=' 2@.
--
--  (2) @is@ is monomorph.
newtype Cycle i = Cycle [i] deriving (Show,Eq,Ord)

instance (Show i, Ord i, Validable i) => Validable (Cycle i) where
  valid (Cycle is) = Label "Cycle" :<=>:
    And [ valid is
        , Label "length" :<=>: (lengthN is >= 2) :?> Params ["length is":= (show $ lengthN is)]
        , Label "monomorph" :<=>: (lengthN is == (lengthN $ set is)) :?> Params ["is":=show is]
        ]

--------------------------------------------------------------------------------
-- splitCycle -

-- | splits a permutation in a cycle and its residuum permutation.
splitCycle :: Eq i => Permutation i -> Maybe (Cycle i,Permutation i)
splitCycle p = do
  PermutationForm jis <- return $ form p
  (c,jis')            <- splitCycle' jis
  return (c,make $ PermutationForm jis')

splitCycle' :: Eq i => PSequence i i -> Maybe (Cycle i,PSequence i i)
splitCycle' (PSequence [])          = Nothing
splitCycle' (PSequence ((j,i):jis)) = Just (Cycle $ reverse cs,PSequence jis') where
  (cs,jis') = sc i j ([i],jis)

  sc i j res | i == j = res
  sc i j (cs,jis)     = case L.span ((j/=) . snd) jis of
    (jis',jis'')     -> case jis'' of
      (j',_):jis'''  -> sc i j' (j:cs,jis' ++ jis''')
      _              -> throw $ InvalidData "splitCycle'"
    
--------------------------------------------------------------------------------
-- splitCycles -

-- | splits a permutation in a list of cycles.
splitCycles :: Eq i => Permutation i -> [Cycle i]
splitCycles p = cyc is where
  PermutationForm is = form p
  
  cyc is = case splitCycle' is of
    Nothing      -> []
    Just (c,is') -> c : cyc is'
  
--------------------------------------------------------------------------------
-- pmtSign -

-- | the signum of a permutation
pmtSign :: Permutation N -> Z
pmtSign p = if mod (lengthN $ splitCycles p) 2 == 0 then 1 else -1

--------------------------------------------------------------------------------
-- xPermutation -

-- | random variable of permutations.
xPermutation :: (Entity i, Ord i)
  => N -- ^ maximal number of swappings.
  -> X i -- ^ span of the swappings.
  -> X (Permutation i)
xPermutation n xi = xNB 0 n >>= pmt 0 (one ()) where
  pmt k p n | n <= k = return p
  pmt k p n = do
    (i,j) <- xTupple2 xi xi
    pmt (succ k) (p*swap i j) n

--------------------------------------------------------------------------------
-- xPermutationB -

-- | random variable of permutations within the given bounds.
xPermutationB :: (Ord i, Enum i) => i -> i -> X (Permutation i)
xPermutationB l h = do
  is' <- xp (length is) is
  return $ make $ PermutationForm $ PSequence (is' `zip` is)
  where
    is = enum l h
    xp l is | l <= 1    = return is
            | otherwise = do
      n <- xIntB 1 l
      if n == l
        then return is
        else let (is',is'') = splitAt n is in do
          is''' <- xp (pred l) (is' ++ tail is'')
          return (head is'':is''')

--------------------------------------------------------------------------------
-- xPermutationN -

-- | random variable of permutations of the index set @[0..prd n]@. 
xPermutationN :: N -> X (Permutation N)
xPermutationN 0 = return (one ())
xPermutationN n = xPermutationB 0 (pred n)

dd :: Int -> X (Permutation N) -> IO ()
dd n xp = getOmega >>= putDistribution n (amap1 (`pmt`(0::N)) xp)

--------------------------------------------------------------------------------
-- xMltPermutation -

-- | random variable for validating the 'Multiplicative' structure.
xMltPermutation :: (Entity i, Ord i) => N -> X i -> XMlt (Permutation i)
xMltPermutation n xi = xMltTtl (xNB 0 10) (xPermutation n xi)

--------------------------------------------------------------------------------
-- relOprPermutation -

relOprPermutation :: (TotalOpr (Permutation i) (s x), ConstructableSequence s i x)
  => p i -> s x -> Permutation i -> Statement
relOprPermutation pi xs p = (xs <* p == sqcIndexMap is (pmt p) xs)
                :?>Params ["xs":=show xs,"p":=show p] where
  is = setMap (pmt p') $ support pi xs
  p' = invert p

--------------------------------------------------------------------------------
-- relOprPermutationLst -

relOprPermutationLst :: Entity x => X [x] -> X (Permutation N) -> Statement
relOprPermutationLst xxs xp = Label "[]"
  :<=>: Forall  xxsp (uncurry (relOprPermutation nProxy)) where
  xxsp = xTupple2 xxs xp

--------------------------------------------------------------------------------
-- relOprPermutationPsq -

-- | validity of the right operation of permutations on partial sequences according
--   to its definition.
relOprPermutationPsq :: (Entity x, Entity i, Ord i)
  => X (PSequence i x) -> X (Permutation i) -> Statement
relOprPermutationPsq xxs xp = Label "PSequence"
  :<=>: Forall (xTupple2 xxs xp) (uncurry (relOprPermutation (p xxs))) where
  p :: X (PSequence i x) -> Proxy i
  p _ = Proxy
    
--------------------------------------------------------------------------------
-- relOprPermutationPsy -

relOprPermutationPsy :: Entity x
  => X (CSequence x) -> X (Permutation N) -> Statement
relOprPermutationPsy xxs xp = Label "CSequence"
  :<=>: Forall (xTupple2 xxs xp) (uncurry (relOprPermutation nProxy))

--------------------------------------------------------------------------------
-- prpOprPermutaiton -

-- | validity of the total right operation '<*' of permutations on sequences.
prpOprPermutation :: Statement
prpOprPermutation = Prp "OprPermutation"
  :<=>: And [prpLst,prpPsy,prpPsq] where
  xp n m = xPermutation n (xNB 0 m)

  prpLst = relOprPermutationLst xxs (xp 40 100) where
    xxs  = xNB 0 20 >>= \n -> xTakeN n (xStandard :: X Symbol)

  prpPsy = relOprPermutationPsy xxs (xp 40 100) where
    xxs = xCSequence 20 (xStandard :: X Symbol)
    
  prpPsq = relOprPermutationPsq xxs (xp 40 300) where
    xxs = xPSequence 20 40 (xStandard :: X Symbol) (xNB 0 200)

--------------------------------------------------------------------------------
-- relPmtSqc1 -

relPmtSqc1 :: (PermutableSequence s i x, Entity x, Entity i)
  => N -> z i -> s x -> Statement
relPmtSqc1 n z xs = case is of
  [] -> SValid -- with out this match, there will be denied permisses
  _  -> Forall xpi (\(p,i)
                    -> ((xs<*p)??i == ((xs??) . pmt p) i)
                         :?> Params["xs":=show xs,"p":=show p,"i":=show i]
                   )
  where
    Set is = support z xs
    xi = xOneOf is
    xp = xPermutation n xi
    xpi = xTupple2 xp xi 

--------------------------------------------------------------------------------
-- relPmtSqc2 -

relPmtSqc2 :: (PermutableSequence s i x, Show w)
  => z i -> (w -> w -> Ordering) -> (x -> w) -> s x -> Statement
relPmtSqc2 z c w xs = let (xs',p) = permuteBy z c w xs in
  And [ Label "1" :<=>: (xs' == xs <* p) :?> Params ["xs":=show xs,"p":=show p]
      , Label "2" :<=>: increasing (map fst $ list z xs')
      , Label "3" :<=>: (image z p <<= support z xs) :?> Params ["xs":=show xs,"p":=show p]
      ] where

  w <= w' = case c w w' of
    GT -> False
    _  -> True
    
  increasing []     = SValid
  increasing (x:xs) = inc (0::N) (w x) xs where
    inc _ _ []      = SValid
    inc i wx (y:xs) = let wy = w y in
      And [ (wx <= wy) :?> Params ["i":=show i,"(wx,wy)":=show (wx,wy)]
          , inc (succ i) wy xs
          ]
  
--------------------------------------------------------------------------------
-- prpPermutableSequence -

-- | validity for 'PermutableSequence'.
prpPermutableSequence :: (PermutableSequence s i x, Entity x, Entity i, Show w)
  => N -> z i -> (w -> w -> Ordering) -> (x -> w) -> X (s x) -> Statement
prpPermutableSequence n z c w xxs = Prp "PermutableSequence" :<=>:
  And [ Label "1" :<=>: Forall xxs (relPmtSqc1 n z)
      , Label "2" :<=>: Forall xxs (relPmtSqc2 z c w)
      ]

--------------------------------------------------------------------------------
-- prpPermutation -

-- | validity of the functionality of the module "Permutation".
prpPermutation :: Statement
prpPermutation = Prp "Permutation" :<=>:
  And [ prpMlt (xMltPermutation 20 (xNB 0 50))
      , prpOprPermutation
      , prpPermutableSequence 10 nProxy compare id xxs
      , prpPermutableSequence 15 nProxy compare id xpxs
      , prpPermutableSequence 10 nProxy compare id xpsy
      ] where
  xxs = xNB 0 10 >>= \n -> xTakeN n (xNB 0 20)
  xpxs = xPSequence 20 40 (xStandard :: X Symbol) (xNB 0 200)
  xpsy = xCSequence 20 (xStandard :: X Symbol)


