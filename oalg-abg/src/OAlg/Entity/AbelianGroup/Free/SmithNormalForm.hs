
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      : OAlg.Entity.AbelianGroup.Free.SmithNormalForm
-- Description : diagonal and Smith Normal Form for matrices over integers
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- diagonal and Smith Normal Form for 'Z'-matrices.
module OAlg.Entity.AbelianGroup.Free.SmithNormalForm
  (
    -- * Diagonal Form
    zmxDiagonalForm

    -- * Smith Normal Form
  , smithNormalForm, smithNormalForm'
  , zmxDiagonalFormStrictPositive
  , SmithNormalForm(..), snfDiagonalForm

    -- * Proposition
  , prpDiagonalFormZ
  )
  where

import Control.Monad
import Data.List ((++),repeat,dropWhile)

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Reducible

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Number
import OAlg.Structure.Ring

import OAlg.Entity.Product
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence.Permutation
import OAlg.Entity.Sequence.PSequence

import OAlg.Entity.AbelianGroup.Euclid

--------------------------------------------------------------------------------
-- crDiagonalForm -

type TPRows a = ProductForm Z (Transformation a)
type TPCols a = ProductForm Z (Transformation a)
type NF a     = ([a], TPRows a, TPCols a)

-- | reducing a matrix over 'Z' to a diagonal matrix by applying elements of @'GLT' 'Z'@.
-- The entries of the diagonal may not be successively divisible!
crDiagonalForm :: (i ~ N, j ~ N) => Dim Z () -> Dim Z () -> Col i (Row j Z) -> NF Z
crDiagonalForm = dnf' 0

--------------------------------------------------------------------------------
-- dnf -

dnfis :: Eq j => j -> Col i (Row j Z) -> [(Z,i)]
dnfis j = colxs . colTail . crHeadColAt j

dnfjs :: Eq i => i -> Col i (Row j Z) -> [(Z,j)]
dnfjs i = rowxs . rowTail . crHeadRowAt i


-- | transformation by the given offset to diagonal form where the entries of the
-- diagonal may not be successively divisible.
--
-- __Properties__ Let @r@ be in 'N', @n@, @m@ in @'Dim'' 'Z'@ and @rws@ be in
-- @'Col' i ('Row' j 'Z')@ where for all entries @(x,(i,j)@ in @rws@ holds
--
-- (1) @x '/= 0@.
--
-- (2) @r '<=' i@ and @r '<=' j@.
--
-- then holds: Let @(ds,a',b') = 'dnf'' r n m rws@ in
--
-- (1) @0 < d@ for all @d@ in @ds@.
--
-- (2) @(a 'OAlg.Structure.Operational.*>' 'Matrix' n m ('crets' rws))
-- 'OAlg.Structure.Operational.<*' b '==' 'diagonal'' r n m ds@ where
-- @a' = 'RowTrafo' ('make' a' :: 'GLT' 'Z')@ and @b = 'ColTrafo' ('make' b :: 'GLT' 'Z')@.
dnf' :: (i ~ N, j ~ N) => i -> Dim' Z -> Dim' Z -> Col i (Row j Z) -> NF Z
dnf' r n m rws = dnf1 n m r rws ([],One n,One m)

-- | pre:
--
--   (1) for all @i@, @j@ in @rws@ holds: @r '<=' i@ and @r '<=' j@. 
dnf1 :: (i ~ N, j ~ N) => Dim Z () -> Dim Z () -> N -> Col i (Row j Z) -> NF Z -> NF Z
dnf1 dr dc r rws res = if colIsEmpty rws
  then res
  else dnf3 dr dc r rws' (dnfis r rws') (dnfjs r rws') res' where
    (rws',res') = dnf2 dr dc r rws res

-- | swap a non zero entry to the position @(r,r)@ and scale it to be strict positive.
--
-- pre:
--
-- (1) @rws@ is not empty.
--
-- (2) for all @i@, @j@ in @rws@ holds: @r '<=' i@ and @r '<=' j@.
--
-- post:
--
-- (1) the entry @0 '<' rws' r r@.
dnf2 :: (i ~ N, j ~ N)
  => Dim Z () -> Dim Z () -> N -> Col i (Row j Z) -> NF Z -> (Col i (Row j Z),NF Z)
dnf2 dr dc r rws (ds,trs,tcs) = (rws',(ds,trs',tcs')) where
  (rw,i) = colHead rws
  (a,j)  = rowHead rw
  sa     = signum a

  rws'   = (tr |> rws) <| tc where
    t |> rws = prfopl crTrafoRows (inj t) rws
    rws <| t = prfopr crTrafoCols rws (inj t)
    -- tr and tc are reduced and hence alle exponentes are bigger then zero!
    
  tr     = make (P (Scale dr r (Inv sa sa)) :* P (Permute dr dr (swap r i))) :: GLT Z
  tc     = make (P (Permute dc dc (swap r j))) :: GLT Z
  trs'   = form tr :* trs
  tcs'   = tcs :* form tc


-- | @gcd@ of @a@ and @b@ with the appropriate row transformations to eliminate @b@.
--
-- pre: @0 < a@, @k < l@.
tRows :: i ~ N => Dim Z () -> (Z,i) -> (Z,i) -> (Z,TPRows Z)
tRows d (a,k) (b,l) = trws a b (One d) where
  trws a b ts | m == 0 = (a,P (Shear d k l (GL2 1 0 (-q) 1)):*ts) where
    (q,m) = b `divMod` a

  trws a b ts = trws (inj g) (v*b - u*a) (tr:*ts) where
    (g,s,t) = euclid a b
    (_,u,v) = euclid t s -- because g is gcd it follows that gcd s t == 1
    tr = P $ Shear d k l (GL2 s t (-u) v)


-- | @gcd@ of @a@ and @b@ with the appropriate column transformation to eliminate @b@.
--
-- pre: @0 < a@, @k < l@.
tCols :: j ~ N => Dim Z () -> (Z,j) -> (Z,j) -> (Z,TPCols Z)
tCols d ak bl = (g,gltfTrsp tr) where
  (g,tr) = tRows d ak bl


-- | eliminates all non zero entries in the @r@-th row and column
--
-- pre:
--
-- (1) the entry at @(r,r)@ is strict positive
--
-- (1) @is@ are the row numbers of @rws@ with non zero entries at the column @r@
-- with @r '<' i@ for all @i@ in @is@.
--
-- (1) @js@ are the column numbers of @rws@ with non zero entries at the row @r@
-- with @r '<' j@ for all @j@ in @js@.
--
-- post: all entries in the @r@-th row and column - except the one at position @(r,r)@ -
-- are zero (i.e. are eliminated).
dnf3 :: (i ~ N, j ~ N)
  => Dim Z () -> Dim Z () -> N -> Col i (Row j Z) -> [(Z,i)] -> [(Z,i)] -> NF Z -> NF Z
-- this algorithem terminates because in each step the number of primfactors of
-- the entry at postion (r,r) is strict decreasing!
dnf3 dr dc r rws [] [] res = (d:ds,trs,tcs) where
  d            = fst $ rowHead $ fst $ colHead rws
  (ds,trs,tcs) = dnf1 dr dc (r+1) (colTail rws) res

-- eliminates the column
dnf3 dr dc r rws cl@(_:_) _ (ds,trs,tcs)
  = dnf3 dr dc r rws' [] (dnfjs r rws') (ds,form tr :*trs,tcs) where
      t *> rws = prfopl crTrafoRows (inj t) rws
      rws' = tr *> rws
      a    = fst $ rowHead $ fst $ colHead rws
      tr   = make $ elims r a cl (One dr) :: GLT Z

      elims _ _ [] tr          = tr
      elims r a ((b,i):bis) tr = elims r a' bis (tr' :* tr) where
        (a',tr') = tRows dr (a,r) (b,i) 

-- eliminates the row
dnf3 dr dc r rws _ rw@(_:_) (ds,trs,tcs)
  = dnf3 dr dc r rws' (dnfis r rws') [] (ds,trs,tcs:* form tc) where
      rws <* t = prfopr crTrafoCols rws (inj t)
      rws' = rws <* tc
      a    = fst $ rowHead $ fst $ colHead rws
      tc   = make $ elims r a rw (One dc) :: GLT Z
      
      elims _ _ [] tc          = tc
      elims r a ((b,j):bjs) tc = elims r a' bjs (tc :* tc') where
        (a',tc') = tCols dc (a,r) (b,j)


--------------------------------------------------------------------------------
-- zmxDiagonalForm -

-- | transforming a matrix over Z to a diagonal matrix by applying elements of @'GLT' 'Z'@.
zmxDiagonalForm :: Matrix Z -> DiagonalForm Z
zmxDiagonalForm m = m'
  where DiagonalFormStrictPositive m' = zmxDiagonalFormStrictPositive m

--------------------------------------------------------------------------------
-- zmxDiagonalFormStrictPositive -

-- | transforming a matrix over Z to a diagonal matrix with strict positive entries
-- by applying elements of @'GLT' 'Z'@.
--
-- __Property__ Let @m@ be in @'Matrix' Z@ and
-- @'DiagonalFormStrictPositive' d = 'zmxDiagonalFormStrictPositive' m@, then holds:
-- @(a 'OAlg.Structure.Operational.*>' m) 'OAlg.Structure.Operational.<*' b '=='
-- 'diagonal' ('rows' m) ('cols' m) ds@ where  @'DiagonalForm' ds a b = d@.
--
-- __Note__ The entries of the diagonal may not be successively divisible, as such
-- it is a pre-form of the Smith Normal Form.
zmxDiagonalFormStrictPositive :: Matrix Z -> DiagonalFormStrictPositive Z
zmxDiagonalFormStrictPositive (Matrix r c xs)
  = DiagonalFormStrictPositive (DiagonalForm d (RowTrafo $ make trs) (ColTrafo $ make tcs))
    where (d,trs,tcs) = crDiagonalForm r c $ etscr xs

--------------------------------------------------------------------------------
-- SmithNormalForm -

-- | the smith normal form.
--
-- __Properties__ Let @s = 'SmithNormalForm' o ds a b@ be in @'SmithNormalForm' 'Z'@,
-- then holds: 
--
-- (1) @'snfDiagonalForm' s@ is 'valid'.
--
-- (2) For all @k@ in @ks@ holds: @0 < k@.
--
-- (3) For all @..k':'k'..@ in @ks@ holds: @'mod' k' k '==' 0@.
data SmithNormalForm k = SmithNormalForm N [k] (RowTrafo k) (ColTrafo k)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- snfDiagonalForm -

-- | the underlying diagonal form.
snfDiagonalForm :: Semiring k => SmithNormalForm k -> DiagonalForm k
snfDiagonalForm (SmithNormalForm o ds r c)
  = DiagonalForm (takeN o (repeat rOne) ++ ds) r c

--------------------------------------------------------------------------------
-- SmithNormalForm - Validable -

instance Validable (SmithNormalForm Z) where
  valid s@(SmithNormalForm _ ks _ _) = Label "SmithNormalForm" :<=>:
    And [ valid (snfDiagonalForm s)
        , vld (0::N) ks
        ] where

    vld0 i k = Label "2" :<=>: (0 < k):?> Params["(k,i)":=show (k,i)]
    
    vld _ []  = SValid
    vld i [k] = vld0 i k
    vld i (k:k':ks)
      = And [ vld0 i k
            , Label "3" :<=>: (k' `mod` k == 0)
                :?> Params["i":=show i,"(k,k')":=show (k,k')]

            , vld (succ i) (k':ks)
            ]

instance Entity (SmithNormalForm Z)

--------------------------------------------------------------------------------
-- smithNormalForm -

-- | Smith Normal Form of a matrix.
--
-- __Property__ Let @m@ be in @'Matrix' 'Z'@ and
-- @'SmithNormalForm o ds a b = 'smithNormalForm' m@, then holds:
-- @(a 'OAlg.Structure.Operational.*>' m) 'OAlg.Structure.Operational.<*' b '=='
-- 'diagonal' ('rows' m) ('cols' m) ds@ where
-- @ds = ('takeN' o '$' 'repeat' 1) '++' ds'@. 
smithNormalForm :: Matrix Z -> SmithNormalForm Z
smithNormalForm = smithNormalForm' . zmxDiagonalFormStrictPositive

  
-- | Smith Normal Form of a diagonal matrix over 'Z' with strict positive entries.
--
-- __Property__ Let @d = 'DiagonalFormStrictPositive' d' ('DiagonalForm' ds a b)@ be in
-- @'DiagonalFormStrictPositive' 'Z'@, @m = 'dgfMatrix' d'@ and
-- @s = 'smithNormalForm'' d@, then holds: @m '==' 'dgfMatrix' ('snfDiagonalForm' s)@.
smithNormalForm' :: DiagonalFormStrictPositive Z -> SmithNormalForm Z
smithNormalForm' (DiagonalFormStrictPositive (DiagonalForm ds (RowTrafo a) (ColTrafo b)))
  = SmithNormalForm o ds'' (RowTrafo $ make (a':*form a)) (ColTrafo $ make (form b:*b'))
  where
  (ds',a',b') = reduceWith (dnf4 n m) (ds,One n,One m)
  n = start a
  m = end b
  ds'' = dropWhile (==1) ds'
  o = lengthN ds' >- lengthN ds''

-- | reduces the diagonal entries @...d':'d'... = ds@ to smith normal form entries,
--   i.e. @d' `mod` d '==' 0@.
dnf4 :: Dim' Z -> Dim' Z -> NF Z -> Rdc (NF Z )
dnf4 n m = rdcSort >>>= rdcDiv (0::N) where
  
  rdcSort d@(ds,a,b) = if p == one ()
    then return d
    else reducesTo (ds',P (Permute n n p):*a,b:*P(Permute m m (invert p)))
    where (ds',p) = permuteByN compare id ds

  rdcDiv i (ds,a,b) = case ds of
    (d:d':ds') | d' `mod` d /= 0
      -> reducesTo (e:e':ds',a':*a,b:*P (Shear m i i' (GL2 1 0 1 1)):*b') where
          i' = succ i
          ([e,e'],a',b') = dnf' i n m (etscr xs)
          -- from ds is stirct positive follows that dnf yields a diagonal with two elements 
          xs = Entries $ PSequence [(d,(i,i)),(d',(i',i)),(d',(i',i'))] 
                   
    (d:ds') -> rdcDiv (succ i) (ds',a,b) >>= \(ds',a,b) -> return (d:ds',a,b)
    
    _       -> return (ds,a,b)

--------------------------------------------------------------------------------
-- prpDiagonalFormZ -

-- | validating diagonal and Smith Normal form for 'Z'-matrices.
prpDiagonalFormZ :: N -> Q -> Statement
prpDiagonalFormZ dMax dens = Prp "DiagonalFormZ" :<=>:
  Forall (xoOrt $ xMatrixTtl dMax dens xStandard)
    (\m -> let d@(DiagonalFormStrictPositive d') = zmxDiagonalFormStrictPositive m
               s = smithNormalForm' d
           in
             And [ valid (d,s)
                 , Label "DiagonalForm" :<=>:
                     (m == dgfMatrix d'):?> Params ["m":=show m]
                 , Label "SmithNormalForm" :<=>:
                     (m == dgfMatrix (snfDiagonalForm s)):?> Params ["m":=show m]
                 ]
    )


