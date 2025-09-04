
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Matrix.Definition
-- Description : definition of matrices over distributive structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- defintion of matrices over 'Distributive' structures.
module OAlg.Entity.Matrix.Definition
  (
    -- * Matrix
    Matrix(..), rows, cols, mtxxs
  , mtxRowCol, mtxColRow
  , mtxMap, mtxDensity
  
    -- ** Group
  , mtxGroupRow, mtxGroupDim
  , mtxJoin, mtxJoinDim
  
    -- ** Construction
  , matrix, matrixTtl, matrixBlc
  , diagonal, diagonal'

    -- * Duality
  , mtxMapS, mtxMapCov, mtxMapCnt

{-  
    -- * Homomorphisms
  , isoCoMatrixDst
-}
  
    -- * X
  , XStandardOrientationMatrix(..)
  , xMatrix, xMatrixTtl

    -- ** Direction
  , xodZ, xodZZ

  ) where

import Control.Monad

import Data.Typeable
import Data.Foldable
import Data.List (map,repeat,zip,span) 

import OAlg.Prelude

import OAlg.Category.Path as P
import OAlg.Category.Dualisable
import OAlg.Category.SDuality

import OAlg.Data.Singleton
import OAlg.Data.Canonical
import OAlg.Data.Either
import OAlg.Data.HomCo

import OAlg.Data.Constructable

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Distributive
import OAlg.Structure.Algebraic
import OAlg.Structure.Exponential
import OAlg.Structure.Number

import OAlg.Entity.Product
import OAlg.Entity.Sequence hiding (span)

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.FibredOriented
import OAlg.Hom.Additive
import OAlg.Hom.Distributive

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Entries


--------------------------------------------------------------------------------
-- Matrix -

-- | matrix over 'Distributive' structures.
--
--  __Property__ Let @'Matrix' rw cl xijs@ be in @'Matrix' __a__@ for a 'Distributive'
--  structure __@a@__, then holds:
--
--  (1) @rw@ and @cl@ are 'valid'.
--
--  (2) @xijs@ is 'valid'.
--
--  (3) For all @(x,i,j)@ in @xijs@ holds:
--
--      (1) @x@ is not 'zero'.
--
--      (2) @'orientation' x '==' (cl '?' j) ':>' (rw '?' i)@.
data Matrix x = Matrix (Dim' x) (Dim' x) (Entries N N x)

--------------------------------------------------------------------------------
-- rows -

-- | row dimension.
rows :: Matrix x -> Dim' x
rows (Matrix r _ _) = r

--------------------------------------------------------------------------------
-- cols -

-- | column dimension.
cols :: Matrix x -> Dim' x
cols (Matrix _ c _) = c

--------------------------------------------------------------------------------
-- mtxxs -

-- | the entries.
mtxxs :: Matrix x -> Entries N N x
mtxxs (Matrix _ _ xs) = xs

--------------------------------------------------------------------------------
-- mtxDensity -

-- | the density of the entries of a matrix, which is the number of the entries divided by the
-- product of the number of its rows and columns.
mtxDensity :: Matrix x -> Maybe Q
mtxDensity m = case (lengthN $ rows m) * (lengthN $ cols m) of
 0 -> Nothing
 d -> Just $ ((inj $ lengthN $ mtxxs m) % d)

--------------------------------------------------------------------------------
-- Matrix - Entity -

deriving instance Oriented x => Show (Matrix x)
deriving instance Oriented x => Eq (Matrix x)
deriving instance (Oriented x, Ord x, OrdPoint x) => Ord (Matrix x)

instance (Additive x, FibredOriented x) => Validable (Matrix x) where
  valid m@(Matrix rw cl (Entries (PSequence xijs))) = Label (show $ typeOf m) :<=>:
    And [ Label "1" :<=>: Label "rw" :<=>: valid rw
        , Label "1" :<=>: Label "cl" :<=>:valid cl
        , case xijs of
            []         -> SValid
            (xij:xijs) -> vld rw cl xij xijs
        ] where
    vld rw cl xij []         = vldEntries rw cl xij
    vld rw cl xij (xlk:xijs) = And [ vldEntries rw cl xij
                                   , Label "2" :<=>: let ij = snd xij
                                                         lk = snd xlk
                                      in (ij < lk) :?>Params ["(ij,kl)":=show (ij,lk)]
                                   , vld rw cl xlk xijs
                                   ]

    vldEntries rw cl xij@(x,(i,j)) 
      = And [ Label "2" :<=>: valid xij
            , Label "3.1" :<=>: (not (isZero x)) :?> Params ["xij":=show xij]
            , Label "3.2" :<=>: (orientation x == (cl ? j) :> (rw ? i))
                :?> Params ["xij":=show xij]
            ]
              
-- instance (Additive x, FibredOriented x) => Entity (Matrix x)

--------------------------------------------------------------------------------
-- mtxColRow -

-- | viewing as a column of rows.
mtxColRow :: Matrix x -> Col N (Row N x)
mtxColRow (Matrix _ _ xs) = etscr xs

--------------------------------------------------------------------------------
-- mtxRowCol -

-- | viewing as a row of columns.
mtxRowCol :: Matrix x -> Row N (Col N x)
mtxRowCol (Matrix _ _ xs) = etsrc xs

--------------------------------------------------------------------------------
-- Matrix - Distributive -

type instance Point (Matrix x) = Dim' x

instance Oriented x => ShowPoint (Matrix x)
instance Oriented x => EqPoint (Matrix x)
instance Oriented x => ValidablePoint (Matrix x)
instance (Typeable x, TypeablePoint x) => TypeablePoint (Matrix x)

instance (Additive x, FibredOriented x) => Oriented (Matrix x) where
  orientation (Matrix rw cl _) = cl :> rw

type instance Root (Matrix x) = Orientation (Dim' x)

instance Oriented x => ShowRoot (Matrix x)
instance Oriented x => EqRoot (Matrix x)
instance Oriented x => ValidableRoot (Matrix x)
instance (Typeable x, TypeablePoint x) => TypeableRoot (Matrix x)

instance (Additive x, FibredOriented x) => Fibred (Matrix x)

instance (Additive x, FibredOriented x) => FibredOriented (Matrix x)

instance (Additive x, FibredOriented x) => Additive (Matrix x) where
  zero (cl:>rw) = Matrix rw cl etsEmpty
  Matrix rw cl xs + Matrix rw' cl' ys
    | rw == rw' && cl == cl' = Matrix rw cl (etsAdd xs ys)
    | otherwise              = throw $ NotAddable
  ntimes n (Matrix rw cl xs)
    = Matrix rw cl (etsElimZeros $ fmap (ntimes n) xs)

instance (Abelian x, FibredOriented x) => Abelian (Matrix x) where
  negate (Matrix rw cl xs) = Matrix rw cl (fmap negate xs)
  ztimes z (Matrix rw cl xs)
    = Matrix rw cl (etsElimZeros $ fmap (ztimes z) xs)

instance (Vectorial x, FibredOriented x) => Vectorial (Matrix x) where
  type Scalar (Matrix x) = Scalar x
  r ! Matrix rw cl xs = Matrix rw cl $ etsElimZeros $ fmap (r!) xs
  
instance Distributive x => Multiplicative (Matrix x) where
  one d = Matrix d d ones where
    ones = etsElimZeros $ Entries $ PSequence $ map (\(p,i) -> (one p,(i,i))) $ dimxs d
                                          
  Matrix i k xs * Matrix k' j ys
    | k == k' = Matrix i j (crets $ etsMlt (etscr xs) (etsrc ys))
    | otherwise = throw NotMultiplicable

  npower m 1                  = m
  npower m _ | not (isEndo m) = throw NotExponential
  npower m 0                  = one (rows m)
  npower (Matrix r _ xs) n    = Matrix r r (crets xs') where
    xs' = foldl etsMlt (etscr xs) $ takeN (pred n) $ repeat $ (etsrc xs)

instance Distributive x => Distributive (Matrix x)

instance TransformableG Matrix Dst Dst where tauG Struct = Struct
instance TransformableGRefl Matrix Dst

instance Algebraic x => Algebraic (Matrix x)

--------------------------------------------------------------------------------
-- Transposable -

instance (Distributive x, TransposableDistributive x) => Transposable (Matrix x) where
  transpose (Matrix r c xs) = Matrix c r (transpose xs)

instance (Distributive x, TransposableDistributive x) => TransposableOriented (Matrix x)
instance (Distributive x, TransposableDistributive x)
  => TransposableMultiplicative (Matrix x)
instance (Distributive x, TransposableDistributive x) => TransposableDistributive (Matrix x)

--------------------------------------------------------------------------------
-- matrix -

-- | matrix with the given row and column number and the given entries for a
--  'Distributive' structure.
--
--   __Property__ Let @m = 'matrix' rw cl xis@ then holds
--
--   [Pre] For all @(x,i,j)@ in @xijs@ holds: @'start' x '==' cl '?' j@ and
--   @'end' x '==' rw '?' i@.
--
--   [Post] @m@ is 'valid'.
--
--  __Note__ The given entries will be sorted, aggregated and 'zero's eliminated.
matrix :: (Additive x, p ~ Point x)
  => Dim x p -> Dim x p -> [(x,N,N)] -> Matrix x
matrix rw cl xijs = Matrix rw cl xijs' where
  xijs' = etsElimZeros $ Entries $ psequence (+) $ map (\(x,i,j) -> (x,(i,j))) xijs

--------------------------------------------------------------------------------
-- matrixTtl -

-- | matrix with the given row and column number and the given entries for a 'Total'
--  'Distributive' structure.
--
--   __Property__ Let @m = 'matrixTtl' rws cls xis@ then holds
--
--   [Pre] For all @(_,i,j)@ in @xijs@ holds: @i '<' rws@ and @j '<' cls@.
--
--   [Post] @m@ is 'valid'.
--
--  __Note__ The given entries will be sorted, aggregated and 'zero's eliminated.
matrixTtl :: (Additive x, FibredOriented x, Total x) => N -> N -> [(x,N,N)] -> Matrix x
matrixTtl rws cls = matrix rw cl where
  rw = dim unit ^ rws
  cl = dim unit ^ cls

--------------------------------------------------------------------------------
-- matrixBlc -

-- | block matrices as matrix of matrices.
matrixBlc :: (Additive x, FibredOriented x)
  => [Dim' x] -> [Dim' x] -> [(Matrix x,N,N)] -> Matrix (Matrix x)
matrixBlc rws cls = matrix rw cl where
  rw = productDim rws
  cl = productDim cls

--------------------------------------------------------------------------------
-- diagonal' -

-- | diagonal matrix with entries starting at the given index offset.
diagonal' :: Additive x => N -> Dim' x -> Dim' x -> [x] -> Matrix x
diagonal' r n m xs = matrix n m xs' where
  xs' = map (\(x,i) -> (x,i,i)) (xs `zip` [r..])
  
--------------------------------------------------------------------------------
-- diagonal -

-- | diagonal matrix with entries starting at the index @0@ (see 'diagonal'').
diagonal :: Additive x => Dim' x -> Dim' x -> [x] -> Matrix x
diagonal = diagonal' 0
  
--------------------------------------------------------------------------------
-- mtxJoinDim -

-- | joining the dimension of matrices over @__x__@.
mtxJoinDim :: Oriented x => Dim' (Matrix x) -> Dim' x
mtxJoinDim (Dim dm) = Dim
                 $ make
                 $ prfMapTotal f
                 $ prfMapTotal g
                 $ form dm
  where f :: U (ProductSymbol x) -> ProductForm N (U x)
        f (U xs) = form xs
        
        g :: U (Dim' x) -> ProductForm N (U (ProductSymbol (Point x)))
        g (U (Dim xs)) = P $ U xs

--------------------------------------------------------------------------------
-- mtxJoin -
        
-- | joining block matrices, i.e. matrices of matrices.
mtxJoin :: Oriented x => Matrix (Matrix x) -> Matrix x
mtxJoin (Matrix rw cl ets) = Matrix rw' cl' ets' where
  rw' = mtxJoinDim rw
  cl' = mtxJoinDim cl
  
  ets' = etsJoin di dj $ fmap mtxxs ets
  di = psyMap lengthN $ fromDim rw
  dj = psyMap lengthN $ fromDim cl

--------------------------------------------------------------------------------
-- mtxGroupDim -

-- | groups a formal product of points @p 0 '^' r 0 '*' .. '*' p n '^' r n@ into a formal
-- product of dimensions @('dim' [p 0] '^' r o) '*' .. '*' ('dim' [p n] '^' r n)@.
mtxGroupDim :: Distributive x => Dim' x -> Dim' (Matrix x)
mtxGroupDim d = productDim $ map (\(p,n) -> dim p ^ n) $ fromWord $ dimwrd d

--------------------------------------------------------------------------------
-- mtxGroupRow -

-- | groups the rows with same row dimensions into a matrix of matrices with one column
-- and n rows accordingly.
mtxGroupRow :: Distributive x => Matrix x -> Matrix (Matrix x)
mtxGroupRow (Matrix r c xs) = Matrix r' c' xs' where
  r'  = mtxGroupDim r
  c'  = dim c
  wrd = fromWord (dimwrd r)
  xs' = Entries $ PSequence $ split c 0 (wrd `zip` [0..]) (colxs $ etscr xs)

  split :: Oriented x
    => Dim' x -> N -> [((Point x,N),N)] -> [(Row N x,N)]
    -> [(Matrix x,(N,N))]
  split _ _ _ []         = []
  split c i [] rws       = error $ show (c,i,rws)
  split c i (((d,l),i''):ds') rws@((_,i'):_)
    | i <= i' && i' < il = (Matrix d' c (crets xs),(i'',0)) : split c il ds' rws'
    | otherwise          = split c il ds' rws
    where il = i+l
          d' = dim d ^ l
          (xs',rws') = span ((<il) . snd) rws
          xs = Col $ PSequence $ map (\(rw,i') -> (rw,i'>-i)) xs'

--------------------------------------------------------------------------------
-- mtxMapCov -

mtxMapCovStruct :: HomDistributiveDisjunctive h
  => Struct Dst y
  -> Variant2 Covariant h x y -> Matrix x -> Matrix y
mtxMapCovStruct Struct h (Matrix rw cl xs) = Matrix rw' cl' ys where
  rw' = dimMap (pmap h) rw
  cl' = dimMap (pmap h) cl
  ys  = etsMapCov h xs

-- | mapping of a matrix.
mtxMapCov :: HomDistributiveDisjunctive h => Variant2 Covariant h x y -> Matrix x -> Matrix y
mtxMapCov h = mtxMapCovStruct (tau $ range h) h

--------------------------------------------------------------------------------
-- mtxMap -

mtxMap :: HomDistributive h => h x y -> Matrix x -> Matrix y
mtxMap h = mtxMapCov (homDisjOpDst h)

--------------------------------------------------------------------------------
-- mtxMapCnt -

mtxMapCntStruct :: HomDistributiveDisjunctive h
  => Struct Dst y
  -> Variant2 Contravariant h x y -> Matrix x -> Matrix y
mtxMapCntStruct Struct h (Matrix rw cl xs) = Matrix cl' rw' ys where
  cl' = dimMap (pmap h) cl
  rw' = dimMap (pmap h) rw
  ys  = etsMapCnt h xs

mtxMapCnt :: HomDistributiveDisjunctive h
  => Variant2 Contravariant h x y -> Matrix x -> Matrix y
mtxMapCnt h = mtxMapCntStruct (tau $ range h) h 

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 Matrix = Matrix

--------------------------------------------------------------------------------
-- mtxMapS -

mtxMapS :: HomDistributiveDisjunctive h
  => h x y -> SDualBi Matrix x -> SDualBi Matrix y
mtxMapS = vmapBi mtxMapCov mtxMapCov mtxMapCnt mtxMapCnt

instance HomDistributiveDisjunctive h => ApplicativeG (SDualBi Matrix) h (->) where
  amapG = mtxMapS

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  ) => FunctorialG (SDualBi Matrix) h (->)

--------------------------------------------------------------------------------
-- coMatrixCov -

-- | covariant mapping to its generalized co-matrix.
coMatrixGCovStruct ::
  ( TransformableDst s
  , TransformableGRefl o s   
  , DualisableDistributive s o 
  )
  => Struct s (Matrix x) -> Struct s x -> o (Matrix x) -> Matrix (o x)
coMatrixGCovStruct sm s = mtxMapCnt (toDualO s) . amap (inv2 t) where Contravariant2 t = toDualO sm

-- | covariant mapping to its generalized co-matrix.
coMatrixGCov ::
  ( TransformableDst s
  , TransformableGRefl o s   
  , DualisableDistributive s o
  , TransformableG Matrix s s
  )
  => Struct s x -> o (Matrix x) -> Matrix (o x)
coMatrixGCov s = coMatrixGCovStruct (tauG s) s

-- | covariant mapping to its co-matrix.
coMatrixCov :: Struct Dst x -> Op (Matrix x) -> Matrix (Op x)
coMatrixCov = coMatrixGCov

--------------------------------------------------------------------------------
-- coMatrixCovInv -

-- | covariant mapping from its generalized co-matrix.
coMatrixGInvCovStruct ::
  ( TransformableDst s
  , TransformableGRefl o s   
  , DualisableDistributive s o
  )
  => Struct s (Matrix x) -> Struct s x -> Matrix (o x) -> o (Matrix x)
coMatrixGInvCovStruct sm s = amap tm . mtxMapCnt (Contravariant2 (inv2 ts))
  where Contravariant2 tm = toDualO sm
        Contravariant2 ts = toDualO s

-- | covariant mapping from its generalized co-matrix.
coMatrixGInvCov ::
  ( TransformableDst s
  , TransformableGRefl o s   
  , DualisableDistributive s o
  , TransformableG Matrix s s
  )
  => Struct s x -> Matrix (o x) -> o (Matrix x)
coMatrixGInvCov s = coMatrixGInvCovStruct (tauG s) s

-- | covariant mapping from its co-matrix.
coMatrixInvCov :: Struct Dst x -> Matrix (Op x) -> Op (Matrix x)
coMatrixInvCov = coMatrixGInvCov

--------------------------------------------------------------------------------
-- coMatrixGPnt -

-- | contravariant 'Point'-mapping to its generalized co-matrix.
coMatrixGPntStruct ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => Struct Dst (o x) -> Struct s x -> Pnt (Matrix x) -> Pnt (Matrix (o x))
coMatrixGPntStruct so@Struct s (Pnt d) = Pnt $ dimMap (pmap t) d where
  Contravariant2 t = toDualO' (q so) s
  q :: Struct Dst (o x) -> Proxy o
  q _ = Proxy

-- | contravariant 'Point'-mapping to its generalized co-matrix.
coMatrixGPnt ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => Struct s x -> Pnt (Matrix x) -> Pnt (Matrix (o x))
coMatrixGPnt s = coMatrixGPntStruct (tau $ tauO s) s
  
--------------------------------------------------------------------------------
-- coMatrixGCovPnt -

-- | covariant 'Point'-mapping to its generalized co-matrix.
coMatrixGCovPntStruct ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => Struct Dst (o x) -> Struct s (Matrix x) -> Struct s x -> Pnt (o (Matrix x)) -> Pnt (Matrix (o x))
coMatrixGCovPntStruct so sm s = coMatrixGPntStruct so s . amapG (inv2 t) where
  Contravariant2 t = toDualO' (q so) sm
  
  q :: Struct Dst (o x) -> Proxy o
  q _ = Proxy

-- | covariant 'Point'-mapping to its generalized co-matrix.
coMatrixGCovPnt ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableG Matrix s s
  )
  => Struct s x -> Pnt (o (Matrix x)) -> Pnt (Matrix (o x))
coMatrixGCovPnt s = coMatrixGCovPntStruct (tau $ tauO s) (tauG s) s

--------------------------------------------------------------------------------
-- coMatrixGInvPnt -

-- | contravariant 'Point'-mapping from its generalized co-matrix.
coMatrixGInvPntStruct ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => q o -> Struct Dst x -> Struct s x -> Pnt (Matrix (o x)) -> Pnt (Matrix x)
coMatrixGInvPntStruct q Struct s (Pnt d) = Pnt $ dimMap (pmap (inv2 t)) d where
  Contravariant2 t = toDualO' q s

-- | contravariant 'Point'-mapping from its generalized co-matrix.
coMatrixGInvPnt ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => Struct s x -> Pnt (Matrix (o x)) -> Pnt (Matrix x)
coMatrixGInvPnt s pmo = coMatrixGInvPntStruct (q pmo) (tau s) s pmo where
  q :: Pnt (Matrix (o x)) -> Proxy o
  q _ = Proxy

--------------------------------------------------------------------------------
-- coMatrixGInvCovPnt -

coMatrixGInvCovPntStruct ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )  
  => q o -> Struct Dst x -> Struct s (Matrix x)
  -> Struct s x -> Pnt (Matrix (o x)) -> Pnt (o (Matrix x))
coMatrixGInvCovPntStruct q sDst sm s = amapG t . coMatrixGInvPntStruct q sDst s where
  Contravariant2 t = toDualO' q sm 

-- | covariant 'Point'-mapping from its generalized co-matrix.
coMatrixGInvCovPnt ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableG Matrix s s
  )  
  => Struct s x -> Pnt (Matrix (o x)) -> Pnt (o (Matrix x))
coMatrixGInvCovPnt s pmo = coMatrixGInvCovPntStruct (q pmo) (tau s) (tauG s) s pmo where
  q :: Pnt (Matrix (o x)) -> Proxy o
  q _ = Proxy

--------------------------------------------------------------------------------
-- coMatrixGRt -

coMatrixGRtStruct ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => Struct Dst (o x) -> Struct s x -> Rt (Matrix x) -> Rt (Matrix (o x))
coMatrixGRtStruct so@Struct s (Rt (cls:>rws)) = Rt (rws':>cls') where
  rws' = dimMap (pmap t) rws
  cls' = dimMap (pmap t) cls
  
  Contravariant2 t = toDualO' (q so) s
  
  q :: Struct Dst (o x) -> Proxy o
  q _ = Proxy

--------------------------------------------------------------------------------
-- coMatrixGCovRt -

coMatrixGCovRtStruct ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => Struct Dst (o x) -> Struct s (Matrix x) -> Struct s x -> Rt (o (Matrix x)) -> Rt (Matrix (o x))
coMatrixGCovRtStruct so sm s = coMatrixGRtStruct so s . amapG (inv2 t) where
  Contravariant2 t = toDualO' (q so) sm  
  q :: Struct Dst (o x) -> Proxy o
  q _ = Proxy

coMatrixGCovRt ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableG Matrix s s
  )
  => Struct s x -> Rt (o (Matrix x)) -> Rt (Matrix (o x))
coMatrixGCovRt s = coMatrixGCovRtStruct (tau $ tauO s) (tauG s) s

--------------------------------------------------------------------------------
-- coMatrixGInvRt -

coMatrixGInvRtStruct ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => q o -> Struct Dst x -> Struct s x -> Rt (Matrix (o x)) -> Rt (Matrix x)
coMatrixGInvRtStruct q Struct s (Rt (cls':>rws')) = Rt (rws:>cls) where
  rws = dimMap (pmap (inv2 t)) rws'
  cls = dimMap (pmap (inv2 t)) cls'
  Contravariant2 t = toDualO' q s

--------------------------------------------------------------------------------
-- coMatrixGInvCovRt -

coMatrixGInvCovRtStruct ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  )
  => q o -> Struct Dst x -> Struct s (Matrix x)
  -> Struct s x -> Rt (Matrix (o x)) -> Rt (o (Matrix x))
coMatrixGInvCovRtStruct q sDst sm s = amapG t . coMatrixGInvRtStruct q sDst s where
  Contravariant2 t = toDualO' q sm 

coMatrixGInvCovRt ::
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableG Matrix s s
  )
  => Struct s x -> Rt (Matrix (o x)) -> Rt (o (Matrix x))
coMatrixGInvCovRt s rmo = coMatrixGInvCovRtStruct (q rmo) (tau s) (tauG s) s rmo where
  q :: Rt (Matrix (o x)) -> Proxy o
  q _ = Proxy

--------------------------------------------------------------------------------
-- HomCo -

instance
  ( TransformableDst s
  , TransformableGRefl o s   
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  )
  => ApplicativeG Id (MorCo Matrix s o) (->) where
  amapG t@ToCo   = toIdG (coMatrixGCov $ mcoStruct t)
  amapG f@FromCo = toIdG (coMatrixGInvCov $ mcoStruct f) 

instance
  ( TransformableDst s
  , TransformableGRefl o s   
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  )
  => ApplicativeG Id (HomCo Matrix s o) (->) where
  amapG h x = y where SVal y = amapG h (SVal x)

instance
  ( TransformableDst s
  , TransformableGRefl o s   
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  )
  => FunctorialG Id (HomCo Matrix s o) (->)

instance
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  )  
  => ApplicativeG Pnt (MorCo Matrix s o) (->) where
  amapG t@ToCo   = coMatrixGCovPnt $ mcoStruct t
  amapG f@FromCo = coMatrixGInvCovPnt $ mcoStruct f

instance
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  ) 
  => ApplicativeG Pnt (HomCo Matrix s o) (->) where
  amapG h x = y where SVal y = amapG h (SVal x)

instance
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  ) 
  => FunctorialG Pnt (HomCo Matrix s o) (->)

instance
  ( DualisableDistributive s o
  , TransformableGRefl o s   
  , TransformableGRefl Matrix s
  , TransformableDst s
  ) 
  => HomOrientedDisjunctive (HomCo Matrix s o)

instance
  ( DualisableDistributive s o
  , TransformableGRefl o s   
  , TransformableGRefl Matrix s
  , TransformableDst s
  ) 
  => HomMultiplicativeDisjunctive (HomCo Matrix s o)


instance
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  )
  => ApplicativeG Rt (MorCo Matrix s o) (->) where
  amapG t@ToCo   = coMatrixGCovRt $ mcoStruct t
  amapG f@FromCo = coMatrixGInvCovRt $ mcoStruct f

instance
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  )
  => ApplicativeG Rt (HomCo Matrix s o) (->) where
  amapG h x = y where SVal y = amapG h (SVal x)

instance
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  )
  => FunctorialG Rt (HomCo Matrix s o) (->)
  
instance
  ( TransformableGRefl o s
  , DualisableDistributive s o
  , TransformableGRefl Matrix s
  , TransformableDst s
  )
  => HomFibred (HomCo Matrix s o)

instance
  ( DualisableDistributive s o
  , TransformableGRefl o s   
  , TransformableGRefl Matrix s
  , TransformableDst s
  )
  => HomFibredOrientedDisjunctive (HomCo Matrix s o)

instance
  ( DualisableDistributive s o
  , TransformableGRefl o s   
  , TransformableGRefl Matrix s
  , TransformableDst s
  ) 
  => HomAdditive (HomCo Matrix s o)

instance
  ( DualisableDistributive s o
  , TransformableGRefl o s   
  , TransformableGRefl Matrix s
  , TransformableDst s
  ) 
  => HomDistributiveDisjunctive (HomCo Matrix s o)


--------------------------------------------------------------------------------
-- xMatrixRL -

-- | random variable of matrices with the given maximal dimension and density.
xMatrix :: Additive x
  => Q -> XOrtOrientation x -> X (Orientation (Point (Matrix x)))
  -> XOrtOrientation (Matrix x)
xMatrix qMax xx xoDim = XOrtOrientation xoDim xMtx where

  xn 0 = XEmpty
  xn n = xNB 0 (pred n)
  
  xMtx (cl:>rw) = do
    n  <- xNB 0 xMax
    xs <- xets n (rw,lrw) (cl,lcl) 
    return $ matrix rw cl xs
    where lcl  = lengthN cl
          lrw  = lengthN rw
          xMax = prj $ fst $ zFloorFraction $ inj (lcl*lrw) * qMax
          
  xets 0 _ _  = return []
  xets n  (rw,lrw) (cl,lcl) = do
    xs <- xets (pred n) (rw,lrw) (cl,lcl)
    i  <- xn lrw
    j  <- xn lcl
    x  <- xoArrow xx (cl ? j :> rw ? i) 
    return ((x,i,j):xs)

--------------------------------------------------------------------------------
-- xMatrixTtl -

-- | random variable of matrices with the given maximal dimension and the given density.
xMatrixTtl :: (Distributive x, Total x)
  => N -> Q -> X x -> XOrtOrientation (Matrix x)
xMatrixTtl dimMax qMax xx = xMatrix qMax (xoTtl xx) xoDim where
  d = dim unit
  xoDim = do
    n <- xNB 0 dimMax
    m <- xNB 0 dimMax
    return (d^n :> d^m)

-- | a random variable of t'Z'-matrices.
xodZ :: XOrtOrientation (Matrix Z)
xodZ = xMatrixTtl 5 0.9 (xZB (-100) 100)


-- | a random variable of t'Z'-bolck-matrices.
xodZZ :: XOrtOrientation (Matrix (Matrix Z))
xodZZ = xMatrix 0.7 xodZ xoDim where
  dMax = 10
  xd = xoPoint xodZ 
  xoDim = do
    n <- xTakeB 0 dMax xd
    m <- xTakeB 0 dMax xd
    return (productDim n :> productDim m)

--------------------------------------------------------------------------------
-- XStandardOrientationMatrix -

-- | standard random variable for the orientations of matrices over @__x__@.
class XStandardOrientationMatrix x where
  xStandardOrientationMatrix :: X (Orientation (Dim' x))
  
--------------------------------------------------------------------------------
-- Matrix - XStandard -

instance XStandardPoint (Matrix Z)

instance XStandardOrientationMatrix Z where
  xStandardOrientationMatrix = do
    n <- xStandard
    m <- xStandard
    return (n:>m)
    
instance ( Additive x, FibredOriented x
         , XStandardOrtOrientation x, XStandardOrientationMatrix x
         )
  => XStandardOrtOrientation (Matrix x) where
  xStandardOrtOrientation = xMatrix 0.8 xStandardOrtOrientation xStandardOrientationMatrix

--------------------------------------------------------------------------------
-- Matrix Z - XStandard -

instance XStandardOrtSite From (Matrix Z) where
  xStandardOrtSite = xoFrom xStandardOrtOrientation
  
instance XStandardOrtSiteFrom (Matrix Z)

instance XStandardOrtSite To (Matrix Z) where
  xStandardOrtSite = xoTo xStandardOrtOrientation

instance XStandard (Matrix Z) where
  xStandard = xosOrt (xStandardOrtSite :: XOrtSite From (Matrix Z))
  
dstXStdMatrixZ :: Int -> (Matrix Z -> String) -> IO ()
dstXStdMatrixZ n f = getOmega >>= putDistribution n (amap1 f xStandard)

