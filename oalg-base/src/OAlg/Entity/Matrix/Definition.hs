
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
  , mtxMap
  
    -- ** Group
  , mtxGroupRow, mtxGroupDim
  , mtxJoin, mtxJoinDim
  
    -- ** Construction
  , matrix, matrixTtl, matrixBlc
  , diagonal, diagonal'

    -- * Duality
  , coMatrix, coMatrixInv, mtxFromOpOp

    -- * Homomorphisms
  , isoCoMatrixDst

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
import OAlg.Data.Singleton
import OAlg.Data.Canonical

import OAlg.Data.Constructable

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Distributive
import OAlg.Structure.Algebraic
import OAlg.Structure.Exponential
import OAlg.Structure.Number

import OAlg.Entity.Product
import OAlg.Entity.Sequence hiding (span)

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Distributive
import OAlg.Hom.Definition

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
              
instance (Additive x, FibredOriented x) => Entity (Matrix x)

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

instance (Additive x, FibredOriented x) => Oriented (Matrix x) where
  type Point (Matrix x) = Dim' x
  orientation (Matrix rw cl _) = cl :> rw


instance (Additive x, FibredOriented x) => Fibred (Matrix x) where
  type Root (Matrix x) = Orientation (Dim' x)

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
-- mtxMap -

mtxMapStruct :: Hom Dst h => Struct Dst y -> h x y -> Matrix x -> Matrix y
mtxMapStruct Struct h (Matrix rw cl xs) = Matrix rw' cl' ys where
  rw' = dimMap (pmap h) rw
  cl' = dimMap (pmap h) cl
  ys = etsElimZeros $ fmap (amap h) xs


-- | mapping of a matrix.
mtxMap :: Hom Dst h => h x y -> Matrix x -> Matrix y
mtxMap h = mtxMapStruct (tau $ range h) h

instance HomDistributive h => Applicative1 h Matrix where
  amap1 = mtxMap

--------------------------------------------------------------------------------
-- Matrix - Duality -

type instance Dual (Matrix x) = Matrix (Op x)

-- | the dual matrix, with inverse 'coMatrixInv'.
coMatrix :: Entity (Point x) => Matrix x -> Dual (Matrix x)
coMatrix (Matrix rw cl xs) = Matrix cl' rw' xs' where
  cl' = dimMap id cl
  rw' = dimMap id rw
  xs' = coEntries xs

-- | from the bidual.
mtxFromOpOp :: Entity (Point x) => Matrix (Op (Op x)) -> Matrix x
mtxFromOpOp (Matrix rw cl xs) = Matrix rw' cl' xs' where
  rw' = dimMap id rw
  cl' = dimMap id cl
  xs' = fmap fromOpOp xs

-- | from the dual matrix, with inverse 'coMatrix'.
coMatrixInv :: Entity (Point x) => Dual (Matrix x) -> Matrix x
coMatrixInv (Matrix rw cl xs) = Matrix cl' rw' xs' where
  cl' = dimMap id cl
  rw' = dimMap id rw
  xs' = coEntriesInv xs

instance EntityPoint x => Dualisable (Matrix x) where
  toDual   = coMatrix
  fromDual = coMatrixInv

--------------------------------------------------------------------------------
-- OpMap Matrix s - Hom -

instance ForgetfulDst s => Applicative (OpMap Matrix s) where
  amap h@ToOp1 = coMatrixDst (tau (toOp1Struct h)) where
    coMatrixDst :: Struct Dst x -> Op (Matrix x) -> Matrix (Op x)
    coMatrixDst Struct = coMatrix . fromOp
    
  amap h@FromOp1 = coMatrixDst (tau (fromOp1Struct h)) where
    coMatrixDst :: Struct Dst x -> Matrix (Op x) -> Op (Matrix x)
    coMatrixDst Struct = Op . coMatrixInv

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomOriented (OpMap Matrix s) where
  pmap h@ToOp1 = coDimDst (tau (toOp1Struct h)) where
    coDimDst :: Struct Dst x -> Point (Op (Matrix x)) -> Point (Matrix (Op x))
    coDimDst Struct = dimMap id

  pmap h@FromOp1 = coDimDst (tau (fromOp1Struct h)) where
    coDimDst :: Struct Dst x -> Point (Matrix (Op x)) -> Point (Op (Matrix x))
    coDimDst Struct = dimMap id
                                                               
instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomMultiplicative (OpMap Matrix s)

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomFibred (OpMap Matrix s)
instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomFibredOriented (OpMap Matrix s)
instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomAdditive (OpMap Matrix s)
instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomDistributive (OpMap Matrix s)

--------------------------------------------------------------------------------
-- IsoOpMap - Hom -

instance ForgetfulDst s => Applicative (IsoOpMap Matrix s) where
  amap = restrict amap

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomOriented (IsoOpMap Matrix s) where pmap = restrict pmap

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomMultiplicative (IsoOpMap Matrix s)

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomFibred (IsoOpMap Matrix s)

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomFibredOriented (IsoOpMap Matrix s)

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomAdditive (IsoOpMap Matrix s)

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomDistributive (IsoOpMap Matrix s)
  
--------------------------------------------------------------------------------
-- IsoOpMap - Functorial -

instance ForgetfulDst s => Functorial (IsoOpMap Matrix s)

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => FunctorialHomOriented (IsoOpMap Matrix s)

--------------------------------------------------------------------------------
-- isoCoMatrixDst -

-- | the contravariant isomorphism from @'Matrix' __x__@ to @'Matrix' ('Op' __x__)@.
isoCoMatrixDst :: Distributive x => IsoOpMap Matrix Dst (Op (Matrix x)) (Matrix (Op x))
isoCoMatrixDst = make (ToOp1 :. IdPath Struct)

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

instance XStandardOrtSite From (Matrix Z) where
  xStandardOrtSite = xoFrom xStandardOrtOrientation
  
instance XStandardOrtSiteFrom (Matrix Z)

instance XStandardOrtSite To (Matrix Z) where
  xStandardOrtSite = xoTo xStandardOrtOrientation
