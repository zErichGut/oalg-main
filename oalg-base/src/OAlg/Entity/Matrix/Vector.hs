{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , FlexibleInstances
  , GADTs
  , MultiParamTypeClasses
  , StandaloneDeriving
#-}

-- |
-- Module      : OAlg.Entity.Matrix.Vector
-- Description : vectors with coefficients lying in a semi rings.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'Vector's with coefficients, lying in a 'Semiring'.
module OAlg.Entity.Matrix.Vector
  ( -- * Vector
    Vector(..), vecpsq, cf, cfsssy, ssycfs, vecrc, vecAppl

    -- * Hom
  , HomSymbol(..), mtxHomSymbol
  
    -- * Representation
  , repMatrix, Representable(..), mtxRepresentable

    -- * Propostion
  , prpRepMatrix, prpRepMatrixZ

    -- * X
  , xVecN
  ) where

import Control.Monad

import Data.Typeable

import Data.List (map,(++))
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Singleton
-- import OAlg.Data.Ord

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
import OAlg.Structure.Exponential
import OAlg.Structure.Vectorial

import OAlg.Entity.Sequence hiding (sy)
import OAlg.Entity.Sum

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Definition

import OAlg.Hom.Definition
import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Vectorial

--------------------------------------------------------------------------------
-- Vector -

-- | vector with coefficients lying in a 'Semiring', indexd by 'N'.
--
-- __Definition__ Let @v = 'Vector' ris@ be in @'Vector' __r__@ with @__r__@ be a 'Semiring',
-- then @v@ is 'valid' iff
--
-- (1) @ris@ is 'valid'
--
-- (2) For all @(r,i)@ in @ris@ holds: @r@ is not equal to 'rZero'.
newtype Vector r = Vector (PSequence N r) deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- vecpsq -

-- | the underlying partial sequence.
vecpsq :: Vector r -> PSequence N r
vecpsq (Vector ris) = ris

--------------------------------------------------------------------------------
-- vector -

-- | the induced vector.
vector :: Semiring r => [(r,N)] -> Vector r
vector = Vector . psqFilter (not . isZero) . psequence (+)

--------------------------------------------------------------------------------
-- cf -

-- | the @i@-th coefficient of the given vector.
--
-- __Example__ Let @v = 'vector' [(-3,2),(9,4)] :: 'Vector' 'Z'@
--
-- >>> map (cf v) [0..8]
-- [0,0,-3,0,9,0,0,0,0]
cf :: Semiring r => Vector r -> N -> r
cf (Vector v) i = fromMaybe rZero (v ?? i)

--------------------------------------------------------------------------------
-- Vector - Entity -

instance Semiring r => Validable (Vector r) where
  valid v@(Vector ris) = (Label $ show $ typeOf v) :<=>: vldVec ris where
    vldVec ris
      = And [ Label "1" :<=>: valid ris
            , Label "2" :<=>: foldl vldxs SValid (psqxs ris)
            ]

    vldxs s ri
      = And [ s
            , (not $ isZero $ fst ri) :?> Params ["(r,i)":=show ri]
            ]

instance Semiring r => Entity (Vector r)

--------------------------------------------------------------------------------
-- Vector - Euclidean -

instance Semiring r => Fibred (Vector r) where
  type Root (Vector r) = ()
  root _ = ()

instance Semiring r => Additive (Vector r) where
  zero _ = Vector psqEmpty
  
  Vector v + Vector w = Vector (psqFilter (not . isZero) $ psqInterlace (+) id id v w)
    
  ntimes x (Vector v) = Vector (psqFilter (not . isZero) $ psqMap (ntimes x) v)

instance Ring r => Abelian (Vector r) where
  negate (Vector v) = Vector (psqMap negate v)
  ztimes x (Vector v) = Vector (psqFilter (not . isZero) $ psqMap (ztimes x) v)

instance (Semiring r, Commutative r) => Vectorial (Vector r) where
  type Scalar (Vector r) = r
  r ! (Vector v) = Vector (psqFilter (not . isZero) $ psqMap (r*) v)

instance (Semiring r, Commutative r) => Euclidean (Vector r) where
  Vector v <!> Vector w
    = foldl (+) rZero
    $ map fst
    $ psqxs
    $ psqInterlace (*) (const rZero) (const rZero) v w

--------------------------------------------------------------------------------
-- ssycfs -

-- | the associated coefficients of a free sum of symbols according to the given set of symbols.
--
-- __Property__ Let @s = s 0 '<' s 1 '<' ..@ be in @'Set' __a__@ and @x@ in
-- @'SumSymbol' __r__ __a__@ then holds:
-- @'ssyprj' s x '==' 'cf' r 0 '!' 'sy' (s 0) '+' 'cf' r  1 '!' 'sy' (s 1) '+' ..@ where
-- @r = 'ssycfs' s x@, 
ssycfs :: (Semiring r, Ord a) => Set a -> SumSymbol r a -> Vector r
ssycfs s x = Vector (psqCompose (PSequence $ lcs $ ssylc x) (PSequence $ listN s))
                              -- :: PSequence a r            :: PSequence N a
             
--------------------------------------------------------------------------------
-- cfsssy -

-- | the associated free sum of symbols according to the given set of symbols and coefficients.
--
-- __Property__ Let @s = s 0 '<' s 1 '<' ..@ be in @'Set' __a__@ and
-- @r@ be in @'Vector' __r__@ then holds:
-- @'cfsssy' s r '==' 'cf' r 0 '!' 'sy' (s 0) '+' 'cf' r  1 '!' 'sy' (s 1) '+' ..@.
cfsssy :: (Semiring r, Commutative r, Entity a, Ord a) => Set a -> Vector r -> SumSymbol r a
cfsssy s v = sumSymbol $ psqxs $ psqCompose (vecpsq v) (PSequence $ map (\(a,i) -> (i,a)) $ listN s)
                             -- :: PSequence i r    :: PSeqeunce a i
                             -- :: PSequence a r

--------------------------------------------------------------------------------
-- vecrc -

-- | a vector as a row with one column at @0@.
vecrc :: Vector r -> Row N (Col N r)
vecrc (Vector (PSequence []))  = rowEmpty
vecrc (Vector v)               = Row $ PSequence [(Col v,0)]

--------------------------------------------------------------------------------
-- vecAppl -

-- | applying a matrix from the left.
vecAppl :: Semiring r => Matrix r -> Vector r -> Vector r
vecAppl m v = crvec (mtxColRow m `etsMlt` vecrc v) where

    crvec :: Col N (Row N r) -> Vector r
    crvec cl = case crHeadColAt 0 cl of Col v -> Vector v

--------------------------------------------------------------------------------
-- HomSymbol -

data HomSymbol r x y where
  HomSymbol :: (Entity x, Ord x, Entity y, Ord y)
    => PSequence x (LinearCombination r y) -> HomSymbol r (SumSymbol r x) (SumSymbol r y)
  Cfs :: (Entity x, Ord x) => Set x -> HomSymbol r (SumSymbol r x) (Vector r)
  Ssy :: (Entity x, Ord x) => Set x -> HomSymbol r (Vector r) (SumSymbol r x)
  HomMatrix :: Matrix r -> HomSymbol r (Vector r) (Vector r)

--------------------------------------------------------------------------------
-- HomSymbol - Entity -

deriving instance Semiring r => Show (HomSymbol r x y)
instance Semiring r => Show2 (HomSymbol r) 

deriving instance Semiring r => Eq (HomSymbol r x y)
instance Semiring r => Eq2 (HomSymbol r)

instance Semiring r => Validable (HomSymbol r x y) where
  valid h = case h of
    HomSymbol lcs -> Label "HomSymbol" :<=>: valid lcs
    Cfs xs        -> Label "Cfs" :<=>: valid xs
    Ssy xs        -> Label "Ssy" :<=>: valid xs
    HomMatrix m   -> Label "HomMatrix" :<=>: valid m
instance Semiring r => Validable2 (HomSymbol r)

instance (Semiring r, Typeable x, Typeable y) => Entity (HomSymbol r x y)
instance Semiring r => Entity2 (HomSymbol r)

--------------------------------------------------------------------------------
-- HomSymbol - HomVectorial -

instance (Semiring r, Commutative r) => Applicative (HomSymbol r) where
  amap (HomSymbol lcs) s = ssySum f s where
    f x = case lcs ?? x of
      Just lc -> lc
      Nothing -> LinearCombination []
  amap (Cfs xs) s = ssycfs xs s
  amap (Ssy xs) v = cfsssy xs v
  amap (HomMatrix m) v = vecAppl m v

instance (Semiring r, Commutative r) => Morphism (HomSymbol r) where
  type ObjectClass (HomSymbol r) = Vec r
  homomorphous m = case m of
    HomSymbol _ -> Struct :>: Struct
    Cfs _       -> Struct :>: Struct
    Ssy _       -> Struct :>: Struct
    HomMatrix _ -> Struct :>: Struct
  

instance (Semiring r, Commutative r) => HomFibred (HomSymbol r) where
  rmap (HomSymbol _) = const ()
  rmap (Cfs _)       = const ()
  rmap (Ssy _)       = const ()
  rmap (HomMatrix _) = const ()

instance (Semiring r, Commutative r) => HomAdditive (HomSymbol r)

instance (Semiring r, Commutative r) => HomVectorial r (HomSymbol r)

--------------------------------------------------------------------------------
-- Representable -

-- | Predicate for a @__r__@-linear homomorphisms between the free sums @'SumSymbol' __r__ __x__@
-- and @'SumSymbol' __r__ __y__@ being /representable/ for the given symbol sets.
--
-- __Definition__ Let @l@ be in @'LinearCombination' __r__ __x__@ and @xs@ be a 'Set' of symbols of
-- @__x__@, then @l@ is called __/representable in/__ @xs@ iff all symbols of @'lcs' l@ are elements
-- of @xs@.
--
-- __Property__ Let @h@ be a @__r__@-linear homomorphism between the free sums
-- @'SumSymbol' __r__ __x__@ and @'SumSymbol' __r__ __y__@, @xs@ a 'Set' of symbols in @__x__@ and
-- @ys@ a 'Set' of symbols in @__y__@, then holds: If for each symbol @x@ in @xs@ the associated
-- 'LinearCombination' of @h '$' x@ is representable in @ys@, then @'Representable' h xs ys@ is
-- 'valid'.
data Representable r h x y where
  Representable :: (Hom (Vec r) h, Entity x, Ord x, Entity y, Ord y)
    => h (SumSymbol r x) (SumSymbol r y) -> Set x -> Set y
    -> Representable r h (SumSymbol r x) (SumSymbol r y)

instance Show2 h => Show (Representable r h x y) where
  show (Representable h xs ys)
    = "Representable " ++ show2 h ++ " (" ++ show xs ++ ") (" ++ show ys ++ ")"

instance Validable (Representable r h x y) where
  valid (Representable h xs ys) = Label "Representable"
    :<=>: vldsVec (tauHom (homomorphous h)) h xs ys where

    vldsVec :: (Hom (Vec r) h, Entity x, Ord x, Ord y)
      => Homomorphous (Vec r) (SumSymbol r x) (SumSymbol r y)
      -> h (SumSymbol r x) (SumSymbol r y) -> Set x -> Set y -> Statement
    vldsVec (Struct :>: _) h xs ys = vlds h (listN xs) ys

    vlds :: (Semiring r, Commutative r, Hom (Vec r) h, Entity x, Ord x, Ord y)
      => h (SumSymbol r x) (SumSymbol r y) -> [(x,N)] -> Set y -> Statement
    vlds _ [] _           = SValid
    vlds h ((x,j):xjs) ys = vld j (ssylc $ h $ sy x) ys && vlds h xjs ys

    vld :: Ord y => N -> LinearCombination r y -> Set y -> Statement
    -- as l = h $ sy x the underling lcs l is orderd in the second argument!
    vld j l ys = ((Set $ amap1 snd $ lcs l) `isSubSet` ys)
      :?> Params ["j":=show j]

--------------------------------------------------------------------------------
-- repMatrix -

repMatricVec :: (Hom (Vec r) h, Entity x, Ord x, Ord y)
  => Homomorphous (Vec r) (SumSymbol r x) (SumSymbol r y)
  -> h (SumSymbol r x) (SumSymbol r y) -> Set x -> Set y -> Matrix r
repMatricVec (Struct :>: Struct) h xs ys = Matrix r c ets where
  r   = dim unit ^ lengthN ys
  c   = dim unit ^ lengthN xs
  ets = rcets $ rowFilter (not.colIsEmpty) $ rc (amap h) (setIndex ys) (listN xs)

  rc :: (Semiring r, Commutative r, Entity x, Ord x)
    => (SumSymbol r x -> SumSymbol r y) -> (y -> Maybe N) -> [(x,N)] -> Row N (Col N r)
  rc h iy = Row . PSequence . cls h iy 
    
  cls :: (Semiring r, Commutative r, Entity x, Ord x)
    => (SumSymbol r x -> SumSymbol r y) -> (y -> Maybe N) -> [(x,j)] -> [(Col N r,j)]
  cls _ _ []           = []
  cls h iy ((x,j):xjs) = (cl iy (h $ sy x),j):cls h iy xjs

  cl :: Semiring r => (y -> Maybe N) -> SumSymbol r y -> Col N r
  cl iy sy
    = Col
    $ PSequence
    $ sortSnd
    $ amap1 (\(r,y) -> (r,fromJust $ iy y))
    $ lcs
    $ ssylc sy


-- | the associated representation matrix of the given @__r__@-homomorphism and the two symbol set.
--
-- __Property__ Let @p = 'Representable' h xs ys@ be in @'Representable' __r__ __h__ __x__ __y__@
-- for a 'Commutative' 'Semiring' @__r__@, then holds:
-- For all @v@ in @'Vector' __r__@ holds: Let @h' = 'HomMatrix' ('repMatrix' p)@ in
--
-- (1) For all @(_,i)@ in @h' '$' v@ holds: @i '<' 'lengthN' ys@.
--
-- (2) @('Ssy' ys '$' h' '$' v) '==' (h '$' 'Ssy' xs '$' v)@.
repMatrix :: Representable r h x y -> Matrix r
repMatrix (Representable h xs ys) = repMatricVec (tauHom (homomorphous h)) h xs ys

--------------------------------------------------------------------------------
-- mtxHomSymbol -

-- | the associated @__r__@-linear homomorphism.
mtxHomSymbol :: Matrix r -> HomSymbol r (SumSymbol r N) (SumSymbol r N)
mtxHomSymbol m = HomSymbol $ d m where
  d :: Matrix r -> PSequence N (LinearCombination r N)
  d = PSequence . rowxs . amap1 collc . etsrc . mtxxs

  collc :: Col N r -> LinearCombination r N
  collc = LinearCombination . colxs
  
--------------------------------------------------------------------------------
-- mtxRepresentable -

-- | the associated representation of a matrix.
mtxRepresentable :: (Semiring r, Commutative r)
  => Matrix r -> Representable r (HomSymbol r) (SumSymbol r N) (SumSymbol r N)
mtxRepresentable m = Representable (mtxHomSymbol m) (Set [0..c]) (Set [0..r]) where
  c = lengthN $ fromDim $ cols m
  r = lengthN $ fromDim $ rows m

--------------------------------------------------------------------------------
-- xVecN -

-- | random variable of @'Vector' __r__@ where all indices are strict smaller then the given bound.
--
-- __Property__ Let @n@ be in 'N' and @xr@ be in @'X' __r__@ then holds:
-- For all @(_,i)@ in the range of @'xVecN' n xr@ holds: @i '<' n@.
xVecN :: Semiring r => N -> X r -> X (Vector r)
xVecN 0 _  = return $ vector []
xVecN n xr = amap1 vector $ xri 5 where
  xri m = xTakeB 0 (m*n) $ xTupple2 xr (xNB 0 (pred n))

dstVecMax :: Semiring r => Int -> N -> X r -> IO ()
dstVecMax d n xr = getOmega >>= putDistribution d (amap1 (lengthN . vecpsq) $ xVecN n xr)

--------------------------------------------------------------------------------
-- prpRepMatrix -

-- | validity of 'repMatrix' for the given vector.
prpRepMatrix :: (Semiring r, Commutative r, Show2 h) => Representable r h x y -> Vector r -> Statement
prpRepMatrix p@(Representable h xs ys) v = Prp "RepMatrix" :<=>:
  And [ Label "1" :<=>: (mi < (It $ lengthN ys))
          :?> Params ["h' $ v":=show w,"max index":=show mi]
      , Label "2" :<=>: ((Ssy ys $ w) == (h $ Ssy xs $ v))
          :?> Params ["p":=show p,"h'":=show h',"v":=show v]
      ]
  where h' = HomMatrix $ repMatrix p
        w  = h' $ v
        mi = cmax $ amap1 snd $ psqxs $ vecpsq w

--------------------------------------------------------------------------------
-- prpRepMatrixZ -

-- | validity of 'repMatrix' for 'Z'-matrices with the given row and column numbers.
prpRepMatrixZ :: N -> N -> Statement
prpRepMatrixZ n m = Forall xrv (uncurry prpRepMatrix) where
  xrv = xTupple2 xr xv
  xr  = amap1 mtxRepresentable $ xoArrow xodZ (c :> r)
  c   = dim () ^ m
  r   = dim () ^ n
  xv  = xVecN m (xZB (-100) 100) 
