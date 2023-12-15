{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , GADTs
  , MultiParamTypeClasses
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
    Vector(..), vecpsq, cf, cfsssy, ssycfs, vecRowCol

    -- * ColVec
  , ColVec(..), cvcfs, mtxOplColVec

    -- * Representation
  , repMatrix, Representable(..)

    -- * Propostion
  , prpRepMatrix

    -- * X
  , xVecMax, xColVec
  ) where

import Control.Monad

import Data.Typeable

import Data.List (map,(++))
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
import OAlg.Structure.Operational
import OAlg.Structure.Exponential
import OAlg.Structure.Vectorial

import OAlg.Entity.Sequence hiding (sy)
import OAlg.Entity.Sum

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Definition

import OAlg.Hom.Definition

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
-- ColVec -

-- | a vector as a column to a given dimension.
--
-- __Definition__ Let @c = 'ColVec' n v@ be in @'ColVec' __r__@ for a 'Semiring' @__r__@, then
-- @v@ is 'valid' iff
--
-- (1) @n@ is 'valid'.
--
-- (2) @v@ is 'valid'.
--
-- (3) For all @(_,i)@ in @v@ holds: @i '<' n@
data ColVec r = ColVec N (Vector r) deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- cvcfs -

cvcfs :: ColVec r -> Vector r
cvcfs (ColVec _ v) = v

--------------------------------------------------------------------------------
-- ColVec - Entity -

instance Semiring r => Validable (ColVec r) where
  valid (ColVec n v) = (Label $ show $ typeOf v) :<=>:
    And [ Label "1" :<=>: valid n
        , Label "2" :<=>: valid v
        , Label "3" :<=>: foldl (vldxs n) SValid (psqxs $ vecpsq v)
        ] where
    vldxs n s (_,i) = s && ((i < n) :?> Params ["n":=show n, "i":=show i])

instance Semiring r => Entity (ColVec r)

--------------------------------------------------------------------------------
-- ColVec - Euclidean -

instance Semiring r => Fibred (ColVec r) where
  type Root (ColVec r) = N
  root (ColVec n _) = n

instance Semiring r => Additive (ColVec r) where
  zero n = ColVec n (zero ())
  
  ColVec n v + ColVec m w
    | n /= m    = throw NotAddable
    | otherwise = ColVec n (v+w)
    
  ntimes x (ColVec n v) = ColVec n (ntimes x v)

instance Ring r => Abelian (ColVec r) where
  negate (ColVec n v) = ColVec n (negate v)
  ztimes x (ColVec n v) = ColVec n (ztimes x v)

instance (Semiring r, Commutative r) => Vectorial (ColVec r) where
  type Scalar (ColVec r) = r
  r ! (ColVec n v) = ColVec n (r!v)

instance (Semiring r, Commutative r) => Euclidean (ColVec r) where
  ColVec n v <!> ColVec m w
    | n /= m    = throw UndefinedScalarproduct
    | otherwise = v <!> w 
  
--------------------------------------------------------------------------------
-- ColVec - Oriented -

instance Semiring r => Oriented (ColVec r) where
  type Point (ColVec r) = Dim' r
  orientation (ColVec n _) = u :> u ^ n where u = dim unit

--------------------------------------------------------------------------------
-- vecRowCol -

-- | a vector as a row with one column at @0@.
vecRowCol :: Vector r -> Row N (Col N r)
vecRowCol (Vector (PSequence []))  = rowEmpty
vecRowCol (Vector v)               = Row $ PSequence [(Col v,0)]

--------------------------------------------------------------------------------
-- mtxOplColVec -

-- | applying a matrix from the left.
mtxOplColVec :: Semiring r => Matrix r -> ColVec r -> ColVec r
mtxOplColVec m c@(ColVec _ v)
  | start m /= end c = throw NotApplicable
  | otherwise        = ColVec (lengthN $ end m) (crvec (mtxColRow m `etsMlt` vecRowCol v)) where

    crvec :: Col N (Row N r) -> Vector r
    crvec cl = case crHeadColAt 0 cl of Col v -> Vector v

--------------------------------------------------------------------------------
-- ColVec - OrientedOpl -

instance Semiring r => Opl (Matrix r) (ColVec r) where (*>) = mtxOplColVec

instance Semiring r => OrientedOpl (Matrix r) (ColVec r)
  
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

instance Show (Representable r h x y) where
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
-- __Property__ Let @__r__@ be a 'Commutative' 'Semiring', @xs@ be a set of symbols in @__x__@,
-- @ys@ be a set of symbols in @__y__@ and @h@ a @__r__@-linear homomorphism from
-- @'SumSymbol' __r__ __x__@ to @'SumSymbol' __r__ __y__@ such that @h@ is representable for @xs@ and
-- @ys@. Let @h' = 'repMatrix' ('Representable' h xs ys)@ be the representation matrix of @h@, then
-- holds: For all @c@ in @'ColVec' r@ with @'root' c '==' 'lengthN' xs@ holds:
-- @('cfsssy' ys '$' 'cvcfs' '$' (h' '*>' c)) '==' (h '$' 'cfsssy' xs '$' 'cvcfs' c)@.
repMatrix :: Representable r h x y -> Matrix r
repMatrix (Representable h xs ys) = repMatricVec (tauHom (homomorphous h)) h xs ys

--------------------------------------------------------------------------------
-- xVecMax -

-- | random variable of @'Vector' __r__@ where all indices are smaller then the given @n@.
--
-- __Property__ Let @n@ be in 'N' and @xr@ be in @'X' __r__@ then holds:
-- For all @(_,i)@ in the range of @'xVecMax' n xr@ holds: @i '<=' n@.
xVecMax :: Semiring r => N -> X r -> X (Vector r)
xVecMax n xr = amap1 vector $ xri 5 where
  xri m = xTakeB 0 (m*n) $ xTupple2 xr (xNB 0 n)

dstVecMax :: Semiring r => Int -> N -> X r -> IO ()
dstVecMax d n xr = getOmega >>= putDistribution d (amap1 (lengthN . vecpsq) $ xVecMax n xr)

--------------------------------------------------------------------------------
-- xColVec -

-- | random variable of @'ColVec' __r__@ with the given length.
--
-- __Property__ Let @n@ be in 'N' and @xr@ be in @'X' __r__@ then holds:
-- For all @c@ in the range of @'xColVec' n@ holds: @'root' c '==' n@.
xColVec :: Semiring r => N -> X r -> X (ColVec r)
xColVec 0 _ = return (ColVec 0 $ vector [])
xColVec n xr = amap1 (ColVec n) $ xVecMax (pred n) xr

--------------------------------------------------------------------------------
-- prpRepMatrix -

-- | validity of 'repMatrix'.
prpRepMatrix :: (Semiring r, Commutative r) => Representable r h x y -> X r -> Statement
prpRepMatrix rep@(Representable h xs ys) xr = Prp "repMatrix" :<=>:
  Forall (xColVec (lengthN xs) xr)
    (\c -> let h' = repMatrix rep in
            ((cfsssy ys $ cvcfs $ (h' *> c)) == (h $ cfsssy xs $ cvcfs c))
            :?> Params ["rep":=show rep, "c":=show c]
    )

