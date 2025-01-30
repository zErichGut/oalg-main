
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.AbelianGroup.Definition
-- Description : homomorphisms between finitely generated abelian groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between finitely generated abelian groups.
module OAlg.AbelianGroup.Definition
  ( -- * Abelian Group
    AbGroup(..), abg, isSmithNormal
  , abgDim

    -- * Homomorphism
  , AbHom(..)
  , abh, abh'
  , abhz, zabh
  , abhDensity
  , abhSplitable
  
    -- * Adjunction
  , abhFreeAdjunction
  , AbHomFree(..)

    -- * Limes
  , abhProducts, abhSums


    -- * Finite Presentation
  , abgFinPres

    -- * Elements
  , AbElement(..), AbElementForm(..), abge
  , abhvecFree1, vecabhFree1
    -- * X
  , xAbHom, xAbHomTo, xAbHomFrom
  , stdMaxDim, xAbhSomeFreeSlice

    -- * Proposition
  , prpAbHom
  ) where

import Prelude(ceiling)

import Control.Monad
import Control.Applicative ((<|>))

import Data.List (foldl,(++),filter,takeWhile,zip)
import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.FinitelyPresentable

import OAlg.Category.Path as C

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Distributive
import OAlg.Structure.Algebraic
import OAlg.Structure.Exponential
import OAlg.Structure.Number
import OAlg.Structure.Operational

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Distributive

import OAlg.Limes.Limits
import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.ProductsAndSums as L
import OAlg.Limes.KernelsAndCokernels

import OAlg.Adjunction

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding ((++),zip)
import OAlg.Entity.Diagram
import OAlg.Entity.Sequence
import OAlg.Entity.Matrix
import OAlg.Entity.Product
import OAlg.Entity.Slice
import OAlg.Entity.Sum hiding (sy)

import OAlg.AbelianGroup.ZMod
import OAlg.AbelianGroup.Euclid

--------------------------------------------------------------------------------
-- AbGroup -

-- | finitely generate abelian group, i.e. the cartesian product of cyclic groups @'Z'\/n@
--   and are represented as a formal product with symbols in t'ZMod'.
--
-- __Definition__ Let @g@ be in t'AbGroup'. We call @g@ __/smith normal/__ if and only if
-- there exists a sequence @n 0, n 1 .. n (k-1)@ in 'N' with length @k@ and a exponent
-- @r@ in 'N' such that:
--
-- (1) @2 '<=' n i@ for all @0 '<=' i < k@.
--
-- (2) @n (i v'+' 1) `mod` n i '==' 0@ for all @i@ in @0 '<=' i < k-1@.
--
-- (3) @g '==' 'abg' (n 0) v'*' 'abg' (n 1) v'*' .. v'*' 'abg' (n (k-1)) v'*' 'abg' 0 '^' r@.
--
-- __Theorem__ Every finitely generated abelian group is isomorphic to a group in
-- smith normal form. This isomorphism is given by
-- 'OAlg.AbelianGroup.KernelsAndCokernels.isoSmithNormal'.
--
--  __Examples__ Finitely generated abelian groups constructed via 'abg' and its
--  multiplicative structure:
--
-- >>> abg 12
-- AbGroup[Z/12]
--
-- represents the cyclic group @'Z'/12@.
--
-- >>> abg 2 * abg 3
-- AbGroup[Z/2*Z/3]
--
-- represents the cartesian product of the groups @'Z'\/2@ and @'Z'\/3@.
--
-- >>> abg 6 * abg 4 * abg 4
-- AbGroup[Z/6*Z/4^2]
--
-- represents the cartesian product of the groups @'Z'\/6@, @'Z'\/4@  and @'Z'\/4@.
--
-- >>> abg 0 ^ 6
-- AbGroup[Z^6]
-- 
-- represents the free abelian group  @'Z' '^' 6@ of /dimension/ 6.
--
-- >>> one () :: AbGroup
-- AbGroup[]
--
-- represents the cartesian product of zero cyclic groups and
--
-- >>> one () * abg 4 * abg 6 == abg 4 * abg 6
-- True
--
--
-- __Examples__ Checking for smith normal via 'isSmithNormal':
--
-- >>> isSmithNormal (abg 4)
-- True
--
-- >>> isSmithNormal (abg 2 * abg 2)
-- True
--
-- >>> isSmithNormal (abg 17 * abg 51)
-- True
--
-- >>> isSmithNormal (abg 2 * abg 4 * abg 0 ^ 3)
-- True
--
-- >>> isSmithNormal (abg 5 * abg 3)
-- False
--
-- >>> isSmithNormal (abg 0 * abg 3 * abg 6)
-- False
--
-- >>> isSmithNormal (abg 1 * abg 4)
-- False
--
-- >>> isSmithNormal (one ())
-- True
--
-- __Examples__ The associated isomorphism in 'AbHom' of a finitely generated abelian group
-- given by 'OAlg.AbelianGroup.KernelsAndCokernels.isoSmithNormal'.
--
-- >>> end (isoSmithNormal (abg 3 * abg 5))
-- AbGroup[Z/15]
--
-- >>> end (isoSmithNormal (abg 2 * abg 4 * abg 2))
-- AbGroup[Z/2^2*Z/4]
--
-- >>> end (isoSmithNormal (abg 4 * abg 6))
-- AbGroup[Z/2*Z/12]
--
-- >>> end (isoSmithNormal (abg 1))
-- AbGroup[]
newtype AbGroup = AbGroup (ProductSymbol ZMod)
  deriving (Eq,Ord,LengthN,Validable,Entity,Multiplicative)

instance Show AbGroup where
  show (AbGroup g) = "AbGroup[" ++ psyShow g ++ "]"
    

instance Oriented AbGroup where
  type Point AbGroup = ()
  orientation (AbGroup g) = orientation g

instance Exponential AbGroup where
  type Exponent AbGroup = N
  (^) = npower

--------------------------------------------------------------------------------
-- abg -

-- | the cyclic group of the given order as a finitely generated abelian group.
abg :: N -> AbGroup
abg = AbGroup . sy . ZMod

--------------------------------------------------------------------------------
-- abgxs -

-- | the indexed listing of the 'ZMod's.
abgxs :: AbGroup -> [(ZMod,N)]
abgxs (AbGroup g) = psyxs g

--------------------------------------------------------------------------------
-- isSmithNormal -

-- | checks if the given group is smith normal (see definition 'AbGroup').
isSmithNormal :: AbGroup -> Bool
isSmithNormal (AbGroup g) = sn (amap1 fst ws) where
  Word ws = psywrd g

  sn [ZMod n,ZMod n']    = and [2 <= n,(n' == 0) || (n' `mod` n == 0)]
  sn (ZMod n:ZMod n':ws) = and [2 <= n,n' `mod` n == 0,sn (ZMod n':ws)]
  sn [ZMod n]            = (2 <= n) || (n == 0)
  sn _                   = True


--------------------------------------------------------------------------------
-- AbHom -

-- | additive homomorphism between finitely generated abelian groups which are
-- represented by matrices over 'ZModHom'.
newtype AbHom = AbHom (Matrix ZModHom)
  deriving (Show,Eq,Ord,Validable,Entity)

--------------------------------------------------------------------------------
-- abgDim -

-- | the associated dimension for matrices of 'ZModHom'.
abgDim :: AbGroup -> Dim' ZModHom
abgDim (AbGroup g) = Dim g

--------------------------------------------------------------------------------
-- abhDensity -

-- | the density of the abelian homomorphism, i. e. the density of the underlying matrix
-- (see: 'mtxDensity').
abhDensity :: N -> AbHom -> Maybe Q
abhDensity n (AbHom h) = do
  d <- mtxDensity h
  return (ceiling (inj n * d) % n)

--------------------------------------------------------------------------------
-- abhz -

-- | the underlying 'Z'-matrix.
abhz :: AbHom -> Matrix Z
abhz (AbHom (Matrix r c xs)) = Matrix r' c' xs' where
  u = dim ()
  r' = u ^ lengthN r
  c' = u ^ lengthN c

  xs' = amap1 toZ xs

--------------------------------------------------------------------------------
-- zabh -

-- | the associated homomorphism between products of @'abg' 0@ given by the column
-- - respectively row - length.
zabh :: Matrix Z -> AbHom
zabh (Matrix r c xs) = AbHom (Matrix r' c' xs') where
  u = dim (ZMod 0)
  r' = u ^ lengthN r
  c' = u ^ lengthN c

  xs' = amap1 fromZ xs

--------------------------------------------------------------------------------
-- AbHom - Algebraic -

instance Oriented AbHom where
  type Point AbHom = AbGroup
  orientation (AbHom h) = AbGroup s :> AbGroup e where
    Dim s :> Dim e = orientation h

instance Multiplicative AbHom where
  one = AbHom . one . abgDim
  AbHom f * AbHom g = AbHom (f*g)
  npower (AbHom h) n = AbHom (npower h n)

instance Fibred AbHom where
  type Root AbHom = Orientation AbGroup

instance Additive AbHom where
  zero (s :> e) = AbHom (zero (abgDim s :> abgDim e))
  AbHom a + AbHom b = AbHom (a+b)
  ntimes n (AbHom a) = AbHom (ntimes n a)

instance Abelian AbHom where
  negate (AbHom a) = AbHom (negate a)
  AbHom a - AbHom b = AbHom (a-b)
  ztimes z (AbHom a) = AbHom (ztimes z a)
  
instance Vectorial AbHom where
  type Scalar AbHom = Z
  (!) = ztimes

instance FibredOriented AbHom
instance Distributive AbHom
instance Algebraic AbHom

--------------------------------------------------------------------------------
-- abh -

-- | the additive homomorphism with the given orientation and 'ZModHom'-entries.
abh :: Orientation AbGroup -> [(ZModHom,N,N)] -> AbHom
abh (s :> e) xs = AbHom $ matrix (abgDim e) (abgDim s) xs 

-- | the additive homomorphism with the given orientation and 'Z'-entries.
abh' :: Orientation AbGroup -> [(Z,N,N)] -> AbHom
abh' o@(s :> e) xs = abh o xs' where
  xs' = amap1 (\(r,i,j) -> (zmh (s' j :> e' i) r,i,j)) xs
  s' j = fromJust (sp ?? j)
  e' i = fromJust (ep ?? i)
  AbGroup sp = s
  AbGroup ep = e

--------------------------------------------------------------------------------
-- AbHomMap -

-- | morphisms between 'AbHom' and the underlying @'Matrix' 'ZModHom'@ which constitute
-- isomorphisms (see 'IsoAbHomMap').
data AbHomMap x y where
  AbHomMatrix :: AbHomMap AbHom (Matrix ZModHom)
  MatrixAbHom :: AbHomMap (Matrix ZModHom) AbHom

--------------------------------------------------------------------------------
-- AbHomMap - Entity -

deriving instance Show (AbHomMap x y)
instance Show2 AbHomMap
deriving instance Eq (AbHomMap x y)
instance Eq2 AbHomMap

instance Validable (AbHomMap x y) where
  valid AbHomMatrix = SValid
  valid MatrixAbHom = SValid

instance Validable2 AbHomMap

instance (Typeable x, Typeable y) => Entity (AbHomMap x y)
instance Entity2 AbHomMap

--------------------------------------------------------------------------------
-- invAbHomMap -

-- | the inverse.
invAbHomMap :: AbHomMap x y -> AbHomMap y x
invAbHomMap AbHomMatrix = MatrixAbHom
invAbHomMap MatrixAbHom = AbHomMatrix

--------------------------------------------------------------------------------
-- AbHomMap - HomAlgebraic -

instance Morphism AbHomMap where
  type ObjectClass AbHomMap = Alg Z
  homomorphous AbHomMatrix = Struct :>: Struct
  homomorphous MatrixAbHom = Struct :>: Struct

instance Applicative AbHomMap where
  amap AbHomMatrix (AbHom m) = m
  amap MatrixAbHom m = AbHom m

instance TransformableObjectClassTyp AbHomMap

instance HomOriented AbHomMap where
  pmap AbHomMatrix (AbGroup g) = Dim g
  pmap MatrixAbHom (Dim g) = AbGroup g

instance HomMultiplicative AbHomMap

--------------------------------------------------------------------------------
-- PathAbHomMap -

-- | paths of 'AbHomMap'.
type PathAbHomMap = C.Path AbHomMap

--------------------------------------------------------------------------------
-- IsoAbHomMap -

-- | isomorphisms between 'AbHom' and @'Matrix' 'ZModHom'@.
newtype IsoAbHomMap x y = IsoAbHomMap (PathAbHomMap x y)
  deriving (Show,Show2,Validable,Validable2,Eq,Eq2,Entity,Entity2)

--------------------------------------------------------------------------------
-- IsoAbHomMap - Constructable -

-- | reducing paths of 'AbHomMap'.
rdcPathAbHomMap :: PathAbHomMap x y -> Rdc (PathAbHomMap x y)
rdcPathAbHomMap pth = case pth of
  AbHomMatrix :. MatrixAbHom :. p -> reducesTo p >>= rdcPathAbHomMap
  MatrixAbHom :. AbHomMatrix :. p -> reducesTo p >>= rdcPathAbHomMap
  h :. p                          -> rdcPathAbHomMap p >>= return . (h:.)
  p                               -> return p

instance Reducible (PathAbHomMap x y) where
  reduce = reduceWith rdcPathAbHomMap

instance Exposable (IsoAbHomMap x y) where
  type Form (IsoAbHomMap x y) = PathAbHomMap x y
  form (IsoAbHomMap p) = p

instance Constructable (IsoAbHomMap x y) where
  make p = IsoAbHomMap (reduce p)

--------------------------------------------------------------------------------
-- abHomMatrix -

-- | the induced isomorphism from 'AbHom' to @'Matrix' 'ZModHom'@ with inverse 'matrixAbHom'.
abHomMatrix :: IsoAbHomMap AbHom (Matrix ZModHom)
abHomMatrix = IsoAbHomMap (AbHomMatrix :. IdPath Struct)

--------------------------------------------------------------------------------
-- matrixAbHom -

-- | the induced isomorphism from @'Matrix' 'ZModHom'@ to 'AbHom' with inverse 'abHomMatrix'.
matrixAbHom :: IsoAbHomMap (Matrix ZModHom) AbHom
matrixAbHom = IsoAbHomMap (MatrixAbHom :. IdPath Struct)

--------------------------------------------------------------------------------
-- IsoAbHomMap - Cayleyan2 -

instance Morphism IsoAbHomMap where
  type ObjectClass IsoAbHomMap = Alg Z
  homomorphous = restrict homomorphous

instance Category IsoAbHomMap where
  cOne o = IsoAbHomMap (IdPath o)
  IsoAbHomMap f . IsoAbHomMap g = make (f . g)

instance Cayleyan2 IsoAbHomMap where
  invert2 (IsoAbHomMap f) = IsoAbHomMap (reverse id invAbHomMap f) 

--------------------------------------------------------------------------------
-- IsoAbHomMap - Hom -

instance Applicative IsoAbHomMap where
  amap = restrict amap

instance HomOriented IsoAbHomMap where
  pmap = restrict pmap

instance HomMultiplicative IsoAbHomMap

--------------------------------------------------------------------------------
-- IsoAbHomMap - Functorial -

instance Functorial IsoAbHomMap
instance FunctorialHomOriented IsoAbHomMap

--------------------------------------------------------------------------------
-- abhProducts -

-- | products for 'AbHom'.
abhProducts :: Products n AbHom
abhProducts = lmsMap matrixAbHom mtxProducts

--------------------------------------------------------------------------------
-- abhSums -

-- | sums for 'AbHom'.
abhSums :: Sums n AbHom
abhSums = lmsMap matrixAbHom mtxSums

--------------------------------------------------------------------------------
-- abgFree -

-- | the free abelian group of the given dimension.
--
-- >>> abgFree (Free attest :: Free N6 AbGroup)
-- AbGroup ProductSymbol[Z^6]
abgFree :: Free k x -> AbGroup
abgFree n = abg 0 ^ (freeN n)

--------------------------------------------------------------------------------
-- Sliced (Free k) -

instance Attestable k => Sliced (Free k) AbHom where
  slicePoint = abgFree

--------------------------------------------------------------------------------
-- abgMaybeFree -

-- | check of being free of some length.
--
-- >>> abgMaybeFree (abg 0 ^ 5)
-- Just (SomeFree (Free 5))
--
-- >>> abgMaybeFree (abg 0 ^ 5 * abg 3)
-- Nothing
--
-- >>> abgMaybeFree (abg 0 ^ 5 * abg 3 ^ 0)
-- Just (SomeFree (Free 5))
abgMaybeFree :: AbGroup -> Maybe (SomeFree AbHom)
abgMaybeFree g = case someNatural $ lengthN g of
  SomeNatural k -> if g == abgFree k' then Just (SomeFree k') else Nothing where k' = Free k

--------------------------------------------------------------------------------
-- abgFrees -

-- | number of free components.
abgFrees :: AbGroup -> N
abgFrees = lengthN . filter ((== ZMod 0) . fst) . abgxs

--------------------------------------------------------------------------------
-- abhSplit -

-- | splitable property for 'AbHom' with free start point of any finite dimension.
abhSplitable :: Splitable From Free AbHom
abhSplitable = Splitable abhSplit

abhSplit :: Slice From (Free k) AbHom -> FinList k (Slice From (Free N1) AbHom)
abhSplit (SliceFrom (Free k) h@(AbHom h'))
  = case maybeFinList k $ toAbHoms k 0 $ rowxs $ mtxRowCol h' of
      Just xs -> xs
      _       -> throw $ ImplementationError "abhSplit.maybeFinList"
  where
    r  = end h
    n1 = Free attest :: Free N1 AbHom
    z1 = abg 0 
    
    sZero :: Slice From (Free N1) AbHom
    sZero = zero r

    toAbHoms :: (j ~ N, i ~ N) => Any k -> j -> [(Col i ZModHom,j)] -> [Slice From (Free N1) AbHom]
    toAbHoms W0 _ _                         = []
    toAbHoms (SW k') j []                   = sZero : toAbHoms k' (succ j) []
    toAbHoms (SW k') j cljs@((cl,j'):cljs') = case j `compare` j' of
      LT -> sZero : toAbHoms k' (succ j) cljs
      EQ -> toAbHom cl : toAbHoms k' (succ j) cljs'
      _  -> throw $ ImplementationError "abhSplit.toAbHoms"


    toAbHom :: i ~  N => Col i ZModHom -> Slice From (Free N1) AbHom
    toAbHom cl = SliceFrom n1 h where
      h = abh (z1 :> r) $ amap1 (\(x,i) -> (x,i,0)) $ colxs cl

  
--------------------------------------------------------------------------------
-- AbHomFree -

-- | projection homomorphisms to @'Matrix' 'Z'@.
data AbHomFree x y where
  AbHomFree :: AbHomFree AbHom (Matrix Z)
  FreeAbHom :: AbHomFree (Matrix Z) AbHom

--------------------------------------------------------------------------------
-- AbHomFree - Entity -

deriving instance Show (AbHomFree x y)
instance Show2 AbHomFree
deriving instance Eq (AbHomFree x y)
instance Eq2 AbHomFree

instance Validable (AbHomFree x y) where
  valid AbHomFree = SValid
  valid _         = SValid

instance Validable2 AbHomFree

instance (Typeable x, Typeable y) => Entity (AbHomFree x y)
instance Entity2 AbHomFree

--------------------------------------------------------------------------------
-- AbHomFree - HomAlgebraic -

instance Morphism AbHomFree where
  type ObjectClass AbHomFree = Alg Z
  homomorphous AbHomFree = Struct :>: Struct
  homomorphous FreeAbHom = Struct :>: Struct

instance Applicative AbHomFree where
  amap AbHomFree h@(AbHom (Matrix _ _ xs)) = Matrix n m xs' where
    s :> e = orientation h
    u = dim ()
    n = u ^ abgFrees e
    m = u ^ abgFrees s
    
    xs' = crets $ Col $ PSequence $ frees 0 (abgxs e) (abgxs s) $ colxs $ etscr xs

    frees :: (i ~ N,j ~ N)
      => i -> [(ZMod,i)] -> [(ZMod,j)] -> [(Row j ZModHom,i)] -> [(Row j Z,i)]
    frees _ [] _ _ = []
    frees _ _ _ [] = []
    frees i'' ((ZMod 0,i):is') js rws@((rw,i'):rws') = if i < i'
      then frees (succ i'') is' js rws
      else ((Row $ PSequence $ rwFrees 0 js (rowxs rw),i''):frees (succ i'') is' js rws')
    frees i'' ((ZMod _,i):is') js rws@((_,i'):rws') = if i < i'
      then frees i'' is' js rws
      else frees i'' is' js rws'

    rwFrees :: j ~ N => j -> [(ZMod,j)] -> [(ZModHom,j)] -> [(Z,j)]
    rwFrees _ [] _ = []
    rwFrees _ _ [] = []
    rwFrees j'' ((ZMod 0,j):js') hs@((h,j'):hs') = if j < j'
      then rwFrees (succ j'') js' hs
      else ((toZ h,j''):rwFrees (succ j'') js' hs')
    rwFrees j'' ((ZMod _,j):js') hs@((_,j'):hs') = if j < j'
      then rwFrees j'' js' hs
      else rwFrees j'' js' hs'
    
  amap FreeAbHom m = zabh m

instance HomOriented AbHomFree where
  pmap AbHomFree g = dim () ^ abgFrees g
  pmap FreeAbHom n = abg 0 ^ lengthN n

instance HomMultiplicative AbHomFree
instance HomFibred AbHomFree
instance HomFibredOriented AbHomFree
instance HomAdditive AbHomFree
instance HomDistributive AbHomFree

--------------------------------------------------------------------------------
-- abhFreeAdjucntion -

-- | the projection 'AbHomFree' as left adjoint.
abhFreeAdjunction :: Adjunction AbHomFree (Matrix Z) AbHom
abhFreeAdjunction = Adjunction AbHomFree FreeAbHom u one where
  u :: AbGroup -> AbHom
  u g = AbHom (Matrix (abgDim g') (abgDim g) (Entries $ PSequence $ xs 0 (abgxs g))) where
    g' = pmap FreeAbHom (pmap AbHomFree g)
    o = one (ZMod 0) :: ZModHom
    
    xs :: Enum i => i -> [(ZMod,j)] -> [(ZModHom,(i,j))]
    xs _ []              = []
    xs i ((ZMod n,j):js) = if n /= 0
      then xs i js
      else ((o,(i,j)): xs (succ i) js)

--------------------------------------------------------------------------------
-- abgGeneratorTo -

-- | the generator for a finitely generated abelian group.
--
-- __Property__ Let @a@ be in 'AbGroup', then holds
-- @a '==' g@ where @'Generator' ('DiagramChainTo' g _) _ _ _ _ = 'abgGeneratorTo' a@.  
abgGeneratorTo :: AbGroup -> FinitePresentation To Free AbHom
abgGeneratorTo g@(AbGroup pg) = case (someNatural ng',someNatural ng'') of
  (SomeNatural k',SomeNatural k'') -> GeneratorTo chn (Free k') (Free k'') coker ker lft
  where
    gs   = listN pg
    g's  = filter ((/=ZMod 1) . fst) gs
    g''s = filter ((/=ZMod 0) . fst) g's

    ng' = lengthN g's
    g'  = abg 0 ^ ng'

    ng'' = lengthN g''s
    g'' = abg 0 ^ ng''
    
    p  = abh (g' :> g) $ amap1 (\((z,i),j) -> (zmh (ZMod 0:>z) 1,i,j)) (g's `zip` [0..])
    p' = abh (g'' :> g') $ zs 0 (amap1 fst g's `zip` [0..]) where
      z0 = ZMod 0
      zs _ [] = []
      zs j ((ZMod n,i):g's) = if n /= 0
        then (zmh (z0:>z0) (inj n),i,j):zs (succ j) g's
        else zs j g's 

    chn = DiagramChainTo g (p:|p':|Nil)
    
    ker = LimesProjective (ConeKernel dg p') univ where
      dg = DiagramParallelLR (start p) (end p) (p:|Nil)
      univ :: KernelCone N1 AbHom -> AbHom
      univ (ConeKernel _ (AbHom (Matrix _ c xs))) = AbHom (Matrix (abgDim g'') c xs') where
        xs' = crets $ Col $ PSequence
          $ divRows 0 (amap1 fst g's `zip` [0..]) (listN $ etscr xs)
        
        divRows :: (Enum i, Ord i)
          => i -> [(ZMod,i)] -> [(Row j ZModHom,i)] -> [(Row j ZModHom,i)]
        divRows _ [] _   = []
        divRows _ _ []   = []
        divRows i'' ((ZMod n,i):zis') rws@((rw,i'):rws')
          | n == 0    = divRows i'' zis' rws
          | i == i'   = (amap1 (divZHom (inj n)) rw,i''):divRows (succ i'') zis' rws'
          | otherwise = divRows (succ i'') zis' rws

        divZHom :: Z -> ZModHom -> ZModHom
        divZHom q h = zmh (orientation h) (div (toZ h) q)
    
    coker = LimesInjective (ConeCokernel dg p) univ where
      dg = DiagramParallelRL (end p') (start p') (p':|Nil)
      univ :: CokernelCone N1 AbHom -> AbHom
      univ (ConeCokernel _ (AbHom (Matrix r _ xs))) = AbHom (Matrix r (abgDim g) xs') where
        xs' = rcets $ Row $ PSequence
          $ castCols 0 gs (listN $ etsrc xs)

        castCols :: (Ord j, Enum j)
          => j -> [(ZMod,j)] -> [(Col i ZModHom,j)] -> [(Col i ZModHom,j)]
        castCols _ [] _  = []
        castCols _ _ []  = []
        castCols j'' ((g@(ZMod n),j):gs) cls@((cl,j'):cls')
          | n == 1    = castCols j'' gs cls
          | j'' == j' = (amap1 (castZHom g) cl,j):castCols (succ j'') gs cls'
          | otherwise = castCols (succ j'') gs cls

        castZHom :: ZMod -> ZModHom -> ZModHom
        castZHom g h = zmh (g :> end h) (toZ h)

    lft :: Slice From (Free k) AbHom -> Slice From (Free k) AbHom
    lft (SliceFrom k (AbHom (Matrix _ c xs))) = SliceFrom k $ AbHom (Matrix (abgDim g') c xs') where
      xs' = crets $ Col $ PSequence $ lftRows 0 gs (listN $ etscr xs)

      lftRows :: (Ord i, Enum i)
        => i -> [(ZMod,i)] -> [(Row j ZModHom,i)] -> [(Row j ZModHom,i)]
      lftRows _ [] _ = []
      lftRows _ _ [] = []
      lftRows i'' ((ZMod n,i):gs) rws@((rw,i'):rws')
        | n == 1    = lftRows i'' gs rws
        | i == i'   = (amap1 (fromZ . toZ) rw,i''):lftRows (succ i'') gs rws'
        | otherwise = lftRows (succ i'') gs rws

--------------------------------------------------------------------------------
-- abgFinPres -

-- | free finitely presentations for 'AbHom'. 
abgFinPres :: FinitelyPresentable To Free AbHom
abgFinPres = FinitelyPresentable abgGeneratorTo
--------------------------------------------------------------------------------
-- AbElementForm -

-- | form for a 'AbElement'.
data AbElementForm = AbElementForm AbGroup [(Z,N)] deriving (Eq)

instance Show AbElementForm where
  show (AbElementForm a zis) = shs zis ++ " :: " ++ show a where
    shs []       = "0"
    shs (zi:zis) = sh zi ++ shs' zis

    shs' []       = ""
    shs' (zi:zis) = " + " ++ sh zi ++ shs' zis

    sh (1,i) = "e" ++ show i
    sh (z,i) = show z ++ "!e" ++ show i

--------------------------------------------------------------------------------
-- AbElement -

-- | elements of an finitely generated abelian group. There 'root' - which is an element of 'AbGroup' -
--   gives there affiliated group. They are gererated via 'make'.
newtype AbElement = AbElement (Slice From (Free N1) AbHom) deriving (Show,Eq,Ord,Validable,Entity)

instance LengthN AbElement where
  lengthN (AbElement (SliceFrom _ a)) = lengthN $ end a
  
--------------------------------------------------------------------------------
-- AbElement - Constructable -

instance Exposable AbElement where
  type Form AbElement = AbElementForm
  form (AbElement (SliceFrom _ a)) = AbElementForm (end a) zis where
    zis = amap1 (\(z,i,_) -> (z,i))
        $ etsxs $ mtxxs $ abhz a
  
instance Constructable AbElement where
  make (AbElementForm a zis)
    = AbElement
    $ SliceFrom (Free (SW W0))
    $ abh' (abg 0 :> a)
    $ amap1 (\(z,i) -> (z,i,0))
    $ lcs
    $ ssylc
    $ sumSymbol
    $ filter ((<n).snd)
    $ zis
    where n = lengthN a

--------------------------------------------------------------------------------
-- abge -

-- | the @i@-th canonical generator of the given abelian group.
abge :: AbGroup -> N -> AbElement
abge a i = make (AbElementForm a [(1,i)])

--------------------------------------------------------------------------------
-- vecabhFree1 -

-- | the abelian homomorphism with the free 'start' point of dimension @1@ and free
-- 'end' point of the given dimension according to the given vector.
vecabhFree1 :: N -> Vector Z -> Slice From (Free N1) AbHom
vecabhFree1 r v = SliceFrom (Free attest :: Free N1 AbHom) (zabh h) where
  h = matrixTtl r 1 $ amap1 (\(x,i) -> (x,i,0)) $ filter ((<r).snd) $ psqxs $ vecpsq v 

--------------------------------------------------------------------------------
-- abhvecFree1 -

-- | the underlying 'Z'-vector.
abhvecFree1 :: Slice From (Free N1) AbHom -> Vector Z
abhvecFree1 (SliceFrom _ h) = fstRow $ mtxRowCol $ abhz h where
  fstRow :: (i ~ N, j ~ N) => Row j (Col i r) -> Vector r
  fstRow (Row (PSequence rs)) = case rs of
    []            -> Vector psqEmpty
    [(Col ris,0)] -> Vector ris
    _             -> throw $ InvalidData "abhvecFree1"
    
--------------------------------------------------------------------------------
-- AbElement - Abelian -

instance Fibred AbElement where
  type Root AbElement = AbGroup -- i.e. Root (Slice From (Free N1) AbHom)
  root (AbElement a) = root a

instance Additive AbElement where
  zero g = AbElement (zero g)

  AbElement a + AbElement b = AbElement (a+b)

  ntimes n (AbElement a) = AbElement $ ntimes n a
    
instance Abelian AbElement where
  negate (AbElement a) = AbElement $ negate a

  AbElement a - AbElement b = AbElement (a-b)

  ztimes z (AbElement a) = AbElement $ ztimes z a

instance Vectorial AbElement where
  type Scalar AbElement = Z
  z ! AbElement a = AbElement (z!a)

--------------------------------------------------------------------------------
-- XSomeFreeSliceFromLiftable -

-- | random variable for 'AbHom'.
xsfsflAbHom :: XSomeFreeSliceFromLiftable AbHom
xsfsflAbHom = XSomeFreeSliceFromLiftable xsf where
  q = 0.1
  xsf g = do
    SomeNatural k <- xSomeNatural (xNB 0 stdMaxDim)
    d <- xNB 1 10
    h <- xAbHomTo (inj d * q) (lengthN k) 0 0 g
    return $ SomeFreeSlice $ SliceFrom (Free k) h
    
instance XStandardSomeFreeSliceFromLiftable AbHom where
  xStandardSomeFreeSliceFromLiftable = xsfsflAbHom
  
--------------------------------------------------------------------------------
-- AbGroup - XStandard -

-- | the maximal length of abelian groups for the standard random variable of type
-- @'X' 'AbGroup'@.
--
-- __Property__ @1 '<=' 'stdMaxDim'@.
stdMaxDim :: N
stdMaxDim = 10

stdMaxPrime :: N
stdMaxPrime = 1000

stdPrimes :: [N]
stdPrimes = takeWhile (<=stdMaxPrime) primes

instance XStandard AbGroup where
  xStandard = join
            $ xOneOfW [ (99,amap1 (AbGroup . productSymbol) $ xTakeB 1 stdMaxDim xStandard)
                      , ( 1,return $ one ())
                      ]

instance XStandardPoint AbHom

--------------------------------------------------------------------------------
-- xAbHom -

-- | random variable for 'AbHom' given by a density and an orientation.
xAbHom :: Q -> Orientation AbGroup -> X AbHom
xAbHom q = xAbHom' q (xZB (-100) 100)

-- | random variable of homomorphism of the given 'Orientation.
xAbHom'
  :: Q -- ^ density @d@.
  -> X Z
  -> Orientation AbGroup -> X AbHom
xAbHom' d xz (AbGroup a :> AbGroup b)
  | dab == 0 = return $ AbHom $ zero (Dim a :> Dim b)
  | otherwise = xxs >>= return . AbHom . matrix (Dim b) (Dim a)
  where
    as = psyxs a
    bs = psyxs b
    da = lengthN as
    db = lengthN bs
        
    dab = da*db
    n = prj $ zFloor (d*inj dab) :: N

    xs = filter (\((h,_),_,_) -> not (isZero h))
       [(zmhGenOrd (a :> b),i,j) | (a,j) <- as, (b,i) <- bs] 
         
    xxs = do
      p <- xPermutationB 0 (pred dab) -- 0 < dba
      xets (takeN n (xs <* p))

    xets []            = return []
    xets ((ho,i,j):xs) = do
      xs' <- xets xs
      h' <- xh ho
      return ((h',i,j):xs')

    xh (h,0) = xz >>= return . (! h)
    xh (h,1) = return h
    xh (h,o) = do
      z <- xZB 1 (pred (inj o))
      return (z ! h)

dstXAbHom :: (AbHom -> String) -> Int -> Q -> Orientation AbGroup -> IO ()
dstXAbHom s n q r = getOmega >>= putDistribution n (amap1 s $ xAbHom q r) 

--------------------------------------------------------------------------------
-- xAbHomTo -

-- | random variable of homomorphisms between abelian groups with 'end' equal to the given
-- one.
--
-- @
--    r s t
--   [f    ] a
--   [     ] b
--   [g h  ] c
-- @
xAbHomTo :: Q -> N -> N -> N -> AbGroup -> X AbHom
xAbHomTo d r s t (AbGroup g) = amap1 AbHom xm where

  xm :: X (Matrix ZModHom)
  xm = do
    dr <- return (sy (ZMod 0) ^ r) 
    ds <- xds
    dt <- xdt
    AbHom f <- xAbHom d (AbGroup dr :> AbGroup da)
    AbHom g <- xAbHom d (AbGroup dr :> AbGroup dc)
    AbHom h <- xAbHom d (AbGroup ds :> AbGroup dc)
    let cl = amap1 Dim [dr,ds,dt]
        rw = amap1 Dim [da,db,dc]
        m  = mtxJoin $ matrixBlc rw cl [(f,0,0),(g,2,0),(h,2,1)]
     in do
      pc <- xpc (start m)
      return ((pr *> m) <* pc)

  (g',p) = permuteByN compare id g

  pr :: RowTrafo ZModHom
  pr = RowTrafo (permute (Dim g) (Dim g') (invert p))

  xpc c = do
    p <- xPermutationN (lengthN c)
    return (ColTrafo (permute c (c <* invert p) p))
      
  expAt n w = case w of
    Word ((ZMod m,r):w') | n == m -> (r,Word w')
    _                             -> (0,w)

  w' = psywrd g'

  da = sy (ZMod 0) ^ a
  (a,w'') = expAt 0 w'
  
  db = sy (ZMod 1) ^ b
  (b,w''') = expAt 1 w''
  -- for all ((ZMod n),_) in w''' holds: 2 <= n
    
  dc = wrdpsy w'''

  ms = amap1 ((\(ZMod m) -> m) . fst) $ fromWord w'''
  gms  = gcds ms  
  lms  = lcms ms
  -- 1 <= lms, because 2 <= m for all m in ms
  
  xsl = do
    n <- xNB 1 10
    return $ ZMod (n*lms)

  xsg | gms < 2   = XEmpty
      | ws == []  = XEmpty
      | otherwise = do
          r  <- xNB 1 rMax
          ps <- xTakeN r (xOneOf fs)
          n  <- xNB 1 10
          return $ ZMod (n * foldl (*) 1 ps)
    where Word ws  = nFactorize' stdMaxPrime gms
          fs = amap1 fst ws
          rMax = foldl (+) 0 $ amap1 snd ws
          -- 0 < nMax, because ws is not empty
          
  xds = xTakeN s (xsg <|> xsl) >>= return . productSymbol

  xt | fs == []  = XEmpty
     | otherwise = do
    n <- xNB 1 5
    ps <- xTakeN n (xOneOf fs)
    return $ ZMod $ foldl (*) 1 ps
    where fs = takeN 10 $ filter ((/=0) . mod lms) (stdPrimes)
    
  xdt = case xt of
    XEmpty -> return (productSymbol [])
    _      -> xTakeN t xt >>= return . productSymbol


dstXAbHomTo :: (AbHom -> String) -> Int -> Q -> N -> N -> N -> X AbGroup -> IO ()
dstXAbHomTo w n q r s t xg = getOmega >>= putDistribution n (amap1 w $ xh)
  where xh = xg >>= xAbHomTo q r s t

dns :: AbHom -> String
dns (AbHom (Matrix r c xs))
  | rc == 0   = "empty"
  | p == 0    = "(" ++ show p ++ "," ++ show (p+1) ++ "%)"
  | p == 100  = "full"
  | otherwise = "[" ++ show p ++ "," ++ show (p+1) ++ "%)"
  
  where p = zFloor $ (100*) $ (inj (lengthN xs) % rc)
        rc = lengthN r * lengthN c

lng :: AbHom -> String
lng (AbHom (Matrix r c _)) = show (lengthN r,lengthN c)

lngMax :: AbHom -> String
lngMax (AbHom (Matrix r c _)) = show (lengthN r `max` lengthN c)

--------------------------------------------------------------------------------
-- xAbHomFrom -

-- | random variable of homomorphisms between abelian groups with 'start' equal to the given
-- one.
--
-- @
--    a b c
--   [f    ] r
--   [g   l] s
--   [h    ] t
-- @
xAbHomFrom :: Q -> N -> N -> N -> AbGroup -> X AbHom
xAbHomFrom d r s t (AbGroup g) = amap1 AbHom xm where

  xm :: X (Matrix ZModHom)
  xm = do
    dr <- return (sy (ZMod 0) ^ r)
    ds <- xds
    dt <- xdt
    AbHom f <- xAbHom d (AbGroup da :> AbGroup dr)
    AbHom g <- xAbHom d (AbGroup da :> AbGroup ds)
    AbHom h <- xAbHom d (AbGroup da :> AbGroup dt)
    AbHom l <- xAbHom d (AbGroup dc :> AbGroup ds)
    let cl = amap1 Dim [da,db,dc]
        rw = amap1 Dim [dr,ds,dt]
        m  = mtxJoin $ matrixBlc rw cl [(f,0,0),(g,1,0),(h,2,0),(l,1,2)]
     in do
      pr <- xpr (end m)
      return ((pr *> m) <* pc)

  (g',p) = permuteByN compare id g

  pc :: ColTrafo ZModHom
  pc = ColTrafo (permute (Dim g') (Dim g) p)

  xpr r = do
    p <- xPermutationN (lengthN r)
    return (RowTrafo (permute (r <* p) r p))

  expAt n w = case w of
    Word ((ZMod m,r):w') | n == m -> (r,Word w')
    _                             -> (0,w)

  w' = psywrd g'

  da = sy (ZMod 0) ^ a
  (a,w'') = expAt 0 w'
  
  db = sy (ZMod 1) ^ b
  (b,w''') = expAt 1 w''
  -- for all ((ZMod n),_) in w''' holds: 2 <= n
    
  dc = wrdpsy w'''

  ms = amap1 ((\(ZMod m) -> m) . fst) $ fromWord w'''
  gms  = gcds ms  
  lms  = lcms ms
  -- 1 <= lms, because 2 <= m for all m in ms
  
  xsl = do
    n <- xNB 1 10
    return $ ZMod (n*lms)

  xsg | gms < 2   = XEmpty
      | ws == []  = XEmpty
      | otherwise = do
          r  <- xNB 1 rMax
          ps <- xTakeN r (xOneOf fs)
          n  <- xNB 1 10
          return $ ZMod (n * foldl (*) 1 ps)
    where Word ws  = nFactorize' stdMaxPrime gms
          fs = amap1 fst ws
          rMax = foldl (+) 0 $ amap1 snd ws
          -- 0 < nMax, because ws is not empty
          
  xds = xTakeN s (xsg <|> xsl) >>= return . productSymbol

  xt | fs == []  = XEmpty
     | otherwise = do
    n <- xNB 1 5
    ps <- xTakeN n (xOneOf fs)
    return $ ZMod $ foldl (*) 1 ps
    where fs = takeN 10 $ filter ((/=0) . mod lms) (stdPrimes)
    
  xdt = case xt of
    XEmpty -> return (productSymbol [])
    _      -> xTakeN t xt >>= return . productSymbol
 
--------------------------------------------------------------------------------
-- AbHom - XStandardOrtSite -

instance XStandardOrtSite To AbHom where
  xStandardOrtSite = XEnd xStandard xTo where
    q = 0.1
    d3 = stdMaxDim `div` 3
    xTo g = do
      r <- xNB 0 (stdMaxDim >- 2*d3)
      s <- xNB 0 d3
      t <- xNB 0 d3
      n <- xNB 1 10
      xAbHomTo (inj n * q) r s t g

-- | distribution of the density of the random variable of @'X' 'AbHom'@, induced by the
-- standard random variable of type @'XOrtSite' 'To' 'AbHom'@.
dstXStdOrtSiteToAbHom :: Int -> (AbHom -> String) -> IO ()
dstXStdOrtSiteToAbHom n f = getOmega >>= putDistribution n (amap1 f xh) where
  XEnd xg xt = xStandardOrtSite :: XOrtSite To AbHom
  xh = xg >>= xt

instance XStandardOrtSiteTo AbHom

instance XStandardOrtSite From AbHom where
  xStandardOrtSite = XStart xStandard xFrom where
    q = 0.1
    d3 = stdMaxDim `div` 3
    xFrom g = do
      r <- xNB 0 (stdMaxDim >- 2*d3)
      s <- xNB 0 d3
      t <- xNB 0 d3
      n <- xNB 1 10
      xAbHomFrom (inj n * q) r s t g

-- | distribution of the density of the random variable of @'X' 'AbHom'@, induced by the
-- standard random variable of type @'XOrtSite' 'From' 'AbHom'@.
dstXStdOrtSiteFromAbHom :: Int -> (AbHom -> String) -> IO ()
dstXStdOrtSiteFromAbHom n f = getOmega >>= putDistribution n (amap1 f xh) where
  XStart xg xs = xStandardOrtSite :: XOrtSite From AbHom
  xh = xg >>= xs

instance XStandardOrtSiteFrom AbHom

instance XStandardOrtOrientation AbHom where
  xStandardOrtOrientation = XOrtOrientation xo xh where
    q = 0.1
    XStart xg xFrom = xStandardOrtSite :: XOrtSite From AbHom
    
    xo = do
      s <- xg
      e <- amap1 end $ xFrom s
      return (s:>e)
      
    xh o = do
      n <- xNB 0 10
      xAbHom (inj n * q) o
      
    

--------------------------------------------------------------------------------
-- AbHom - XStandard -

instance XStandard AbHom where
  xStandard = xosOrt (xStandardOrtSite :: XOrtSite From AbHom)

dstXStdAbHom :: Int -> (AbHom -> String) -> IO ()
dstXStdAbHom n f = getOmega >>= putDistribution n (amap1 f xStandard)

--------------------------------------------------------------------------------
-- prpAbHom -

-- | validity of the algebraic structure of 'AbHom'.
prpAbHom :: Statement
prpAbHom = Prp "AbHom" :<=>:
  And [ prpOrt xOrt
      , prpMlt xMlt
      , prpFbr xFbr
      , prpAdd xAdd
      , prpAbl xAbl
      ] where

  xHomTo@(XEnd xG xTo)  = xStandardOrtSite :: XOrtSite To AbHom

  xOrt = xosOrt xHomTo

  xMlt = XMlt xn xG xOrt xe xh2 xh3 where
    xn = xNB 0 10
    xe = do
      g <- xG
      h <- xAbHom 0.8 (g:>g)
      return $ Endo h
    xh2 = xMltp2 xHomTo
    xh3 = xMltp3 xHomTo

  xFbr = xOrt

  xRoot = do
    t <- xG
    h <- xTo t
    return $ orientation h

  xStalk = XStalk xRoot (xAbHom 0.8)
  xAdd = xAddStalk xStalk (xNB 0 1000)
  xAbl = XAbl xStandard xFbr xa2 where
    xa2 = xRoot >>= xStalkAdbl2 xStalk

xMltAbh :: XMlt AbHom
xMltAbh = xoMlt xN (xStandardOrtOrientation :: XOrtOrientation AbHom)

--------------------------------------------------------------------------------
-- xAbhSomeFreeSlice -
xAbhSomeFreeSlice :: N -> X (SomeFreeSlice From AbHom)
xAbhSomeFreeSlice nMax = do
  n <- xNB 0 nMax
  g <- xStandard
  h <- xAbHom 0.8 ((z1 ^ n) :> g)
  case someNatural n of
    SomeNatural sn -> return $ SomeFreeSlice (SliceFrom (Free sn) h)
  where z1 = abg 0

    
