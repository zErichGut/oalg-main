
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , GeneralizedNewtypeDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.Chain
-- Description : chains of simlices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Chains of simplices..
module OAlg.Homology.Chain
  (
{-    
    -- * Chain
    Chain, ch, chZ, boundary, chainMap

    -- * Chain Homomorphism
  , ChainHom(..), chDomainSet, chRangeSet
  , chainHomRep
-}
  ) where

import Control.Monad

import Data.Typeable

import Data.List as L (zip,(++))

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Map

import OAlg.Data.Reducible
import OAlg.Data.Constructable

import OAlg.Structure.Exception
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Oriented hiding (Path)
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Vectorial

import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Sum
import OAlg.Entity.Matrix

import OAlg.Homology.Simplical

import OAlg.Data.Symbol hiding (S)

--------------------------------------------------------------------------------
-- Chain -

-- | chains as a formal sum of simplices.
type Chain r s x = SumSymbol r (s x)

--------------------------------------------------------------------------------
-- ch -

-- | a simplex as a @__r__@-chain.
ch :: (Ring r, Commutative r, Simplical s x) => s x -> Chain r s x
ch = sy

-- | a simplces as a 'Z'-chain.
chZ :: Simplical s x => s x -> Chain Z s x
chZ = ch

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

--------------------------------------------------------------------------------
-- zeroHom -

-- | the zero homomorphism.
zeroHom :: (Ring r, Commutative r, Simplical s y)
  => Chain r s x -> Chain r s y
zeroHom = ssySum (const $ LinearCombination [])

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary operator of chains.
boundary :: (Ring r, Commutative r, Simplical s x)
  => Chain r s x -> Chain r s x
boundary = ssySum (bdr rAlt) where
  bdr :: Simplical s x => [r] -> s x -> LinearCombination r (s x)
  bdr rs s = LinearCombination (rs `zip` faces s)

--------------------------------------------------------------------------------
-- chainMap -

chainMap :: (Ring r, Commutative r, SimplicalTransformable s x y)
  => Map EntOrd x y -> Chain r s x -> Chain r s y
chainMap f = ssySum (chMap f) where
  chMap :: (Ring r, SimplicalTransformable s x y) => Map EntOrd x y -> s x -> LinearCombination r (s y)
  chMap f sx = LinearCombination [(rOne,amap1 f sx)]

f :: Map EntOrd Symbol N
f = Map ((toEnum :: Int -> N) . fromEnum)

g :: (Entity x, Ord x) => Map EntOrd x x
g = cOne Struct

--------------------------------------------------------------------------------
-- ChainOperatorAtom -

data ChainOperatorAtom r s x y where
  Boundary :: Simplical s x => ChainOperatorAtom r s (Chain r s x) (Chain r s x)
  ChainMap :: SimplicalTransformable s x y
    => Map EntOrd x y -> ChainOperatorAtom r s (Chain r s x) (Chain r s y)

instance (Ring r, Commutative r) => Morphism (ChainOperatorAtom r s) where
  type ObjectClass (ChainOperatorAtom r s) = Vec r
  homomorphous Boundary     = Struct :>: Struct
  homomorphous (ChainMap _) = Struct :>: Struct

instance (Ring r, Commutative r) => EmbeddableMorphism (ChainOperatorAtom r s) Typ
instance (Ring r, Commutative r) => EmbeddableMorphismTyp (ChainOperatorAtom r s)


instance (Ring r, Commutative r) => Applicative (ChainOperatorAtom r s) where
  amap Boundary     = boundary
  amap (ChainMap f) = chainMap f


instance (Ring r, Commutative r) => EmbeddableMorphism (ChainOperatorAtom r s) Fbr
instance (Ring r, Commutative r) => HomFibred (ChainOperatorAtom r s) where
  rmap Boundary     = const ()
  rmap (ChainMap _) = const ()

instance (Ring r, Commutative r) => EmbeddableMorphism (ChainOperatorAtom r s) Add
instance (Ring r, Commutative r) => HomAdditive (ChainOperatorAtom r s)

instance (Ring r, Commutative r) => EmbeddableMorphism (ChainOperatorAtom r s) (Vec r)
instance (Ring r, Commutative r) => HomVectorial r (ChainOperatorAtom r s)

--------------------------------------------------------------------------------
-- ChainOpreratorPath -

type ChainOperatorPath r s = Path (ChainOperatorAtom r s)

--------------------------------------------------------------------------------
-- rdcChnOprPth -

rdcChnOprPth :: ChainOperatorPath r s x y -> Rdc (ChainOperatorPath r s x y)
rdcChnOprPth o = case o of
  ChainMap f :. Boundary :. hs -> reducesTo (Boundary :. ChainMap f :. hs)
  h :. hs                      -> rdcChnOprPth hs >>= return . (h :.)
  _                            -> return o

instance Reducible (Path (ChainOperatorAtom r s) x y) where
  reduce = reduceWith rdcChnOprPth
  
--------------------------------------------------------------------------------
-- ChainOperatorRep -

newtype ChainOperatorRep r s x y
  = ChainOperatorRep (Representable r (ChainOperatorPath r s) x y)

--------------------------------------------------------------------------------
-- chorDomain -

chorDomain :: ChainOperatorRep r s (Chain r s x) (Chain r s y) -> Set (s x)
chorDomain (ChainOperatorRep (Representable _ sx _)) = sx

--------------------------------------------------------------------------------
-- chorRange -

chorRange :: ChainOperatorRep r s (Chain r s x) (Chain r s y) -> Set (s y)
chorRange (ChainOperatorRep (Representable _ _ sy)) = sy

--------------------------------------------------------------------------------
-- chorGraph - 

chorGraph :: (Ring r, Commutative r, Simplical s x)
  => ChainOperatorRep r s (Chain r s x) (Chain r s y) -> Graph (s x) (Chain r s y)
chorGraph (ChainOperatorRep (Representable o (Set sxs) _)) = Graph [(sx, amap o (ch sx)) | sx <- sxs]

--------------------------------------------------------------------------------
-- ChainOperatorRep r s - Entity -

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Show (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  show o = "ChainOperatorRep (" ++ (show $ chorGraph o) ++ ")"

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Eq (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  f == g = (chorDomain f, chorRange f, chorGraph f) == (chorDomain g, chorRange g, chorGraph g)

instance (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Ord (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  f `compare` g
    = (chorDomain f, chorRange f, chorGraph f) `compare` (chorDomain g, chorRange g, chorGraph g)

instance Ring r => Validable (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  valid (ChainOperatorRep r) = Label "ChainOperatorRep" :<=>: valid r

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Entity (ChainOperatorRep r s (Chain r s x) (Chain r s y))

--------------------------------------------------------------------------------
-- ChainOperatorRep r s - Fibred -

instance (Ring r, Commutative r, Simplical s x, Simplical s y)
  => Fibred (ChainOperatorRep r s (Chain r s x) (Chain r s y)) where
  type Root (ChainOperatorRep r s (Chain r s x) (Chain r s y)) = (Set (s x),Set (s y))
  root r = (chorDomain r, chorRange r)

--------------------------------------------------------------------------------
-- ChainOperatorSumForm -

type ChainOperatorSumForm r s x y = SumForm r (ChainOperatorRep r s x y)

-- | reduces the paths according to 'rdcChnOprPth'.
rdcChnOprSFPth :: ChainOperatorSumForm r s (Chain r s x) (Chain r s y)
  -> Rdc (ChainOperatorSumForm r s (Chain r s x) (Chain r s y))
rdcChnOprSFPth o = case o of
  Zero _ -> return o 
  S (ChainOperatorRep (Representable h sx sy))
    -> rdcChnOprPth h >>= \h' -> return $ S $ ChainOperatorRep (Representable h' sx sy)
  r :! o' -> rdcChnOprSFPth o' >>= return . (r:!)
  f :+ g  -> do
    f' <- rdcChnOprSFPth f
    g' <- rdcChnOprSFPth g
    return (f' :+ g')

-- | reduces consecutive 'Boundary' operators to zero.
--
-- pre: the paths are reduced according to 'rdcChnOprPth'.
rdcChnOprSFSum :: ChainOperatorSumForm r s (Chain r s x) (Chain r s y)
  -> Rdc (ChainOperatorSumForm r s (Chain r s x) (Chain r s y))
rdcChnOprSFSum o = case o of
  Zero _ -> return o
  S (ChainOperatorRep (Representable h sx sy)) -> case h of
    Boundary :. Boundary :. _                  -> reducesTo (Zero (sx,sy))
    _                                          -> return o
  r :! o' -> rdcChnOprSFSum o' >>= return . (r:!)
  f :+ g  -> do
    f' <- rdcChnOprSFSum f
    g' <- rdcChnOprSFSum g
    return (f' :+ g')

rdcChnOprSumForm :: ChainOperatorSumForm r s (Chain r s x) (Chain r s y)
  -> Rdc (ChainOperatorSumForm r s (Chain r s x) (Chain r s y))
rdcChnOprSumForm = rdcChnOprSFPth >>>= rdcChnOprSFSum

--------------------------------------------------------------------------------
-- ChainOperator -

data ChainOperator r s where
  ChainOperator
    :: (Simplical s x, Simplical s y)
    => Sum r (ChainOperatorRep r s (Chain r s x) (Chain r s y))
    -> ChainOperator r s

--------------------------------------------------------------------------------
-- chopr -

chopr :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => Representable r (ChainOperatorAtom r s) (Chain r s x) (Chain r s y)
  -> ChainOperator r s
chopr (Representable o sx sy)
  = ChainOperator $ make $ S $ ChainOperatorRep $ Representable (o :. IdPath (domain o)) sx sy 

--------------------------------------------------------------------------------
-- ChainOperator - Entity -

deriving instance (Ring r, Commutative r) => Show (ChainOperator r s)

eqChainOperatorTypes
  :: (Typeable x, Typeable x', Typeable y, Typeable y')
  => Sum r (ChainOperatorRep r s (Chain r s x)  (Chain r s y))
  -> Sum r (ChainOperatorRep r s (Chain r s x') (Chain r s y'))
  -> Maybe (x :~: x',y :~: y')
eqChainOperatorTypes f g = do
  eqx <- xEqT f g
  eqy <- yEqT f g
  return (eqx,eqy)
  where xEqT :: (Typeable x, Typeable x')
             => Sum r (ChainOperatorRep r s (Chain r s x)  (Chain r s y))
             -> Sum r (ChainOperatorRep r s (Chain r s x') (Chain r s y'))
             -> Maybe (x :~: x')
        xEqT _ _ = eqT

        yEqT :: (Typeable y, Typeable y')
             => Sum r (ChainOperatorRep r s (Chain r s x)  (Chain r s y))
             -> Sum r (ChainOperatorRep r s (Chain r s x') (Chain r s y'))
             -> Maybe (y :~: y')
        yEqT _ _ = eqT

instance (Ring r, Commutative r) => Eq (ChainOperator r s) where
  ChainOperator f == ChainOperator g = case eqChainOperatorTypes f g of
    Just (Refl,Refl) -> f == g
    Nothing          -> False

instance (Ring r, Commutative r) => Validable (ChainOperator r s) where
  valid (ChainOperator f) = Label "ChainOperator" :<=>: valid f

instance (Ring r, Commutative r, Typeable s) => Entity (ChainOperator r s)

--------------------------------------------------------------------------------
-- SimplexSet -

data SimplexSet s where
  SimplexSet :: Simplical s x => Set (s x) -> SimplexSet s

deriving instance Show (SimplexSet s)

eqSimplexSetType :: (Typeable x, Typeable y) => Set (s x) -> Set (s y) -> Maybe (x :~: y)
eqSimplexSetType _ _ = eqT

instance Eq (SimplexSet s) where
  SimplexSet sx == SimplexSet sy = case eqSimplexSetType sx sy of
    Just Refl -> sx == sy
    Nothing   -> False

instance Validable (SimplexSet s) where
  valid (SimplexSet sx) = Label "SimplexSet" :<=>: valid sx

instance Typeable s => Entity (SimplexSet s)

--------------------------------------------------------------------------------
-- ChainOperator - Algebraic -

instance (Ring r, Commutative r, Typeable s) => Oriented (ChainOperator r s) where
  type Point (ChainOperator r s) = SimplexSet s
  orientation (ChainOperator f) = SimplexSet sx :> SimplexSet sy where (sx,sy) = root f

instance (Ring r, Commutative r, Typeable s) => Fibred (ChainOperator r s) where
  type Root (ChainOperator r s) = Orientation (SimplexSet s)

instance (Ring r, Commutative r, Ord r, Typeable s) => Additive (ChainOperator r s) where
  zero (SimplexSet sx :> SimplexSet sy) = ChainOperator $ zero (sx,sy)
  ChainOperator f + ChainOperator g = case eqChainOperatorTypes f g of
    Just (Refl,Refl) | root f == root g -> ChainOperator (f + g)
    _                                   -> throw NotAddable

  ntimes n (ChainOperator f) = ChainOperator (ntimes n f)

instance (Ring r, Commutative r, Ord r, Typeable s) => Abelian (ChainOperator r s) where
  negate (ChainOperator f) = ChainOperator $ negate f
  ChainOperator f - ChainOperator g = case eqChainOperatorTypes f g of
    Just (Refl,Refl) | root f == root g -> ChainOperator (f - g)
    _                                   -> throw NotAddable

  ztimes z (ChainOperator f) = ChainOperator (ztimes z f)

instance (Ring r, Commutative r, Ord r, Typeable s) => Vectorial (ChainOperator r s) where
  type Scalar (ChainOperator r s) = r
  r ! ChainOperator f = ChainOperator (r!f)

eqDomRng :: (Typeable y, Typeable y')
  => Sum r (ChainOperatorRep r s (Chain r s y')  (Chain r s z))
  -> Sum r (ChainOperatorRep r s (Chain r s x)  (Chain r s y))
  -> Maybe (y :~: y')
eqDomRng _ _ = eqT


schorDom :: Sum r (ChainOperatorRep r s (Chain r s x)  (Chain r s y)) -> Set (s x)
schorDom = error "nyi"

schorRng :: Sum r (ChainOperatorRep r s (Chain r s x)  (Chain r s y)) -> Set (s y)
schorRng = error "nyi"

sfchorMlt :: SumForm r (ChainOperatorRep r s (Chain r s y)  (Chain r s z))
  -> SumForm r (ChainOperatorRep r s (Chain r s x)  (Chain r s y))
  -> SumForm r (ChainOperatorRep r s (Chain r s x)  (Chain r s z))
sfchorMlt = error "nyi"

schorMlt :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s z)
  => Sum r (ChainOperatorRep r s (Chain r s y)  (Chain r s z))
  -> Sum r (ChainOperatorRep r s (Chain r s x)  (Chain r s y))
  -> Sum r (ChainOperatorRep r s (Chain r s x)  (Chain r s z))
schorMlt f g = make $ reduceWith rdcChnOprSumForm $ (form f `sfchorMlt` form g)


  
instance (Ring r, Commutative r, Ord r, Typeable s) => Multiplicative (ChainOperator r s) where
  one (SimplexSet sx)
    = ChainOperator $ make $ S $ ChainOperatorRep $ Representable (cOne Struct) sx sx

  ChainOperator f * ChainOperator g = case eqDomRng f g of
    Just Refl | schorDom f == schorRng g -> ChainOperator (f `schorMlt` g)
    _                                    -> throw NotMultiplicable

{-
--------------------------------------------------------------------------------
-- choGraph -

choGraph :: (Ring r, Commutative r, Simplical s x)
  => Path (ChainOperatorAtom r s) (Chain r s x) (Chain r s y)
  -> Set (s x) -> Graph (s x) (Chain r s y)
choGraph o s = Graph [(sx,amap o (ch sx)) | sx <- setxs s]

--------------------------------------------------------------------------------
-- SimplexSet -

data SimplexSet s where
  SimplexSet :: (Entity x, Ord x) => Set (s x) -> SimplexSet s

--------------------------------------------------------------------------------
-- ChainHom -

data ChainHomPath r s x y where
  ChainHomPath
    :: (Simplical s x, Simplical s y)
    => Path (ChainOperatorAtom r s) (Chain r s x) (Chain r s y)
    -> Set (s x) -> Set (s y)
    -> ChainHomPath r s (Chain r s x) (Chain r s y)

instance (Ring r, Commutative r) => Show (ChainHomPath r s x y) where
  show (ChainHomPath h sx _) = "ChainHomPath (" ++ (show $ choGraph h sx) ++ ")"
instance (Ring r, Commutative r) => Show2 (ChainHomPath r s)

instance (Ring r, Commutative r) => Eq (ChainHomPath r s x y) where
  ChainHomPath h sx sy == ChainHomPath h' sx' sy' = (sx,sy,choGraph h sx) == (sx',sy',choGraph h' sx')
instance (Ring r, Commutative r) => Eq2 (ChainHomPath r s)

instance (Ring r, Commutative r) => Validable (ChainHomPath r s x y) where
  valid (ChainHomPath h sx sy) = Label "ChainHomPath" :<=>: error "nyi"

instance (Ring r, Commutative r, Typeable s, Typeable x, Typeable y) => Entity (ChainHomPath r s x y)

instance (Ring r, Commutative r, Typeable s, Simplical s x, Simplical s y)
  => Fibred (ChainHomPath r s (Chain r s x) (Chain r s y)) where
  type Root (ChainHomPath r s (Chain r s x) (Chain r s y)) = (Set (s x),Set (s y))
  root (ChainHomPath _ sx sy) = (sx,sy)
  
--------------------------------------------------------------------------------
-- AlgChainHomForm -

-- | the 'Form' for 'ChainOperatorAtom's algebra.
type AlgChainHomForm r s x y = SumForm r (ChainHomPath r s (Chain r s x) (Chain r s y))

ff :: ChainOperatorAtom r s (Chain r s y) (Chain r s z)
  -> Path (ChainOperatorAtom r s) (Chain r s x) (Chain r s y)
  -> Set (s x) -> Set (s z)
ff = error "nyi"

gg :: ChainOperatorAtom r s y (Chain r s z)
  -> AlgChainHomForm r s x y
  -> AlgChainHomForm r s x z
gg = error "nyi"

rdcAlgChHomForm :: AlgChainHomForm r s x y -> Rdc (AlgChainHomForm r s x y)
rdcAlgChHomForm h = case h of
  S (ChainHomPath (Boundary :. Boundary :. _) sx sy)
    -> reducesTo (Zero (sx,sy))
  S (ChainHomPath (ChainMap f :. Boundary :. hs) sx sy)
    -> reducesTo $ S $ ChainHomPath (Boundary :. ChainMap f :. hs) sx sy
  S (ChainHomPath (h:.hs) sx sy) -> 
    rdcAlgChHomForm (S (ChainHomPath hs sx (ff h hs sx))) >>= error "nyi" -- return . gg h
  _ -> return h
-}


  

{-
--------------------------------------------------------------------------------
-- ChainHom -

-- | homomorphism between chains.
--
-- __Property__ Let @h@ be in @'ChainHom' __r__ __s__ __x__ __y__@ where @r@ is a commutaitve ring
-- and @s@ a 'Simplical' structure, then holds:
--
-- (1) In case where @h@ matches @'Boundary' ssx ssx'@ then holds:
-- @'faces'' ssx@ is a subset of @ssx'@.
--
-- (2) In case where @h@ matches @'ChainMap' ssx ssy f@ then for all @sx@ in @ssx@ holds:
-- @'amap1' f sx@ is an element of @ssy@.
data ChainHom r s x y where
  ZeroHom :: (Simplical s x, Simplical s y)
    => Set (s x) -> Set (s y)
    -> ChainHom r s (Chain r s x) (Chain r s y)
  Boundary
    :: Simplical s x
    => Set (s x) -> Set (s x)
    -> ChainHom r s (Chain r s x) (Chain r s x)
  ChainMap
    :: SimplicalTransformable s x y
    => Set (s x) -> Set (s y) -> Map EntOrd x y
    -> ChainHom r s (Chain r s x) (Chain r s y)

--------------------------------------------------------------------------------
-- chDomainSet -

chDomainSet :: ChainHom r s (Chain r s x) (Chain r s y) -> Set (s x)
chDomainSet (ZeroHom sx _)    = sx
chDomainSet (Boundary sx _)   = sx
chDomainSet (ChainMap sx _ _) = sx

--------------------------------------------------------------------------------
-- chRangeSet -

chRangeSet :: ChainHom r s (Chain r s x) (Chain r s y) -> Set (s y)
chRangeSet (ZeroHom _ sy)    = sy
chRangeSet (Boundary _ sy)   = sy
chRangeSet (ChainMap _ sy _) = sy
--------------------------------------------------------------------------------
-- ChainHom - Hom (Vec r) -

instance (Ring r, Commutative r) => Applicative (ChainHom r s) where
  amap (ZeroHom _ _)    = zeroHom
  amap (Boundary _ _)   = boundary
  amap (ChainMap _ _ f) = chainMap f

instance Show (ChainHom r s x y) where
  show (ZeroHom sx sy)    = "ZeroHom (" ++ show sx ++ ") (" ++ show sy ++ ")"
  show (Boundary s s')    = "Boundary (" ++ show s ++ ") (" ++ show s' ++ ")"
  show (ChainMap sx sy _) = "ChainMap (" ++ show sx ++ ") (" ++ show sy ++ ")"
instance Show2 (ChainHom r s)

instance Eq (ChainHom r s x y) where
  ZeroHom sx sy == ZeroHom sx' sy' = sx == sx' && sy == sy'
  Boundary s s' == Boundary t t' = s == t && s' == t'
  ChainMap sx sy f == ChainMap sx' sy' f'
    = sx == sx' && sy == sy' && and [amap1 f s == amap1 f' s | s <- setxs sx]
  _ == _ = False
instance Eq2 (ChainHom r s)

instance Validable (ChainHom r s x y) where
  valid (ZeroHom ssx ssy) = Label "ZeroHom" :<=>: valid ssx && valid ssy
  valid (Boundary ssx ssx') = Label "Boundary" :<=>:
    And [ valid ssx
        , valid ssx'
        , Label "1" :<=>: let fs = faces' ssx in
            (fs <<= ssx') :?> Params ["fs":= show (fs // ssx')]
        ]
  valid (ChainMap ssx ssy f) = Label "ChainMap" :<=>:
    And [ valid ssx
        , valid ssy
        , Label "2" :<=>: let ssy' = amap1 (map f) ssx in
            (ssy' <<= ssy) :?> Params ["ssy'" := show (ssy' // ssy)]
        ]
    where map :: SimplicalTransformable s x y => Map EntOrd x y -> Map EntOrd (s x) (s y)
          map = Map . amap1
instance Validable2 (ChainHom r s)

instance (Typeable r, Typeable s, Typeable x, Typeable y)
  => Entity (ChainHom r s x y)

instance (Typeable r, Typeable s) => Entity2 (ChainHom r s)


instance (Ring r, Commutative r, Typeable s) => Morphism (ChainHom r s) where
  type ObjectClass (ChainHom r s) = Vec r
  homomorphous (ZeroHom _ _)    = Struct :>: Struct
  homomorphous (Boundary _ _)   = Struct :>: Struct
  homomorphous (ChainMap _ _ _) = Struct :>: Struct

instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphism (ChainHom r s) Fbr
instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphism (ChainHom r s) Typ
instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphismTyp (ChainHom r s)
instance (Ring r, Commutative r, Typeable s) => HomFibred (ChainHom r s) where
  rmap (ZeroHom _ _)    = const ()
  rmap (Boundary _ _)   = const ()
  rmap (ChainMap _ _ _) = const ()

instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphism (ChainHom r s) Add
instance (Ring r, Commutative r, Typeable s) => HomAdditive (ChainHom r s)

instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphism (ChainHom r s) (Vec r)
instance (Ring r, Commutative r, Typeable s) => HomVectorial r (ChainHom r s)

--------------------------------------------------------------------------------
-- chainHomRep -

chainHomRep
  :: (Ring r, Commutative r, Typeable s)
  => ChainHom r s (Chain r s x) (Chain r s y)
  -> Representable r (ChainHom r s) (Chain r s x) (Chain r s y)
chainHomRep h@(ZeroHom sx sy)     = Representable h sx sy
chainHomRep h@(Boundary s s')    = Representable h s s'
chainHomRep h@(ChainMap sx sy _) = Representable h sx sy

-}
