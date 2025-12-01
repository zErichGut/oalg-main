
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Homology.ChainComplex
-- Description : definition of a chain complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'ChainComplex'.
module OAlg.Homology.ChainComplex
  (
    -- * Chain Complex
    chainComplex, chainComplexZ
  , chainComplexSet
  , ChainComplex(..), ChainComplexType(..)
  , ccxConsecutiveZero
  , ccxHead, ccxTail
  , ccxCards, ccxSmplSet

    -- * Chain Complex Hom
  , chainComplexHom, ChainComplexHom(..)
  , ccxConsecutiveZeroHom
  , ccxCardsHom
  ) where

import Control.Monad

import Data.Typeable
import Data.List as L (repeat,(++),zip) 

import OAlg.Prelude

-- import OAlg.Category.Map

import OAlg.Data.Filterable
import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Vectorial
import OAlg.Structure.Algebraic

import OAlg.Entity.Diagram as D
import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F 
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Matrix hiding (Transformation(..))

import OAlg.Limes.Exact.ConsecutiveZero

import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator as C
import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- toFinList3 -

-- | maps a infinite list to a finite list of @__n__ + 3@.
toFinList3 :: Any n -> [x] -> FinList (n+3) x
toFinList3 W0 (x:x':x'':_) = x:|x':|x'':|Nil
toFinList3 (SW n) (x:xs)   = x :| toFinList3 n xs
toFinList3 _ _             = throw $ ImplementationError "toFinList3"

--------------------------------------------------------------------------------
-- ccxSimplices -

-- | sequence of sets of simplices over the given complex.
--
-- __Property__ Let @n@ be in @'Any' __n__@ and @c@ in @'Complex' __x__@, then holds:
--
--  (1) For all @(z,ssx)@ in @'ccxSimplices' n c@ and @s@ in @ssx@ holds:
--
--    (1) @'dimension' s '==' z@ 
--
--    (2) @s@ is in @ssx@ iff @'vertices' s@ is in @c@.
ccxSimplices :: Simplical s x => Any n -> Complex x -> FinList (n+3) (Z,Set (s x))
ccxSimplices n c = case mSet (ccs n c) of
  (Just Refl,_) -> ccsSet n c -- more economic and faster
  (Nothing,s)   -> s
  where

    mSet :: Typeable s => FinList n (Z,Set (s x)) -> (Maybe (s :~: Set),FinList n (Z,Set (s x)))
    mSet s = (eqT,s)
  
    ccsSet :: Ord x => Any n -> Complex x -> FinList (n+3) (Z,Set (Set x))
    ccsSet n c = toFinList3 n ([-1..] `L.zip` ssx) where
      ssx = (amap1 snd $ gphxs $ cpxSimplices c) L.++ L.repeat empty
  
    ccs :: Simplical s x => Any n -> Complex x -> FinList (n+3) (Z,Set (s x))
    ccs n c = toFinList3 n ([-1..] `L.zip` ssx) where
      ssx = amap1 (filter (elg c))
          $ ((amap1 snd $ gphxs $ simplices $ cpxVertices c) L.++ L.repeat empty)
  
      elg :: Simplical s x => Complex x -> s x -> Bool
      elg c = cpxElem c . vertices

ccxSimplices' :: (Entity x, Ord x)
  => SimplexType s -> Any n -> Complex x -> FinList (n+3) (Z,Set (s x))
ccxSimplices' s n c = case structSmpl s c of Struct -> ccxSimplices n c

--------------------------------------------------------------------------------
-- ChainComplex -

-- | chain complex of dimension @__n__@ over a @'Ring' __r__@.
--
-- __Properties__ Let @v'ChainComplex' c sx@ be in @t'ChainComplex __r n__@, then holds:
--
-- (1) @'lengthN' d '==' 'lengthN' s@ for all @(d,s)@ in @('dgPoints' $ 'cnzDiagram' c) `zip` sx@.
data ChainComplex r n where
  ChainComplex :: (Entity s, Ord s)
    => ConsecutiveZero To n (Matrix r) -> FinList (n+3) (Set s) -> ChainComplex r n

deriving instance Oriented r => Show (ChainComplex r n)

eqSmplSet :: (Typeable s, Typeable s') => f s -> f s' -> Maybe (s :~: s')
eqSmplSet _ _ = eqT

instance Oriented r =>  Eq (ChainComplex r n) where
  ChainComplex c s == ChainComplex c' s' = c == c' && case eqSmplSet s s' of
    Just Refl -> s == s'
    Nothing   -> False

instance Ring r => Validable (ChainComplex r n) where
  valid (ChainComplex c sx) = Label "ChainComplex" :<=>:
    And [ valid c
        , valid sx
        , vldDims 0 (amap1 lengthN $ dgPoints $ cnzDiagram c) (amap1 lengthN sx)
        ]

    where
      vldDims :: N -> FinList n N -> FinList n N -> Statement
      vldDims _ Nil _           = SValid
      vldDims i (d:|ds) (c:|cs) = And [ (d == c) :?> Params ["i":=show i,"d":=show d,"c":=show c]
                                      , vldDims (succ i) ds cs
                                      ]

--------------------------------------------------------------------------------
-- ccxSmplSet -

ccxSmplSet :: Struct (Smpl s) x -> ChainComplex r n -> Maybe (FinList (n+3) (Set (s x)))
ccxSmplSet s (ChainComplex _ ssx) = case eqS s ssx of
  Just Refl -> return ssx
  Nothing   -> Nothing
  
  where eqS :: Typeable s' => Struct (Smpl s) x -> f (Set s') -> Maybe (s' :~: s x)
        eqS Struct _ = eqT

--------------------------------------------------------------------------------
-- ccxCards -

ccxCards :: Ring r => ChainComplex r n -> Cards n
ccxCards (ChainComplex c _) = DiagramDiscrete $ amap1 lengthN $ dgPoints $ cnzDiagram c

--------------------------------------------------------------------------------
-- ChainComplexType -

data ChainComplexType = ChainComplexStandard | ChainComplexExtended
  deriving (Show,Eq,Ord,Enum,Bounded)

--------------------------------------------------------------------------------
-- chainComplex -

chainComplex :: (Ring r, Commutative r, Entity x, Ord x)
  => ChainComplexType -> SimplexType s -> Any n -> Complex x -> ChainComplex r n
chainComplex t s n c = case structSmpl s c of
  str@Struct -> adpt t $ ChainComplex cnz ssx where
    ssx = chns str n c
    ds  = bnds ssx
    cnz = ConsecutiveZero $ DiagramChainTo (end $ head ds) ds

  where
    chns :: Struct (Smpl s) x -> Any n -> Complex x -> FinList (n+3) (Set (s x))
    chns Struct n c = amap1 snd $ ccxSimplices n c

    bnds :: (Ring r, Commutative r, Simplical s x) => FinList (n+1) (Set (s x)) -> FinList n (Matrix r)
    bnds (_:|Nil)       = Nil
    bnds (sx':|sx:|sxs) = d :| bnds (sx:|sxs) where d = repMatrix (Representable Boundary sx sx')
    -- Representable Boundary sx' sx is valid, because of the construction of sx' and sx via
    -- ccxSimplex and the property (3) of Complex and (5) of Simplical.

    adpt :: Ring r => ChainComplexType -> ChainComplex r n -> ChainComplex r n
    adpt ChainComplexExtended c                      = c
    adpt ChainComplexStandard (ChainComplex cnz ssx) = ChainComplex cnz' ssx' where
      ssx' = empty :| tail ssx
      cnz' = ConsecutiveZero (DiagramChainTo (end d0') ds') where
        DiagramChainTo _ (d0:|ds) = cnzDiagram cnz
        d0' = zero (start d0 :> one unit)
        ds' = d0' :| ds
      
chainComplexZ :: (Entity x, Ord x)
  => ChainComplexType -> SimplexType s -> Any n -> Complex x -> ChainComplex Z n
chainComplexZ = chainComplex

--------------------------------------------------------------------------------
-- ccxConsecutiveZero -

-- | the underlying consecutive zero
ccxConsecutiveZero :: ChainComplex r n -> ConsecutiveZero To n (Matrix r)
ccxConsecutiveZero (ChainComplex c _) = c

--------------------------------------------------------------------------------
-- ccxHead -

ccxHead :: Ring r => ChainComplex r n -> ChainComplex r N0
ccxHead (ChainComplex c (s0:|s1:|s2:|_)) = ChainComplex (cnzHead c) (s0:|s1:|s2:|Nil)

--------------------------------------------------------------------------------
-- ccxTail -

ccxTail :: Ring r => ChainComplex r (n+1) -> ChainComplex r n
ccxTail (ChainComplex c ssx) = ChainComplex (cnzTail c) (tail ssx)

--------------------------------------------------------------------------------
-- ChainComplexHom -

data ChainComplexHom r n
  = ChainComplexHom (ChainComplex r n) (ChainComplex r n) (FinList (n+3) (Matrix r))
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ccxConsecutiveZeroHom -

-- | the underlying homomorphism between consecutive zeros.
ccxConsecutiveZeroHom :: ChainComplexHom r n -> ConsecutiveZeroHom To n (Matrix r)
ccxConsecutiveZeroHom (ChainComplexHom a b fs)
  = ConsecutiveZeroHom $ DiagramTrafo a' b' fs where
  a' = cnzDiagram $ ccxConsecutiveZero a
  b' = cnzDiagram $ ccxConsecutiveZero b

instance (Ring r, Attestable n) => Validable (ChainComplexHom r n) where
  valid h@(ChainComplexHom a b _) = Label "ChainComplexHom" :<=>:
    And [ valid a
        , valid b
        , valid $ ccxConsecutiveZeroHom h
        ]

--------------------------------------------------------------------------------
-- chainComplexHom -

chainComplexHom :: (Ring r, Commutative r, Entity x, Ord x, Entity y, Ord y)
  => ChainComplexType -> Any n -> ComplexMap s (Complex x) (Complex y)
  -> ChainComplexHom r n
chainComplexHom t n f = let h = cpmSmplTrfType f in case structSmplTrf h f of
  Struct2 -> ChainComplexHom a b fs where
    s  = injSmplTrfType h
    sx = structSmpl s (cpmDomain f)
    sy = structSmpl s (cpmRange f)
    
    a  = chainComplex t s n (cpmDomain f)
    b  = chainComplex t s n (cpmRange f)
    fs = amap1 (uncurry (rep f))
           ((fromJust $ ccxSmplSet sx a) `F.zip` (fromJust $ ccxSmplSet sy b))
  
    rep :: (Ring r, Commutative r, SimplicalTransformable s x y)
      => ComplexMap s (Complex x) (Complex y)
      -> Set (s x) -> Set (s y) -> Matrix r
    rep f sx sy = repMatrix (Representable (ChainMap $ cpmMap f) sx sy)
  
chainComplexHomZ :: (Entity x, Ord x, Entity y, Ord y)
  => ChainComplexType -> Any n -> ComplexMap s (Complex x) (Complex y)
  -> ChainComplexHom Z n
chainComplexHomZ = chainComplexHom

--------------------------------------------------------------------------------
-- ccxCardsHom -

ccxCardsHom :: Ring r => ChainComplexHom r n -> CardsHom n
ccxCardsHom (ChainComplexHom a b _) = DiagramTrafo ca cb cs where
  ca = ccxCards a
  cb = ccxCards b
  cs = amap1 (uncurry (:>)) (dgPoints ca `F.zip` dgPoints cb)

--------------------------------------------------------------------------------
-- chainComplexSet -

-- | embedding of the set-simplices.
chainComplexSet :: (Ring r, Commutative r, Entity x, Ord x)
  => ChainComplexType -> SimplexType s -> Any n -> Complex x -> ChainComplexHom r n
chainComplexSet t s n c = ChainComplexHom ccSet cc fs where
  sxSet = structSmpl SpxTypeSet c
  sx    = structSmpl s c
  ccSet = chainComplex t SpxTypeSet n c
  cc    = chainComplex t s n c
  fs    = amap1 (uncurry (rep sxSet sx))
          ( (fromJust $ ccxSmplSet sxSet ccSet)
          `F.zip`
            (fromJust $ ccxSmplSet sx cc)
          )

  rep :: (Ring r, Commutative r)
    => Struct (Smpl Set) x -> Struct (Smpl s) x -> Set (Set x) -> Set (s x) -> Matrix r
  rep Struct Struct sxSet sx = repMatrix (Representable Simplex sxSet sx)

chainComplexSetZ :: (Entity x, Ord x)
  => ChainComplexType -> SimplexType s -> Any n -> Complex x -> ChainComplexHom Z n
chainComplexSetZ = chainComplexSet

--------------------------------------------------------------------------------
-- Algebraic -

type instance Point (ChainComplexHom r n) = ChainComplex r n

instance Oriented r => ShowPoint (ChainComplexHom r n)
instance Oriented r => EqPoint (ChainComplexHom r n)
instance Ring r => ValidablePoint (ChainComplexHom r n)
instance (Typeable r, Typeable n) => TypeablePoint (ChainComplexHom r n)


instance (Ring r, Attestable n) => Oriented (ChainComplexHom r n) where
  orientation (ChainComplexHom a b _) = a :> b

instance (Ring r, Attestable n) => Multiplicative (ChainComplexHom r n) where
  one c = ChainComplexHom c c (amap1 one $ dgPoints $ cnzDiagram $ ccxConsecutiveZero c)

  ChainComplexHom b' c fs * ChainComplexHom a b gs
    | b' == b = ChainComplexHom a c (amap1 (uncurry (*)) (fs `F.zip` gs))
    | otherwise = throw NotMultiplicable

type instance Root (ChainComplexHom r n) = Orientation (ChainComplex r n)

instance Oriented r => ShowRoot (ChainComplexHom r n)
instance Oriented r => EqRoot (ChainComplexHom r n)
instance Ring r => ValidableRoot (ChainComplexHom r n)
instance (Typeable r, Typeable n) => TypeableRoot (ChainComplexHom r n)


instance (Ring r, Attestable n) => Fibred (ChainComplexHom r n)

instance (Ring r, Attestable n) => Additive (ChainComplexHom r n) where
  zero (a :> b) = ChainComplexHom a b zs where
    zs = amap1 (zero . (uncurry (:>)))
         ( (dgPoints $ cnzDiagram $ ccxConsecutiveZero a)
         `F.zip`
           (dgPoints $ cnzDiagram $ ccxConsecutiveZero b)
         )

  ChainComplexHom a b fs + ChainComplexHom a' b' gs
    | (a,b) == (a',b') = ChainComplexHom a b (amap1 (uncurry (+)) (fs `F.zip` gs))
    | otherwise        = throw NotAddable

instance (Ring r, Attestable n) => Abelian (ChainComplexHom r n) where
  negate (ChainComplexHom a b fs) = ChainComplexHom a b (amap1 negate fs)

  ChainComplexHom a b fs - ChainComplexHom a' b' gs
    | (a,b) == (a',b') = ChainComplexHom a b (amap1 (uncurry (-)) (fs `F.zip` gs))
    | otherwise        = throw NotAddable
instance (Ring r, AlgebraicSemiring r, Attestable n)
  => Vectorial (ChainComplexHom r n) where
  type Scalar (ChainComplexHom r n) = r
  r ! (ChainComplexHom a b fs) = ChainComplexHom a b (amap1 (r!) fs) 

instance (Ring r, Attestable n) => FibredOriented (ChainComplexHom r n)

instance (Ring r, Attestable n) => Distributive (ChainComplexHom r n) where

instance ( Ring r, AlgebraicSemiring r, Attestable n)
  => Algebraic (ChainComplexHom r n)

--------------------------------------------------------------------------------
-- examples
{-
n = attest :: Any N4
a = complex [Set "ab",Set "bc",Set "cd"]
b = complex [Set[0,1],Set[1,2],Set[0,2],Set[1,2,3]] :: Complex N

t = ChainComplexExtended
cmf = ComplexMapPrs a b (Map f)
cmfHom = chainComplexHomZ t n cmf

f c = case c of
  'a' -> 0
  'b' -> 1
  'c' -> 2
  'd' -> 0
  _   -> error "undefined"


-- ab = complex [set [(0,0),(0,1),(1,1)], set [(0,0),(1,0),(1,1)]] :: Complex (N,N)
ab = cpxProductAsc l (cpxProductAsc l l)
l  = complex [set [0,1]] :: Complex N

p1 = ComplexMapPrs ab l (Map fst)
p2 = ComplexMapPrs ab (cpxProductAsc l l) (Map snd)
-}
