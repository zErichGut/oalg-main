
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.ConsZero
-- Description : chain diagrams with consecutive zero-able arrows. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Chain diagrams with consecutive zero-able arrows. 
module OAlg.Limes.Exact.ConsZero
  (
{-
    -- * Consecutive Zero
    ConsZero(..), cnzDiagram, cnzPoints, cnzArrows
  , cnzHead, cnzTail
  , cnzMap

    -- ** Duality
  , coConsZero, coConsZeroInv, cnzFromOpOp

    -- * Transformation
  , ConsZeroTrafo(..), cnztTrafos, cnztTransformation
  , cnztHead, cnztTail
  , cnztMap

    -- ** Duality
  , coConsZeroTrafo, coConsZeroTrafoInv, cnztFromOpOp

    -- * X
  , xSomeConsZeroTrafoOrnt, SomeConsZeroTrafo(..)
-}
  ) where

import Control.Monad
import Control.Applicative ((<|>))

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Vectorial
import OAlg.Structure.Algebraic

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Hom.Definition
import OAlg.Hom.Distributive ()

import OAlg.Entity.Slice.Definition
import OAlg.Entity.Slice.Sliced

import OAlg.Limes.Cone
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Limits

{-
data DiagramP f t n m x where
  DiagramP :: Point (f t x) ~ Point x => Diagram t n m (f t x) -> DiagramP f t n m x

class DiagrammaticProdicate f where
  ff :: f (t :: DiagramType) x -> x

instance DiagrammaticProdicate f => Diagrammatic (DiagramP f) where
  diagram (DiagramP dp) = case dp of
    DiagramChainTo p aps -> DiagramChainTo p (amap1 ff aps)
-}

data SomeSlice i t x where
  SomeSlice :: (Attestable n, Sliced (i n) x) => Slice t (i n) x -> SomeSlice i t x

ssSlice :: SomeSlice i t x -> x
ssSlice (SomeSlice s) = slice s

data SomeSliceConsZero i t n x where
  SomeSliceFromConsZero
    :: Diagram (Chain To) (n+1) n (SomeSlice i From x)
    -> SomeSliceConsZero i From n x
  SomeSliceToConsZero
    :: Diagram (Chain From) (n+1) n (SomeSlice i To x)
    -> SomeSliceConsZero i To n x
    
data SomeSliceDiagram i t n m x where
  SomeSliceFromDiagram :: SomeSlice i From x -> SomeSliceDiagram i (Parallel LeftToRight) N2 N1 x
  SomeSliceToDiagram   :: SomeSlice i To x -> SomeSliceDiagram i (Parallel RightToLeft) N2 N1 x

instance Diagrammatic (SomeSliceDiagram i) where
  diagram (SomeSliceFromDiagram (SomeSlice s)) = DiagramParallelLR l r (x:|Nil) where
    x      = slice s
    l :> r = orientation x
  diagram (SomeSliceToDiagram (SomeSlice s))   = DiagramParallelRL l r (x:|Nil) where
    x      = slice s
    r :> l = orientation x

data SomeSliceCone i s p d t n m x where
  SomeSliceFromCone :: Distributive x
    => SomeSliceConsZero i From N2 x
    -> SomeSliceCone i Dst Projective (SomeSliceDiagram i) (Parallel LeftToRight) N2 N1 x
  SomeSliceToCone :: Distributive x
    => SomeSliceConsZero i To N2 x
    -> SomeSliceCone i Dst Injective (SomeSliceDiagram i) (Parallel RightToLeft) N2 N1 x

instance Conic (SomeSliceCone i) where
  cone (SomeSliceFromCone (SomeSliceFromConsZero (DiagramChainTo _ (x:|k:|Nil))))
    = ConeKernel (SomeSliceFromDiagram x) (ssSlice k)

  cone (SomeSliceToCone (SomeSliceToConsZero (DiagramChainFrom _ (x:|c:|Nil))))
    = ConeCokernel (SomeSliceToDiagram x) (ssSlice c)

type SomeSliceKernel i  = KernelG (SomeSliceCone i) (SomeSliceDiagram i) N1
type SomeSliceKernels i = KernelsG (SomeSliceCone i) (SomeSliceDiagram i) N1

ff :: SomeSliceKernels i x -> SomeSliceDiagram i (Parallel LeftToRight) N2 N1 x -> SomeSliceKernel i x
ff = limes


{-
--------------------------------------------------------------------------------
-- ConsZero -

-- | chain diagrams with consecutive zero-able arrows.
--
-- __Properties__ Let @'Zero' c@ be in @'Zero' __t__ __n__ __d__@ for a 'Distributive' structure
-- @__d__@, then holds:
--
-- (1) If @c@ matches @'DiagramChainTo' _ ds@ then holds:
-- @d '*' d'@ is 'zero' for all @..d':|'d'..@ in @ds@.
--
-- (2) If @c@ matches @'DiagramChainFrom' _ ds@ then holds:
-- @d' '*' d@ is 'zero' for all @..d':|'d'..@ in @ds@.
newtype ConsZero t n d = ConsZero (Diagram (Chain t) (n+3) (n+2) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ConsZero - Duality -

type instance Dual (ConsZero t n d) = ConsZero (Dual t) n (Op d)

reflDualChain :: ConsZero t n d -> Dual (Chain t) :~: Chain (Dual t)
reflDualChain (ConsZero d) = case d of
  DiagramChainTo _ _   -> Refl
  DiagramChainFrom _ _ -> Refl

-- | the dual 'ConsZero'
coConsZero :: ConsZero t n d -> Dual (ConsZero t n d)
coConsZero c@(ConsZero d) = case reflDualChain c of
  Refl -> ConsZero (coDiagram d)

cnzFromOpOp :: Oriented d => ConsZero t n (Op (Op d)) -> ConsZero t n d
cnzFromOpOp (ConsZero d) = ConsZero (dgFromOpOp d)
                            
coConsZeroInv :: Oriented d => Dual (Dual t) :~: t -> Dual (ConsZero t n d) -> ConsZero t n d
coConsZeroInv Refl d' = cnzFromOpOp $ coConsZero d'

--------------------------------------------------------------------------------
-- ConsZero - Entity -

vldConsZeroTo :: Distributive d => ConsZero To n d -> Statement
vldConsZeroTo (ConsZero (DiagramChainTo e (d:|ds)))
  = And [ valid d
        , Label "e == end d" :<=>: (e == end d) :?> Params ["e":=show e, "d":=show d]
        , vldZrs 0 d ds
        ] where
  
  vldZrs :: Distributive d => N -> d -> FinList n d -> Statement
  vldZrs _ _ Nil      = SValid
  vldZrs i d (d':|ds) = And [ valid d'
                            , Label "start d == end d'"
                                :<=>: (start d == end d') :?> Params ["i":=show i]
                            , Label "1" :<=>: isZero (d*d') :?> Params ["i":=show i]
                            , vldZrs (succ i) d' ds
                            ]

instance Distributive d => Validable (ConsZero t n d) where
  valid c@(ConsZero d) = Label "ConsZero" :<=>:
    case d of
      DiagramChainTo _ _   -> vldConsZeroTo c
      DiagramChainFrom _ _ -> vldConsZeroTo $ coConsZero c

instance (Distributive d, Typeable t, Typeable n) => Entity (ConsZero t n d)

--------------------------------------------------------------------------------
-- cnzDiagram -

-- | the underlying 'Diagram'.
cnzDiagram :: ConsZero t n d -> Diagram (Chain t) (n+3) (n+2) d
cnzDiagram (ConsZero d) = d

--------------------------------------------------------------------------------
-- cnzPoints -

-- | the points of the underlying 'Diagram'.
cnzPoints :: Oriented d => ConsZero t n d -> FinList (n+3) (Point d)
cnzPoints = dgPoints . cnzDiagram

--------------------------------------------------------------------------------
-- cnzArrows -

-- | the arrows of the underlying 'Diagram'.
cnzArrows :: ConsZero t n d -> FinList (n+2) d
cnzArrows = dgArrows . cnzDiagram

--------------------------------------------------------------------------------
-- cnzHead -

-- | the two first arrows as a 'ConsZero'.
cnzHead :: Oriented d => ConsZero t n d -> ConsZero t N0 d
cnzHead (ConsZero (DiagramChainTo _ (a:|a':|_))) = ConsZero (DiagramChainTo (end a) (a:|a':|Nil))
cnzHead c@(ConsZero (DiagramChainFrom _ _))      = coConsZeroInv Refl $ cnzHead $ coConsZero c 

--------------------------------------------------------------------------------
-- cnzTail -

-- | dropping the first arrow.
cnzTail :: Oriented d => ConsZero t (n+1) d -> ConsZero t n d
cnzTail (ConsZero (DiagramChainTo _ (a:|as))) = ConsZero (DiagramChainTo (start a) as)
cnzTail c@(ConsZero (DiagramChainFrom _ _))   = coConsZeroInv Refl $ cnzTail $ coConsZero c

--------------------------------------------------------------------------------
-- cnzMap -

-- | mapping for 'ConsZero's.
cnzMap :: Hom Dst h => h a b -> ConsZero t n a -> ConsZero t n b
cnzMap h (ConsZero as) = ConsZero $ dgMap h as

--------------------------------------------------------------------------------
-- ConsZeroTrafo -

-- | transformation between two 'ConsZero'.
--
-- __Properties__ Let @t = 'ZeroTrafo' a b fs@ be in @'ConsZeroTrafo' __t__ __n__ __d__@ for a
-- 'Distributive' structure @__d__@, then holds:
--
-- (1) If @a@ matches @'ConsZero' ('DiagramChainTo' _ as)@, then holds:
-- @f '*' a '==' b '*' f'@ for all @f@, @a@ and @b@ in
--
-- @
--                a       
--  as: ...    <------ <------   ...
--            |       |       |
--  fs: ... f |     f'|       |  ...
--            v       v       v
--  bs: ...    <------ <------   ... 
--                b       
-- @
--
-- (2) If @a@ matches @'ConsZero' ('DiagramChainFrom' _ as)@, then holds:
-- @f' '*' a '==' b '*' f@ for all @f@, @a@ and @b@ in
--
-- @
--                a       
--  as: ...    ------> ------>   ...
--            |       |       |
--  fs: ... f |     f'|       |  ...
--            v       v       v
--  bs: ...    ------> ------>   ... 
--                b       
-- @
data ConsZeroTrafo t n d = ConsZeroTrafo (ConsZero t n d) (ConsZero t n d) (FinList (n+3) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- cnztTrafos -

-- | the transformations.
cnztTrafos :: ConsZeroTrafo t n d -> FinList (n+3) d
cnztTrafos (ConsZeroTrafo _ _ fs) = fs

--------------------------------------------------------------------------------
-- cnztTransformation -

-- | the underlying 'Transformation'.
cnztTransformation :: ConsZeroTrafo t n d -> Transformation (Chain t) (n+3) (n+2) d
cnztTransformation (ConsZeroTrafo a b fs) = Transformation (cnzDiagram a) (cnzDiagram b) fs

--------------------------------------------------------------------------------
-- coConsZeroTrafo - Duality -

type instance Dual (ConsZeroTrafo t n d) = ConsZeroTrafo (Dual t) n (Op d)

-- | the dual 'ConsZeroTrafo'.
coConsZeroTrafo :: ConsZeroTrafo t n d -> Dual (ConsZeroTrafo t n d)
coConsZeroTrafo (ConsZeroTrafo a b fs) = ConsZeroTrafo (coConsZero b) (coConsZero a) (amap1 Op fs)

coConsZeroTrafoInv :: Oriented d
  => Dual (Dual t) :~: t -> Dual (ConsZeroTrafo t n d) -> ConsZeroTrafo t n d
coConsZeroTrafoInv Refl t = cnztFromOpOp $ coConsZeroTrafo t

cnztFromOpOp :: Oriented d => ConsZeroTrafo t n (Op (Op d)) -> ConsZeroTrafo t n d
cnztFromOpOp (ConsZeroTrafo a b fs) = ConsZeroTrafo a' b' fs' where
  a' = cnzFromOpOp a
  b' = cnzFromOpOp b
  fs' = amap1 fromOpOp fs

--------------------------------------------------------------------------------
-- vldConsZeroTrafoTo - Entity -

vldConsZeroTrafoTo :: Distributive d => ConsZeroTrafo To n d -> Statement
vldConsZeroTrafoTo (ConsZeroTrafo a@(ConsZero (DiagramChainTo _ as)) b@(ConsZero (DiagramChainTo _ bs)) (f:|fs))
  = And [ valid a
        , valid b
        , valid f
        , vldTrfs 0 f fs as bs 
        ] where

  vldTrfs :: Distributive d => N -> d -> FinList n d -> FinList n d -> FinList n d -> Statement
  vldTrfs _ _ Nil Nil Nil = SValid
  vldTrfs i f (f':|fs) (a:|as) (b:|bs)
    = And [ valid f'
          , Label "f * a" :<=>: (end a == start f) :?> Params ["i":=show i]
          , Label "b * f'" :<=>: (end f' == start b) :?> Params ["i":=show i]
          , Label "1" :<=>: (f * a == b * f') :?> Params ["i":=show i]
          , vldTrfs (succ i) f' fs as bs
          ]

instance Distributive d => Validable (ConsZeroTrafo t n d) where
  valid t@(ConsZeroTrafo a _ _) = Label "ConsZeroTrafo" :<=>: case a of
    ConsZero (DiagramChainTo _ _)   -> vldConsZeroTrafoTo t
    ConsZero (DiagramChainFrom _ _) -> vldConsZeroTrafoTo $ coConsZeroTrafo t

instance (Distributive d, Typeable t, Typeable n) => Entity (ConsZeroTrafo t n d)

--------------------------------------------------------------------------------
-- ConsZeroTrafo - Algebraic -

instance (Distributive d, Typeable t, Typeable n) => Oriented (ConsZeroTrafo t n d) where
  type Point (ConsZeroTrafo t n d) = ConsZero t n d
  orientation (ConsZeroTrafo a b _) = a :> b

instance (Distributive d, Typeable t, Typeable n) => Multiplicative (ConsZeroTrafo t n d) where
  one c = ConsZeroTrafo c c $ amap1 one $ cnzPoints c

  ConsZeroTrafo y' z f * ConsZeroTrafo x y g
    | y == y'   = ConsZeroTrafo x z $ amap1 (uncurry (*)) (f `zip` g)
    | otherwise = throw NotMultiplicable 

instance (Distributive d, Typeable t, Typeable n) => Fibred (ConsZeroTrafo t n d) where
  type Root (ConsZeroTrafo t n d) = Orientation (ConsZero t n d)

instance (Distributive d, Typeable t, Typeable n) => FibredOriented (ConsZeroTrafo t n d)

instance (Distributive d, Typeable t, Typeable n) => Additive (ConsZeroTrafo t n d) where
  zero (a :> b) = ConsZeroTrafo a b $ amap1 (zero . uncurry (:>)) (cnzPoints a `zip` cnzPoints b)

  ConsZeroTrafo a b f + ConsZeroTrafo a' b' g
    | a == a' && b == b' = ConsZeroTrafo a b $ amap1 (uncurry (+)) (f `zip` g)
    | otherwise          = throw NotAddable

instance (Distributive d, Abelian d, Typeable t, Typeable n) => Abelian (ConsZeroTrafo t n d) where
  negate (ConsZeroTrafo a b f) = ConsZeroTrafo a b $ amap1 negate f

  ConsZeroTrafo a b f - ConsZeroTrafo a' b' g
    | a == a' && b == b' = ConsZeroTrafo a b $ amap1 (uncurry (-)) (f `zip` g)
    | otherwise          = throw NotAddable
  
instance (Distributive d, Typeable t, Typeable n) => Distributive (ConsZeroTrafo t n d)

instance (Algebraic d, Typeable t, Typeable n) => Vectorial (ConsZeroTrafo t n d) where
  type Scalar (ConsZeroTrafo t n d) = Scalar d
  x ! ConsZeroTrafo a b f = ConsZeroTrafo a b $ amap1 (x!) f

instance (Algebraic d, Typeable t, Typeable n) => Algebraic (ConsZeroTrafo t n d)
  
--------------------------------------------------------------------------------
-- cnztHead -

-- | the first two arrows of the given 'ConsZeroTrafo'.
cnztHead :: Oriented d => ConsZeroTrafo t n d -> ConsZeroTrafo t N0 d
cnztHead (ConsZeroTrafo a b (f0:|f1:|f2:|_)) = ConsZeroTrafo (cnzHead a) (cnzHead b) (f0:|f1:|f2:|Nil)

--------------------------------------------------------------------------------
-- cnztTail -

-- | dropping the first arrow.
cnztTail :: Oriented d => ConsZeroTrafo t (n+1) d -> ConsZeroTrafo t n d
cnztTail (ConsZeroTrafo a b fs) = ConsZeroTrafo (cnzTail a) (cnzTail b) (tail fs)

--------------------------------------------------------------------------------
-- cnztMap -

-- mapping of 'ConsZeroTrafo's.
cnztMap :: Hom Dst h => h a b -> ConsZeroTrafo t n a -> ConsZeroTrafo t n b
cnztMap h (ConsZeroTrafo a b fs) = ConsZeroTrafo a' b' fs' where
  a'  = cnzMap h a
  b'  = cnzMap h b
  fs' = amap1 (amap h) fs
  
--------------------------------------------------------------------------------
-- SomeConsZeroTrafo -

-- | some 'ConsZeroTrafo'.
data SomeConsZeroTrafo d where
  SomeConsZeroTrafo :: (Typeable t, Typeable n) => ConsZeroTrafo t n d -> SomeConsZeroTrafo d

instance Distributive d => Validable (SomeConsZeroTrafo d) where
  valid (SomeConsZeroTrafo t) = Label "SomeConsZeroTrafo" :<=>: valid t
  
--------------------------------------------------------------------------------
-- xSomeConsZeroTrafoOrnt -

-- | random variable for @'ConsZeroTrafo' __t__ __n__ 'OS'@ with a maximal @__n__@ of the given one.
xSomeConsZeroTrafoOrnt :: N -> X (SomeConsZeroTrafo OS)
xSomeConsZeroTrafoOrnt n = xscnztTo n <|> xscnztFrom n where

  xTo :: Any n -> X (Diagram (Chain To) (n+3) (n+2) OS)
  xTo n = xDiagram Refl $ XDiagramChainTo (SW $ SW n) xStandardOrtSite
  
  xFrom :: Any n -> X (Diagram (Chain From) (n+3) (n+2) OS)
  xFrom n = xDiagram Refl $ XDiagramChainFrom (SW $ SW n) xStandardOrtSite
  
  xcnztTo :: Any n -> X (ConsZeroTrafo To n OS)
  xcnztTo n = do
    a <- amap1 ConsZero $ xTo n
    b <- amap1 ConsZero $ xTo n
    return $ ConsZeroTrafo a b $ amap1 (uncurry (:>)) $ (cnzPoints a `zip` cnzPoints b) 
  
  xcnztFrom :: Any n -> X (ConsZeroTrafo From n OS)
  xcnztFrom n = do
    a <- amap1 ConsZero $ xFrom n
    b <- amap1 ConsZero $ xFrom n
    return $ ConsZeroTrafo a b $ amap1 (uncurry (:>)) $ (cnzPoints a `zip` cnzPoints b) 
  
  xscnztTo :: N -> X (SomeConsZeroTrafo OS)
  xscnztTo n = do
    SomeNatural n' <- amap1 someNatural $ xNB 0 n
    t              <- xcnztTo n'
    return $ SomeConsZeroTrafo t

  xscnztFrom :: N -> X (SomeConsZeroTrafo OS)
  xscnztFrom n = do
    SomeNatural n' <- amap1 someNatural $ xNB 0 n
    t              <- xcnztFrom n'
    return $ SomeConsZeroTrafo t
  
-}
