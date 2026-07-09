
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, TupleSections #-}

-- |
-- Module      : OAlg.Topology.Limes.ProductsAndSums
-- Description : product and disjoint union space.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Product and disjoint union space.
module OAlg.Topology.Limes.ProductsAndSums
  (
    -- * Products
    cntProductsAsc, (<*>)

    -- * Sums
  , cntSums
  ) where

import Control.Monad as M

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Either
import OAlg.Data.Filterable

import OAlg.Structure.Additive
import OAlg.Structure.PartiallyOrdered

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.ProductsAndSums

import OAlg.Homology.Simplical hiding (simplex,dimension)
import OAlg.Homology.Complex hiding (cpxProduct, cpxProductAsc)

import OAlg.Topology.Definition
import OAlg.Topology.Limes.TerminalAndInitialSpace


--------------------------------------------------------------------------------
-- cpxProductAsc -

-- | product for complex within @'ComplexMap' 'Asc'@.
--
-- __Property__ Let @ab = 'cpxProductAsc' a b@, then holds:
--
-- (1) @'ComplexMapPrs' ab a ('Map' fst)@ and @'CompelxMapPrs' ab b ('Map' snd')@ are 'valid'.
cpxProductAsc :: (Entity x, Ord x, Entity y, Ord y)
  => Complex x -> Complex y
  -> ( Complex (x,y)
     , ComplexMap Asc (Complex (x,y)) (Complex x)
     , ComplexMap Asc (Complex (x,y)) (Complex y)
     )
cpxProductAsc a b = (ab,mFst,mSnd) where
-- more efficient then OAlg.Homology.Complex.cpxProductAsc
  s    = SpxTypeAsc
  ab   = Complex $ Graph $ gph xy0 (elg a b) (-1) (Set [empty])
  mFst = ComplexMap s ab a (Map fst)
  mSnd = ComplexMap s ab b (Map snd)


  xs  = cpxVertices a
  ys  = cpxVertices b
  dx  = cpxDim a
  dy  = cpxDim b
  dxy = dx + dy
  xy0 = Set [(x,y) | x <- setxs xs, y <- setxs ys]

  map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
  map = Map

  elg :: (Entity x, Ord x, Entity y, Ord y)
    => Complex x -> Complex y -> Set (x,y) -> Bool
  elg a b = (cpxElem a . amap1 (map fst)) && (cpxElem b . amap1 (map snd))

  -- pre: for all xy in xys hilds:
  --        - dimension xy == d.
  --        - elg xy is True.
  gph :: (Ord x, Ord y)
    => Set (x,y) -> (Set (x,y) -> Bool) -> Z -> Set (Set (x,y)) -> [(Z,Set (Set (x,y)))]
  gph xy0 elg d xys = (d,xys) : if d < dxy then gph xy0 elg d' xys' else [] where
    d'   = succ d
    xys' = Set
         $ filter elg
         $ [Set (xy:xys'') | xy <- setxs xy0, Set xys'' <- setxs xys, xy << xys'']

  (<<) :: (Ord x, Ord y) => (x,y) -> [(x,y)] -> Bool
  _ << []                     = True
  xy@(x,y) << (xy'@(x',y'):_) = x <= x' && y <= y' && xy /= xy'

--------------------------------------------------------------------------------
-- cntProduct2Asc -

cntProduct2Asc :: Diagram Discrete N2 N0 (Continuous Asc)
  -> Product N2 (Continuous Asc)
cntProduct2Asc d@(DiagramDiscrete (Space a:|Space b:|Nil))
  = LimesProjective abCn (abUn ab) where
  
  (ab,mFst,mSnd) = cpxProductAsc a b

  abCn = ConeProjective d (Space ab) (Continuous mFst:|Continuous mSnd:|Nil)

  abUn :: (Entity x, Ord x, Entity y, Ord y)
    => Complex (x,y) -> ProductCone N2 (Continuous Asc)
    -> Continuous Asc
  abUn ab (ConeProjective _ (Space t)  (Continuous f:|Continuous g:|Nil))
    = case elg ab t f g of
      Nothing                    -> throw $ NotEligibleCone
      Just (Refl,Refl,Refl,Refl) -> Continuous fg where
        fg = ComplexMap s t ab (Map (\t -> (f' t, g' t)))
        ComplexMap s _ _ (Map f') = f
        ComplexMap _ _ _ (Map g') = g
        
  elg ::
    (Typeable x, Typeable y, Typeable t)
    => Complex (x,y)
    -> Complex t
    -> ComplexMap Asc (Complex tF) (Complex x')
    -> ComplexMap Asc (Complex tS) (Complex y')
    -> Maybe (t :~: tF,t :~: tS,x :~: x', y :~: y')
  elg ab t f g = do
    tF <- tFEq t f
    tS <- tFEq t g
    xF <- xFEq ab f
    yS <- ySEq ab g
    return (tF,tS,xF,yS)
    
    where
      tFEq :: Typeable t
        => Complex t -> ComplexMap s (Complex tF) c
        -> Maybe (t :~: tF)
      tFEq _ (ComplexMap _ _ _ f) = case tauTyp $ domain f of Struct -> eqT

      xFEq :: Typeable x
        => Complex (x,y) -> ComplexMap s (Complex tF) (Complex xF)
        -> Maybe (x :~: xF)
      xFEq _ (ComplexMap _ _ _ f) = case tauTyp $ range f of Struct -> eqT 

      ySEq :: Typeable y
        => Complex (x,y) -> ComplexMap s (Complex tS) (Complex yS)
        -> Maybe (y :~: yS)
      ySEq _ (ComplexMap _ _ _ g) = case tauTyp $ range g of Struct -> eqT

--------------------------------------------------------------------------------
-- cntProducts2Asc -

cntProducts2Asc :: Products N2 (Continuous Asc)
cntProducts2Asc = LimitsG cntProduct2Asc

--------------------------------------------------------------------------------
-- cntProductsAsc -

cntProductsAsc :: Products n (Continuous Asc)
cntProductsAsc = products (products0 spcTerminalAsc) cntProducts2Asc

--------------------------------------------------------------------------------
-- <*> -

infixr 7 <*>
  
(<*>) :: Space -> Space -> Space
a <*> b = tip $ universalCone $ limes cntProductsAsc ab where
  ab = DiagramDiscrete (a :| b :| Nil) :: Diagram Discrete N2 N0 (Continuous Asc)

--------------------------------------------------------------------------------
-- cpxSum2 -

cpxSum2 :: (Entity x, Ord x, Entity y, Ord y, AttestableSimplexType s)
  => Complex x -> Complex y
  -> ( Complex (Either x y)
     , ComplexMap s (Complex x) (Complex (Either x y))
     , ComplexMap s (Complex y) (Complex (Either x y))
     )
cpxSum2 a@(Complex ssx) b@(Complex ssy) = (ab, mFst, mSnd) where
  s    = simplexType
  ab   = Complex (amap1 left ssx || amap1 right ssy)
  mFst = ComplexMap s a ab (Map Left)
  mSnd = ComplexMap s b ab (Map Right)

  left :: Set (Set x) -> Set (Set (Either x y))
  left (Set sx) = Set $ amap1 (\(Set xs) -> Set (amap1 Left xs)) sx

  right :: Set (Set y) -> Set (Set (Either x y))
  right (Set sy) = Set $ amap1 (\(Set ys) -> Set (amap1 Right ys)) sy

--------------------------------------------------------------------------------
-- cntSum2 -

cntSum2 :: AttestableSimplexType s
  => Diagram Discrete N2 N0 (Continuous s)
  -> Sum N2 (Continuous s)
cntSum2 d@(DiagramDiscrete (Space a:|Space b:|Nil))
  = LimesInjective abCn (abUn simplexType ab) where
  (ab,mFst,mSnd) = cpxSum2 a b
  
  abCn = ConeInjective d (Space ab) (Continuous mFst:|Continuous mSnd:|Nil)

  abUn :: (Entity x, Ord x, Entity y, Ord y)
    => SimplexType s -> Complex (Either x y) -> SumCone N2 (Continuous s)
    -> Continuous s
  abUn s ab (ConeInjective _ (Space t)  (Continuous f:|Continuous g:|Nil))
    = case elg ab t f g of
      Nothing                    -> throw $ NotEligibleCone
      Just (Refl,Refl,Refl,Refl) -> Continuous $ ComplexMap s ab t (Map fg) where
        
        fg (Left x) = f' x
        fg (Right y) = g' y

        ComplexMap _ _ _ (Map f') = f
        ComplexMap _ _ _ (Map g') = g

  elg ::
    (Typeable x, Typeable y, Typeable t)
    => Complex (Either x y)
    -> Complex t
    -> ComplexMap s (Complex x') (Complex tF)
    -> ComplexMap s (Complex y') (Complex tS)
    -> Maybe (t :~: tF,t :~: tS,x :~: x', y :~: y')
  elg ab t f g = do
    tF <- tEq t f
    tS <- tEq t g
    ex <- xEq ab f
    ey <- yEq ab g
    return (tF,tS,ex,ey)

  tEq :: Typeable t
    => Complex t -> ComplexMap s c (Complex tF) -> Maybe (t :~: tF)
  tEq _ (ComplexMap _ _ _ f) = case tauTyp $ range f of Struct -> eqT

  xEq :: Typeable x
    => Complex (Either x y) -> ComplexMap s (Complex x') c -> Maybe (x :~: x')
  xEq _ (ComplexMap _ _ _ f) = case tauTyp $ domain f of Struct -> eqT

  yEq :: Typeable y
    => Complex (Either x y) -> ComplexMap s (Complex y') c -> Maybe (y :~: y')
  yEq _ (ComplexMap _ _ _ g) = case tauTyp $ domain g of Struct -> eqT


--------------------------------------------------------------------------------
-- cntSums2 -

cntSums2 :: AttestableSimplexType s => Sums N2 (Continuous s)
cntSums2 = LimitsG $ cntSum2

--------------------------------------------------------------------------------
-- cntSums -

cntSums :: AttestableSimplexType s => Sums n (Continuous s)
cntSums = sums (sums0 spcInitial) cntSums2

