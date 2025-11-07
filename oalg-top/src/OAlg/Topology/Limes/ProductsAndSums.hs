
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

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
  ) where

import Control.Monad as M

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Either

import OAlg.Structure.Definition

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Matrix.Vector

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.ProductsAndSums
import OAlg.Limes.Proposition

import OAlg.Homology.Complex hiding (cpxProduct)

import OAlg.Topology.Definition
import OAlg.Topology.Limes.TerminalAndInitialSpace

--------------------------------------------------------------------------------
-- cpxProduct -

cpxProduct :: (Entity x, Ord x, Entity y, Ord y)
  => Complex x -> Complex y
  -> ( Complex (x,y)
     , ComplexMap Preserving (Complex (x,y)) (Complex x)
     , ComplexMap Preserving (Complex (x,y)) (Complex y)
     )
cpxProduct a b = (ab, mFst, mSnd) where
  ab   = cpxProductAsc a b
  mFst = ComplexMapPrs ab a (Map fst)
  mSnd = ComplexMapPrs ab b (Map snd)

--------------------------------------------------------------------------------
-- cntProduct2 -

cntProduct2 :: Diagram Discrete N2 N0 (Continuous Abstract) -> Product N2 (Continuous Abstract)
cntProduct2 d@(DiagramDiscrete (SpaceAbstract a:|SpaceAbstract b:|Nil))
  = LimesProjective abCn (abUn ab) where
  
  (ab,mFst,mSnd) = cpxProduct a b

  abCn = ConeProjective d (SpaceAbstract ab) (CntAbstract mFst:|CntAbstract mSnd:|Nil)

  abUn :: (Entity x, Ord x, Entity y, Ord y)
    => Complex (x,y) -> ProductCone N2 (Continuous Abstract) -> Continuous Abstract
  abUn ab (ConeProjective _ (SpaceAbstract t)  (CntAbstract f:|CntAbstract g:|Nil))
    = case elg ab t f g of
      Nothing                    -> throw $ NotEligibleCone
      Just (Refl,Refl,Refl,Refl) -> CntAbstract fg where
        fg = ComplexMapPrs t ab (Map (\t -> (f' t, g' t)))
        ComplexMapPrs _ _ (Map f') = f
        ComplexMapPrs _ _ (Map g') = g
        
  elg ::
    (Typeable x, Typeable y, Typeable t)
    => Complex (x,y)
    -> Complex t
    -> ComplexMap Preserving (Complex tF) (Complex x')
    -> ComplexMap Preserving (Complex tS) (Complex y')
    -> Maybe (t :~: tF,t :~: tS,x :~: x', y :~: y')
  elg ab t f g = do
    tF <- tFEq t f
    tS <- tFEq t g
    xF <- xFEq ab f
    yS <- ySEq ab g
    return (tF,tS,xF,yS)
    
    where
      tFEq :: Typeable t
        => Complex t -> ComplexMap Preserving (Complex tF) c
        -> Maybe (t :~: tF)
      tFEq _ (ComplexMapPrs _ _ f) = case tauTyp $ domain f of Struct -> eqT

      xFEq :: Typeable x
        => Complex (x,y) -> ComplexMap Preserving (Complex tF) (Complex xF)
        -> Maybe (x :~: xF)
      xFEq _ (ComplexMapPrs _ _ f) = case tauTyp $ range f of Struct -> eqT 

      ySEq :: Typeable y
        => Complex (x,y) -> ComplexMap Preserving (Complex tS) (Complex yS)
        -> Maybe (y :~: yS)
      ySEq _ (ComplexMapPrs _ _ g) = case tauTyp $ range g of Struct -> eqT

--------------------------------------------------------------------------------
-- cntProducts2 -

cntProducts2 :: Products N2 (Continuous Abstract)
cntProducts2 = LimitsG cntProduct2

--------------------------------------------------------------------------------
-- cntProducts -

cntProducts :: Products n (Continuous Abstract)
cntProducts = products (products0 spcTerminal) cntProducts2

--------------------------------------------------------------------------------
-- 

instance ApplicativeG (Graph i) (->) (->) where amapG = M.fmap

--------------------------------------------------------------------------------
-- cpxSum2 -

cpxSum2 :: (Entity x, Ord x, Entity y, Ord y)
  => Complex x -> Complex y
  -> ( Complex (Either x y)
     , ComplexMap Preserving (Complex x) (Complex (Either x y))
     , ComplexMap Preserving (Complex y) (Complex (Either x y))
     )
cpxSum2 a@(Complex ssx) b@(Complex ssy) = (ab, mFst, mSnd) where
  ab   = Complex (amap1 left ssx || amap1 right ssy)
  mFst = ComplexMapPrs a ab (Map Left)
  mSnd = ComplexMapPrs b ab (Map Right)

  left :: Set (Set x) -> Set (Set (Either x y))
  left (Set sx) = Set $ amap1 (\(Set xs) -> Set (amap1 Left xs)) sx

  right :: Set (Set y) -> Set (Set (Either x y))
  right (Set sy) = Set $ amap1 (\(Set ys) -> Set (amap1 Right ys)) sy

--------------------------------------------------------------------------------
-- cntSum2 -

cntSum2 :: Diagram Discrete N2 N0 (Continuous Abstract) -> Sum N2 (Continuous Abstract)
cntSum2 d@(DiagramDiscrete (SpaceAbstract a:|SpaceAbstract b:|Nil))
  = LimesInjective abCn (abUn ab) where
  (ab,mFst,mSnd) = cpxSum2 a b
  
  abCn = ConeInjective d (SpaceAbstract ab) (CntAbstract mFst:|CntAbstract mSnd:|Nil)

  abUn :: (Entity x, Ord x, Entity y, Ord y)
    => Complex (Either x y) -> SumCone N2 (Continuous Abstract) -> Continuous Abstract
  abUn ab (ConeInjective _ (SpaceAbstract t)  (CntAbstract f:|CntAbstract g:|Nil))
    = case elg ab t f g of
      -- Nothing                    -> throw $ NotEligibleCone
      -- Nothing                    -> error $ show $ (tEq t f, tEq t g, xEq ab f, yEq ab g)
      Nothing                    -> error $ case cpmHomEntOrd g of
        Struct:>:Struct          -> show $ typeOf $ (t,cpmDomain g, cpmRange g)
      -- Nothing                    -> error $ show $ typeOf t
      Just (Refl,Refl,Refl,Refl) -> CntAbstract $ ComplexMapPrs ab t (Map fg) where
        
        fg (Left x) = f' x
        fg (Right y) = g' y

        ComplexMapPrs _ _ (Map f') = f
        ComplexMapPrs _ _ (Map g') = g

  elg ::
    (Typeable x, Typeable y, Typeable t)
    => Complex (Either x y)
    -> Complex t
    -> ComplexMap Preserving (Complex x') (Complex tF)
    -> ComplexMap Preserving (Complex y') (Complex tS)
    -> Maybe (t :~: tF,t :~: tS,x :~: x', y :~: y')
  elg ab t f g = do
    tF <- tEq t f
    tS <- tEq t g
    ex <- xEq ab f
    ey <- yEq ab g
    return (tF,tS,ex,ey)

  tEq :: Typeable t
    => Complex t -> ComplexMap Preserving c (Complex tF) -> Maybe (t :~: tF)
  tEq _ (ComplexMapPrs _ _ f) = case tauTyp $ range f of Struct -> eqT

  xEq :: Typeable x
    => Complex (Either x y) -> ComplexMap Preserving (Complex x') c -> Maybe (x :~: x')
  xEq _ (ComplexMapPrs _ _ f) = case tauTyp $ domain f of Struct -> eqT

  yEq :: Typeable y
    => Complex (Either x y) -> ComplexMap Preserving (Complex y') c -> Maybe (y :~: y')
  yEq _ (ComplexMapPrs _ _ g) = case tauTyp $ domain g of Struct -> eqT

--------------------------------------------------------------------------------
-- cntSums2 -

cntSums2 :: Sums N2 (Continuous Abstract)
cntSums2 = LimitsG cntSum2

--------------------------------------------------------------------------------
-- cntSums -

cntSums :: Sums n (Continuous Abstract)
cntSums = sums (sums0 spcInitial) cntSums2

d :: Diagram Discrete N3 N0 (Continuous Abstract)
d = DiagramDiscrete (spcPoint:|spcPoint:|spcPoint:|Nil)

p = limes cntProducts d
s = limes cntSums d
pU = universalCone p
sU = universalCone s

pF = universalFactor p pU
sF = universalFactor s sU

(f:|g:|h:|Nil) = shell sU

spcType :: Space m -> TypeRep
spcType (SpaceAbstract c) = typeOf c
spcType (SpaceConcrete c) = typeOf c
