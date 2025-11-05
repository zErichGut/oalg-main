
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

import Control.Monad

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Structure.Definition

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Matrix.Vector

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.ProductsAndSums

import OAlg.Homology.Complex hiding (cpxProduct)

import OAlg.Topology.Definition

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
    -> ComplexMap Preserving (Complex tF) (Complex xF)
    -> ComplexMap Preserving (Complex tS) (Complex yS)
    -> Maybe (t :~: tF,t :~: tS,x :~: xF, y :~: yS)
  elg ab t f g = do
    tF <- tFEq t f
    tS <- tSEq t g
    xF <- xFEq ab f
    yS <- ySEq ab g
    return (tF,tS,xF,yS)
    
    where
      tFEq :: Typeable t
        => Complex t -> ComplexMap Preserving (Complex tF) (Complex xF)
        -> Maybe (t :~: tF)
      tFEq _ (ComplexMapPrs _ _ f) = case tauTyp $ domain f of Struct -> eqT

      tSEq :: Typeable t
        => Complex t -> ComplexMap Preserving (Complex tS) (Complex xS)
        -> Maybe (t :~: tS)
      tSEq = tFEq

      xFEq :: Typeable x
        => Complex (x,y) -> ComplexMap Preserving (Complex tF) (Complex xF)
        -> Maybe (x :~: xF)
      xFEq _ (ComplexMapPrs _ _ f) = case tauTyp $ range f of Struct -> eqT 

      ySEq :: Typeable y
        => Complex (x,y) -> ComplexMap Preserving (Complex tS) (Complex yS)
        -> Maybe (y :~: yS)
      ySEq _ (ComplexMapPrs _ _ g) = case tauTyp $ range g of Struct -> eqT
