
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- | Mapping of limits under adjunctions.
module OAlg.Adjunction.Limes
  (
    -- * Multiplicative
    lmPrjMap, lmInjMap
    
    -- * Distributive
  , lmPrjMapDst, lmInjMapDst
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Diagram
import OAlg.Entity.FinList

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom

import OAlg.Adjunction.Definition

import OAlg.Limes.Cone
import OAlg.Limes.Definition


--------------------------------------------------------------------------------
-- lmPrjMap -

lmPrjMapStruct :: Hom Mlt h
  => Struct Mlt d
  -> Adjunction h d c
  -> Limes Mlt Projective t n m d -> Limes Mlt Projective t n m c
lmPrjMapStruct Struct adj@(Adjunction l r _ _) (LimesProjective dLim dUniv)
  = LimesProjective cLim cUniv where

  dDgm = cnDiagram dLim
  
  cLim = cnMap r dLim
  
  cUniv (ConeProjective _ cTip fs) = adjr adj cTip (dUniv dCone) where
    -- from ConeProjective _ cTip fs is eligible and ajd is valid follows
    -- that dCone is eligible!
    dCone = ConeProjective dDgm (pmap l cTip) fs'
    fs' = amap1 (uncurry (adjl adj)) (dgPoints dDgm `zip` fs)


-- | mapping a 'Projective' limes under an adjunction.
lmPrjMap :: Hom Mlt h
  => Adjunction h d c -> Limes Mlt Projective t n m d -> Limes Mlt Projective t n m c
lmPrjMap adj@(Adjunction _ r _ _) = lmPrjMapStruct (tau (domain r)) adj


--------------------------------------------------------------------------------
-- lmInjMap -

lmInjMapHom :: Hom Mlt h
  => Homomorphous Mlt d c
  -> Dual (Dual t) :~: t
  -> Adjunction h d c -> Limes Mlt Injective t n m c -> Limes Mlt Injective t n m d
lmInjMapHom (Struct:>:Struct) rt adj@(Adjunction _ _ _ _) lim
  = coLimesInv ConeStructMlt Refl rt
  $ lmPrjMap (coAdjunction adj) (coLimes ConeStructMlt Refl rt lim)


lmInjMap :: Hom Mlt h
  => Adjunction h d c -> Limes Mlt Injective t n m c -> Limes Mlt Injective t n m d
lmInjMap adj lim = lmInjMapHom (adjHomMlt adj) (lmDiagramTypeRefl lim) adj lim

--------------------------------------------------------------------------------
-- lmPrjMapDst -

lmPrjMapDstStruct :: Hom Dst h => Struct Dst d -> Adjunction h d c
  -> Limes Dst Projective t n m d -> Limes Dst Projective t n m c
lmPrjMapDstStruct Struct adj@(Adjunction _ r _ _)
  (LimesProjective dLim@(ConeKernel _ _) dUniv) = LimesProjective cLim cUniv where

  dDgm = cnDiagram dLim

  cLim = cnMap r dLim

  cUniv (ConeKernel _ x) = adjr adj (start x) (dUniv dCone) where
    dCone = ConeKernel dDgm (adjl adj (head $ dgPoints dDgm) x)


lmPrjMapDst :: Hom Dst h
  => Adjunction h d c -> Limes Dst Projective t n m d -> Limes Dst Projective t n m c
lmPrjMapDst adj@(Adjunction _ r _ _) = lmPrjMapDstStruct (tau (domain r)) adj 

--------------------------------------------------------------------------------
-- lmInjMapDst -

lmInjMapDstHom :: Hom Dst h
  => Homomorphous Dst d c
  -> Dual (Dual t) :~: t
  -> Adjunction h d c -> Limes Dst Injective t n m c -> Limes Dst Injective t n m d
lmInjMapDstHom (Struct:>:Struct) rt adj@(Adjunction _ _ _ _) lim
  = coLimesInv ConeStructDst Refl rt
  $ lmPrjMapDst (coAdjunction adj) (coLimes ConeStructDst Refl rt lim)

lmInjMapDst :: Hom Dst h
  => Adjunction h d c -> Limes Dst Injective t n m c -> Limes Dst Injective t n m d
lmInjMapDst adj@(Adjunction _ r _ _) lim
  = lmInjMapDstHom (tauHom (homomorphous r)) (lmDiagramTypeRefl lim) adj lim


