
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Adjunction.Limes
-- Description : mapping of limits under adjunctions
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- mapping of 'OAlg.Limes.Limits.Limits' under 'Adjunction's.
module OAlg.Adjunction.Limes
  (
    -- * Multiplicative
    lmPrjMap, lmInjMap
    
    -- * Distributive
  , lmPrjMapDst, lmInjMapDst

  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Proxy

import OAlg.Entity.Diagram
import OAlg.Entity.FinList

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom

import OAlg.Adjunction.Definition hiding (coAdjunctionOp)

import OAlg.Limes.Cone
import OAlg.Limes.Definition

--------------------------------------------------------------------------------
-- homDisjMlt -

homDisjMlt :: HomMultiplicative h => h x y -> Variant2 Covariant (HomDisj Mlt Op h) x y
homDisjMlt = homDisj

--------------------------------------------------------------------------------
-- adjHomDisj' -

adjHomDisj' ::
  ( HomMultiplicative h
  , Transformable (ObjectClass h) s
  )
  => q s o -> Adjunction h x y -> Adjunction (Variant2 Covariant (HomDisj s o h)) x y
adjHomDisj' _ = adjHomDisj

--------------------------------------------------------------------------------
-- lmPrjMap -

-- | blabla
--
-- @
--              l
--          <------- 
--        x          y
--          -------->
--              r
-- @
--
lmPrjMapGStruct ::
  ( NaturalConic h c s Projective d t n m
  , s ~ Mlt
  ) 
  => Struct s x
  -> Adjunction (Variant2 Covariant h) x y
  -> LimesG c s Projective d t n m x -> LimesG c s Projective d t n m y
lmPrjMapGStruct Struct adj@(Adjunction (Covariant2 l) (Covariant2 r) _ _)
  (LimesProjective xLim xUniv) = LimesProjective yLim yUniv where

  xDgm     = diagrammaticObject $ cone xLim
  xDgmPnts = dgPoints $ diagram xDgm
  
  SDualBi (Right1 (ConeG yLim)) = amapF r (SDualBi (Right1 (ConeG xLim)))

  yUniv (ConeProjective _ yTip fs) = adjr adj yTip (xUniv xCn) where
    -- from ConeProjective _ cTip fs is valid, eligible and ajd is valid follows
    -- that xCn is valid and eligible!
    fs'  = amap1 (uncurry (adjl adj)) (xDgmPnts `zip` fs)
    xCn  = ConeProjective xDgm (pmap l yTip) fs'

lmPrjMapStruct :: HomMultiplicative h
  => Struct Mlt d
  -> Adjunction h d c
  -> Limes Mlt Projective t n m d -> Limes Mlt Projective t n m c
lmPrjMapStruct s adj l = case lmDiagramTypeRefl l of
  Refl -> lmPrjMapGStruct s (adjHomDisj' (Proxy2 :: Proxy2 Mlt Op) adj) l 

{-

old implementation, keep it for the moment!!!!

lmPrjMapStruct Struct adj@(Adjunction l r _ _) (LimesProjective dLim dUniv)
  = LimesProjective cLim cUniv where

  dDgm = diagram $ diagrammaticObject dLim
  
  -- cLim = cnMap r dLim
  Covariant2 rCov = homDisjMlt r
  SDualBi (Right1 cLim) = case dgTypeRefl dDgm of Refl -> amapF rCov (SDualBi (Right1 dLim))
  
  cUniv (ConeProjective _ cTip fs) = adjr adj cTip (dUniv dCone) where
    -- from ConeProjective _ cTip fs is eligible and ajd is valid follows
    -- that dCone is eligible!
    dCone = ConeProjective dDgm (pmap l cTip) fs'
    fs' = amap1 (uncurry (adjl adj)) (dgPoints dDgm `zip` fs)
-}


-- | mapping a projective limes under an adjunction.
lmPrjMap :: HomMultiplicative h
  => Adjunction h d c -> Limes Mlt Projective t n m d -> Limes Mlt Projective t n m c
lmPrjMap adj@(Adjunction _ r _ _) = lmPrjMapStruct (tau (domain r)) adj

--------------------------------------------------------------------------------
-- lmInjMap -

lmInjMapGStruct ::
  ( NaturalConic (Inv2 h) c s Injective d t n m
  , NaturalConic (Inv2 h) c s Projective d (Dual t) n m
  , NaturalConic h c s Projective d (Dual t) n m
  , s ~ Mlt
  )
  => Struct s y
  -> Variant2 Contravariant (Inv2 h) x (Op x)
  -> Variant2 Contravariant (Inv2 h) y (Op y)
  -> Adjunction (Variant2 Covariant h) x y
  -> LimesG c s Injective d t n m y -> LimesG c s Injective d t n m x
lmInjMapGStruct sy xOp@(Contravariant2 ixOp) yOp@(Contravariant2 iyOp) adj yLmInj = xLmInj where
  adj'                    = adjMapCnt xOp yOp adj  -- :: Adjunctin (Variant2 Covariant h) (Op y) (Op x)
  SDualBi (Left1 yLmPrj') = amapF iyOp (SDualBi (Right1 yLmInj))
  xLmPrj'                 = lmPrjMapGStruct (tauO sy) adj' yLmPrj'
  SDualBi (Right1 xLmInj) = amapG (inv2 ixOp) (SDualBi (Left1 xLmPrj'))

-- | mapping a injective limes under an adjunction.
lmInjMap :: HomMultiplicative h
  => Adjunction h d c -> Limes Mlt Injective t n m c -> Limes Mlt Injective t n m d
lmInjMap adj l = case lmDiagramTypeRefl l of
  Refl -> lmInjMapGStruct sc (isoHomDisj sd) (isoHomDisj sc) (adjHomDisj adj) l where
            sd :>: sc = adjHomMlt adj

--------------------------------------------------------------------------------
-- lmPrjMapDst -

lmPrjMapDstGStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalConic h c s Projective d t n m
  , s ~ Dst
  ) 
  => Struct s x
  -> Adjunction (Variant2 Covariant h) x y
  -> LimesG c s Projective d t n m x -> LimesG c s Projective d t n m y
lmPrjMapDstGStruct Struct adj@(Adjunction (Covariant2 _) (Covariant2 r) _ _)
  (LimesProjective xLim xUniv) = LimesProjective yLim yUniv where

  xDgm     = diagrammaticObject $ cone xLim
  xDgmPnts = dgPoints $ diagram xDgm
  
  SDualBi (Right1 (ConeG yLim)) = amapF r (SDualBi (Right1 (ConeG xLim)))

  yUniv (ConeKernel _ f) = adjr adj yTip (xUniv xCn) where
    -- from ConeProjective _ cTip fs is valid, eligible and ajd is valid follows
    -- that xCn is valid and eligible!
    yTip = start f 
    f'   = adjl adj (head xDgmPnts) f
    xCn  = ConeKernel xDgm f'

{-
-- old implementation

lmPrjMapDstStruct :: Hom Dst h => Struct Dst d -> Adjunction h d c
  -> Limes Dst Projective t n m d -> Limes Dst Projective t n m c
lmPrjMapDstStruct Struct adj@(Adjunction _ r _ _)
  (LimesProjective dLim@(ConeKernel _ _) dUniv) = LimesProjective cLim cUniv where

  dDgm = cnDiagram dLim

  cLim = cnMap r dLim

  cUniv (ConeKernel _ x) = adjr adj (start x) (dUniv dCone) where
    dCone = ConeKernel dDgm (adjl adj (head $ dgPoints dDgm) x)
-}

lmPrjMapDstStruct :: HomDistributive h
  => Struct Dst d
  -> Adjunction h d c
  -> Limes Dst Projective t n m d -> Limes Dst Projective t n m c
lmPrjMapDstStruct s adj l = case lmDiagramTypeRefl l of
  Refl -> lmPrjMapDstGStruct s (adjHomDisj' (Proxy2 :: Proxy2 Dst Op) adj) l

-- | mapping a projective limes under an adjunction.
lmPrjMapDst :: HomDistributive h
  => Adjunction h d c -> Limes Dst Projective t n m d -> Limes Dst Projective t n m c
lmPrjMapDst adj@(Adjunction _ r _ _) = lmPrjMapDstStruct (tau (domain r)) adj 

--------------------------------------------------------------------------------
-- lmInjMapDst -

lmInjMapDstGStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalConicBi (Inv2 h) c s Injective d t n m
  , NaturalConic h c s Projective d (Dual t) n m
  , s ~ Dst
  )
  => Struct s y
  -> Variant2 Contravariant (Inv2 h) x (Op x)
  -> Variant2 Contravariant (Inv2 h) y (Op y)
  -> Adjunction (Variant2 Covariant h) x y
  -> LimesG c s Injective d t n m y -> LimesG c s Injective d t n m x
lmInjMapDstGStruct sy xOp@(Contravariant2 ixOp) yOp@(Contravariant2 iyOp) adj yLmInj = xLmInj where
  adj'                    = adjMapCnt xOp yOp adj  -- :: Adjunctin (Variant2 Covariant h) (Op y) (Op x)
  SDualBi (Left1 yLmPrj') = amapF iyOp (SDualBi (Right1 yLmInj))
  xLmPrj'                 = lmPrjMapDstGStruct (tauO sy) adj' yLmPrj'
  SDualBi (Right1 xLmInj) = amapG (inv2 ixOp) (SDualBi (Left1 xLmPrj'))

lmInjMapDst :: HomDistributive h
  => Adjunction h d c -> Limes Dst Injective t n m c -> Limes Dst Injective t n m d
lmInjMapDst adj l = case lmDiagramTypeRefl l of
  Refl -> lmInjMapDstGStruct sc (isoHomDisj sd) (isoHomDisj sc) (adjHomDisj adj) l where
            sd :>: sc = adjHomDst adj

