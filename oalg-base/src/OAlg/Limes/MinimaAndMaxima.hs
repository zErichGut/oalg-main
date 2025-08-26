
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.MinimaAndMaxima
-- Description : minima and maxima
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- minima and maxima within a 'Multiplicative' structure, i.e. limits of @'Diagram' ('Chain' __t__)@.
module OAlg.Limes.MinimaAndMaxima
  (
    -- * Minima
    Minima, MinimaG
  , Minimum, MinimumG
  , MinimumCone, MinimumConic
  , MinimumDiagram, MinimumDiagrammatic
  , minimaTo, minimaGTo
  , minimaFrom, minimaGFrom

    -- * Maxima
  , Maxima, MaximaG
  , Maximum, MaximumG
  , MaximumCone, MaximumConic
  , MaximumDiagram, MaximumDiagrammatic
  , maximaTo, maximaFrom, maximaTo', maximaFrom'

    -- * Duality
  , DualisableGChain
  , coMinimaGTo, coMinimaGFrom
  )
  where

import Control.Monad

import Data.Typeable
import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Entity.Natural
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone
import OAlg.Limes.Cone.FactorChain
import OAlg.Limes.Definition
import OAlg.Limes.Limits


--------------------------------------------------------------------------------
-- Minima -

-- | 'Diagrammatic' object for a minimum.
type MinimumDiagrammatic d t n = d (Chain t) (n+1) n :: Type -> Type

-- | 'Diagram' for a minimum.
type MinimumDiagram t n = MinimumDiagrammatic Diagram t n

-- | 'Conic' object for a minimum.
type MinimumConic c (d :: DiagramType -> N' -> N' -> Type -> Type) t n
  = c Mlt Projective d (Chain t) (n+1) n :: Type -> Type

-- | 'Cone' for a minimum.
type MinimumCone t n = MinimumConic Cone Diagram t n

-- | generic minimum as 'LimesG'.
type MinimumG c d t n = LimesG c Mlt Projective d (Chain t) (n+1) n

-- | minimum as 'Limes'.
type Minimum t n = MinimumG Cone Diagram t n

-- | generic minima for a 'Multiplicative' structure.
type MinimaG c d t n = LimitsG c Mlt Projective d (Chain t) (n+1) n

-- | minima for a 'Multiplicative' structure.
type Minima t n = MinimaG Cone Diagram t n

--------------------------------------------------------------------------------
-- minima -

-- | generic minima according to @'Chain' 'To'@.
minimaGTo ::
  ( Multiplicative x
  , Diagrammatic d
  ) => MinimaG Cone d To n x
minimaGTo = LimitsG lMin where
  lMin :: (Multiplicative x, Diagrammatic d)
       => MinimumDiagrammatic d To n x -> MinimumG Cone d To n x
  lMin d = LimesProjective l u where
    l = cnPrjChainTo (FactorChain (one (chnToStart $ diagram d)) d)
    u c = f where FactorChain f _ = cnPrjChainToInv c

-- | minima according to @'Chain' 'To'@.
minimaTo :: Multiplicative x => Minima To n x
minimaTo = minimaGTo

-- | generic minima according to @'Chain' 'From'@.
minimaGFrom ::
  ( Multiplicative x
  , Diagrammatic d
  ) => MinimaG Cone d From n x
minimaGFrom = LimitsG lMin where
  lMin :: ( Multiplicative x, Diagrammatic d)
       => MinimumDiagrammatic d From n x -> MinimumG Cone d From n x
  lMin d = LimesProjective l u where
    l = cnPrjChainFrom (FactorChain (one (chnFromStart $ diagram d)) d)
    u c = f where FactorChain f _ = cnPrjChainFromInv c

-- | minima according to @'Chain' 'From'@.
minimaFrom :: Multiplicative x => Minima From n x
minimaFrom = minimaGFrom

--------------------------------------------------------------------------------
-- Maxima -

-- | 'Diagrammatic' object for a maximum.
type MaximumDiagrammatic d t n = d (Chain t) (n+1) n :: Type -> Type

-- | 'Diagram' for a maximum.
type MaximumDiagram t n = MaximumDiagrammatic Diagram t n

-- | 'Conic' object for a maximum.
type MaximumConic c (d :: DiagramType -> N' -> N' -> Type -> Type) t n
  = c Mlt Injective d (Chain t) (n+1) n :: Type -> Type

-- | 'Cone' for a maximum.
type MaximumCone t n = MaximumConic Cone Diagram t n

-- | generic maximum as 'LimesG'.
type MaximumG c d t n = LimesG c Mlt Injective d (Chain t) (n+1) n

-- | maximum as 'Limes'.
type Maximum t n = MaximumG Cone Diagram t n

-- | generic maxima for a 'Multiplicative' structure.
type MaximaG c d t n = LimitsG c Mlt Injective d (Chain t) (n+1) n

-- | maxima for a 'Multiplicative' structure.
type Maxima t n = MaximaG Cone Diagram t n

--------------------------------------------------------------------------------
-- DualisableGChain -

-- | type for dualisable generic limits of 'Conic'' objects over t'Chain' 'Diagrammatic' objects.
type DualisableGChain p t o c d n
  = NaturalConicBi (HomDisjEmpty Mlt o) c Mlt p d (Chain t) (n+1) n

--------------------------------------------------------------------------------
-- coMinimumTo -

coMinimumGTo ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableGChain Projective To o c d n
  )
  => MinimumG c d To n x -> MaximumG c d From n (o x)
coMinimumGTo min = max where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)
  SDualBi (Left1 max) = amapF i (SDualBi (Right1 min))

--------------------------------------------------------------------------------
-- coMinimaTo -

coMinimaGTo ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableGChain Projective To o c d n
  )
  => MinimaG c d To n x -> MaximaG c d From n (o x)
coMinimaGTo min = max where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)
  SDualBi (Left1 max) = amapF i (SDualBi (Right1 min))

--------------------------------------------------------------------------------
-- coMinimaFrom -

coMinimaGFrom ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableGChain Projective From o c d n
  )
  => MinimaG c d From n x -> MaximaG c d To n (o x)
coMinimaGFrom min = max where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)
  SDualBi (Left1 max) = amapF i (SDualBi (Right1 min))

--------------------------------------------------------------------------------
-- coMaximaFrom -

coMaximaGFrom ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableGChain Injective From o c d n
  )
  => MaximaG c d From n x -> MinimaG c d To n (o x)
coMaximaGFrom min = max where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)
  SDualBi (Left1 max) = amapF i (SDualBi (Right1 min))

--------------------------------------------------------------------------------
-- maxima -

maximaTo :: Multiplicative x => Maxima To n x
maximaTo = maxs where
  Contravariant2 i = toDualOpMlt
  SDualBi (Left1 maxs) = amapF (inv2 i) (SDualBi (Right1 minimaFrom)) 


maximaFrom :: Multiplicative x => Maxima From n x
maximaFrom = maxs where
  Contravariant2 i = toDualOpMlt
  SDualBi (Left1 maxs) = amapF (inv2 i) (SDualBi (Right1 minimaTo)) 

-- | maxima according to @'Chain' 'To'@ given by two proxy types.
maximaTo' :: Multiplicative x => p n -> f x -> Maxima To n x
maximaTo' _ _ = maximaTo

-- | maxima according to @'Chain' 'From'@ given by two proxy types.
maximaFrom' :: Multiplicative x => p n -> f x -> Maxima From n x
maximaFrom' _ _ = maximaFrom

--------------------------------------------------------------------------------
-- xecOrtSite -

xecPrjOrtSiteTo :: (Conic c, Diagrammatic d, Multiplicative x)
  => XOrtSite To x -> MinimumG c d t n x -> X (MinimumConic Cone d t n x)
xecPrjOrtSiteTo xe = xcn xe . diagrammaticObject . cone . universalCone where
  
  xcn :: (Diagrammatic d, Multiplicative x)
    => XOrtSite To x -> d (Chain t) (n+1) n x -> X (MinimumConic Cone d t n x)
  xcn (XEnd _ xe) d = case diagram d of
    d'@(DiagramChainTo _ _)   -> do
      f <- xe $ chnToStart d'
      return $ cnPrjChainTo (FactorChain f d)
    DiagramChainFrom s _      -> do
      f <- xe s
      return $ cnPrjChainFrom (FactorChain f d)

xecInjOrtSiteFrom ::
  ( Multiplicative x
  , DualisableGChain Injective t Op c d n
  , NaturalDiagrammaticBi (Inv2 (HomDisjEmpty Mlt Op)) d (Chain (Dual t)) (n+1) n  
  )
  => XOrtSite From x -> MaximumG c d t n x -> X (MaximumConic Cone d t n x)
xecInjOrtSiteFrom xf max = amap1 coMin xmin where
  xmin = xecPrjOrtSiteTo (coXOrtSite xf) (coMax max)

  coMax ::
    ( Multiplicative x
    , DualisableGChain Injective t Op c d n
    )
    => MaximumG c d t n x -> MinimumG c d (Dual t) n (Op x)
  coMax max = min where
    Contravariant2 i = toDualOpMlt
    SDualBi (Left1 min) = amapF i (SDualBi (Right1 max))

  coMin ::
    ( Multiplicative x
    , NaturalDiagrammaticBi (Inv2 (HomDisjEmpty Mlt Op)) d (Chain t) (n+1) n
    )
    => MinimumConic Cone d t n (Op x) -> MaximumConic Cone d (Dual t) n x
  coMin min = max where
    Contravariant2 i      = toDualOpMlt
    SDualBi (Left1 max) = amapF (inv2 i) (SDualBi (Right1 min))

xecOrtSiteChain ::
  (  Multiplicative x
  , s ~ Mlt
  , DualisableGChain Injective t Op c d n
  , NaturalDiagrammaticBi (Inv2 (HomDisjEmpty Mlt Op)) d (Chain (Dual t)) (n+1) n  
  )
  => XOrtSite r x -> XEligibleCone c s (ToPerspective r) d (Chain t) (n+1) n x
xecOrtSiteChain xe@(XEnd _ _)   = XEligibleCone (xecPrjOrtSiteTo xe)
xecOrtSiteChain xs@(XStart _ _) = XEligibleCone (xecInjOrtSiteFrom xs)

--------------------------------------------------------------------------------
-- prpMinimaAndMaxima -

prpMinimaAndMaxima :: N -> Statement
prpMinimaAndMaxima n = case someNatural n of
  SomeNatural n' -> And [ prpLimitsG xecMaxTo xecfMaxTo xStandard maxTo
                        , prpLimitsG xecMaxFm xecfMaxFm xStandard maxFm
                        , prpLimitsG xecMaxFm' xecfMaxFm' xStandard maxFm'
                        , prpLimitsG xecMaxToN xecfMaxToN xStandard maxToN
                        ]
    where
      maxTo     = maximaTo' n' (Proxy :: Proxy OS)
      xecMaxTo  = xEligibleConeOrnt xStandard
      xecfMaxTo = xEligibleConeFactorOrnt xStandard

      maxFm     = maximaFrom' n' (Proxy :: Proxy OS)
      xecMaxFm  = xEligibleConeOrnt xStandard
      xecfMaxFm = xEligibleConeFactorOrnt xStandard

      Contravariant2 i = toDualOpMlt
      SDualBi (Left1 maxFm') = amapG i (SDualBi (Right1 maxFm))
      xecMaxFm'  = coXEligibleCone xecMaxFm
      xecfMaxFm' = coXEligibleConeFactor xecfMaxFm

      maxToN     = maximaTo' n' (Proxy :: Proxy N)
      xecMaxToN  = xecOrtSiteChain (xoFrom $ xoTtl $ xNB 0 100)
      xecfMaxToN = xecfOrtSite (xoFrom $ xoTtl $ xNB 0 100)


