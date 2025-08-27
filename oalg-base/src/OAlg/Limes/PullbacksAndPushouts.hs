
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.PullbacksAndPushouts
-- Description : pullbacks and pushouts
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- pullbacks and pushouts, i.e. limits of @'Diagram' ('Star' __d__)@.
module OAlg.Limes.PullbacksAndPushouts
  (

    -- * Pullbacks
    Pullbacks, PullbacksG
  , Pullback, PullbackG
  , PullbackCone, PullbackConic
  , PullbackDiagram, PullbackDiagrammatic

    -- ** Construction
  , pullbacks, pullbacks0, pullbacks1, plbPrdEql2

    -- *** Orientation
  , pullbacksOrnt

    -- * Pushouts
  , Pushouts, PushoutsG
  , Pushout, PushoutG
  , PushoutCone, PushoutConic
  , PushoutDiagram, PushoutDiagrammatic

    -- ** Construction
  , pushouts, pushouts', pshSumCoeql2

    -- *** Orientation
  , pushoutsOrnt

  )
  where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.MinimaAndMaxima
import OAlg.Limes.ProductsAndSums
import OAlg.Limes.EqualizersAndCoequalizers

--------------------------------------------------------------------------------
-- Pullbacks -

-- | 'Diagrammmatic' object for a pullback.
type PullbackDiagrammatic d (n :: N') = d (Star To) (n+1) n :: Type -> Type

-- | 'Diagram' for a pullback.
type PullbackDiagram n = PullbackDiagrammatic Diagram n

-- | 'Conic' object for a pullback.
type PullbackConic c (d :: DiagramType -> N' -> N' -> Type -> Type) (n :: N')
  = c Mlt Projective d (Star To) (n+1) n :: Type -> Type

-- | 'Cone' for a pullback.
type PullbackCone n = PullbackConic Cone Diagram n

-- | generic pullback as 'LimesG'.
type PullbackG c d n = LimesG c Mlt Projective d (Star To) (n+1) n

-- | pullback as 'Limes'.
type Pullback n = PullbackG Cone Diagram n

-- | generic pullbacks for 'Multiplicative' structures.
type PullbacksG c d n = LimitsG c Mlt Projective d (Star To) (n+1) n

-- | pullbacks for 'Multiplicative' structures.
type Pullbacks n = PullbacksG Cone Diagram n

--------------------------------------------------------------------------------
-- plbMinimumDiagram0 -

-- | the underlying minimum diagram.
plbMinimumDiagram0 :: PullbackDiagram n x -> MinimumDiagram To N0 x
plbMinimumDiagram0 (DiagramSink e _) = DiagramChainTo e Nil


--------------------------------------------------------------------------------
-- plbMinimumCone0 -

-- | the underlying minimum cone.
plbMinimumCone0 :: PullbackCone n x -> MinimumCone To N0 x
plbMinimumCone0 (ConeProjective d t (c0:|_))
  = ConeProjective (plbMinimumDiagram0 d) t (c0:|Nil)

--------------------------------------------------------------------------------
-- pullbacks0 -

-- | pullbacks for zero arrows as 'Minima'.
pullbacks0 :: Multiplicative x => Pullbacks N0 x
pullbacks0 = LimitsG (plb minimaTo) where
  plb :: Multiplicative x => Minima To N0 x -> PullbackDiagram N0 x -> Pullback N0 x
  plb min d = LimesProjective l u where
    LimesProjective lMin uMin = limes min (plbMinimumDiagram0 d)
    l = ConeProjective d (tip lMin) (shell lMin)  
    u = uMin . plbMinimumCone0

--------------------------------------------------------------------------------
-- plbMinimumDiagram1 -

-- | the underlying minimum diagram given by the first arrow.
plbMinimumDiagram1 :: PullbackDiagram (n+1) x -> MinimumDiagram To N1 x
plbMinimumDiagram1 (DiagramSink e (a0:|_)) = DiagramChainTo e (a0:|Nil)

--------------------------------------------------------------------------------
-- plbMinimumCone1 -

-- | the underlying minimum cone given by the first arrow.
plbMinimumCone1 :: PullbackCone (n+1) x -> MinimumCone To N1 x
plbMinimumCone1 (ConeProjective d t (c0:|c1:|_))
  = ConeProjective (plbMinimumDiagram1 d) t (c0:|c1:|Nil)

--------------------------------------------------------------------------------
-- pullbacks1 -

-- | pullbacks of one arrow, i.e. 'Minima'.
pullbacks1 :: Multiplicative x => Pullbacks N1 x
pullbacks1 = LimitsG (plb minimaTo) where
  plb :: Multiplicative x => Minima To N1 x -> PullbackDiagram N1 x -> Pullback N1 x
  plb min d = LimesProjective l u where
    LimesProjective lMin uMin = limes min (plbMinimumDiagram1 d)
    
    l = ConeProjective d (tip lMin) (shell lMin)
    u = uMin . plbMinimumCone1

--------------------------------------------------------------------------------
-- pullbacks2 -

-- | promotion of pullbacks with at least two arrows.
pullbacks2 :: Multiplicative x => Pullbacks N2 x -> Pullbacks (n+2) x
pullbacks2 plb2 = LimitsG (plb plb2) where
  plb :: Multiplicative x
      => Pullbacks N2 x -> PullbackDiagram (n+2) x -> Pullback (n+2) x
  plb plb2 d@(DiagramSink _ (_:|_:|Nil)) = limes plb2 d
  plb plb2 d@(DiagramSink e (a1:|aN@(_:|_:|_))) = LimesProjective l u where
    dN = DiagramSink e aN
    LimesProjective (ConeProjective _ _ (h1:|hN)) uN = plb plb2 dN

    d2 = DiagramSink e (a1:|h1:|Nil)
    LimesProjective (ConeProjective _ k (k0:|k1:|k2:|Nil)) u2 = plb plb2 d2
    
    l = ConeProjective d k (k0:|k1:|amap1 (*k2) hN)
    u (ConeProjective _ x (x0:|x1:|xN)) = u2 (ConeProjective d2 x (x0:|x1:|uh:|Nil)) where
      uh = uN (ConeProjective dN x (x0:|xN))

--------------------------------------------------------------------------------
-- pullbacks -

-- | promotion of pullbacks.
--
-- ![image pullback](c:/Users/zeric/haskell/oalg/src/OAlg/Limes/pullback.png)
pullbacks :: Multiplicative x => Pullbacks N2 x -> Pullbacks n x
pullbacks plb2 = LimitsG (plb plb2) where
  plb :: Multiplicative x
      => Pullbacks N2 x -> PullbackDiagram n x -> Pullback n x
  plb plb2 d = case dgArrows d of
    Nil     -> limes pullbacks0 d
    _:|Nil  -> limes pullbacks1 d
    _:|_:|_ -> limes (pullbacks2 plb2) d

--------------------------------------------------------------------------------
-- plbPrdEql2 -



-- | pullbacks given by products and equalizers.
plbPrdEql2 :: Multiplicative x => Products N2 x -> Equalizers N2 x -> Pullbacks N2 x
plbPrdEql2 prd eql = LimitsG (plb prd eql) where
  cnDiagram = diagram . diagrammaticObject
  
  plb :: Multiplicative x
    => Products N2 x -> Equalizers N2 x -> PullbackDiagram N2 x -> Pullback N2 x
  plb prd eql d@(DiagramSink s as@(f:|g:|Nil)) = LimesProjective l u where
    LimesProjective p uPrd = limes prd (DiagramDiscrete $ amap1 start as)
    shp@(pf:|pg:|Nil) = shell p
    dp = cnDiagram p

    LimesProjective e uEql = limes eql (DiagramParallelLR (tip p) s (f*pf:|g*pg:|Nil))
    e0:|e1:|Nil = shell e
    de = cnDiagram e
    
    l = ConeProjective d (tip e) (e1:|amap1 (*e0) shp) 
    u (ConeProjective _ x (x0:|xs)) = uEql (ConeProjective de x (up:|x0:|Nil)) where
      up = uPrd (ConeProjective dp x xs)

--------------------------------------------------------------------------------
-- pullbacksOrnt -

-- | pullbacks for 'Orientation'.
pullbacksOrnt :: Entity p => p -> Pullbacks n (Orientation p)
pullbacksOrnt = lmsMltPrjOrnt


--------------------------------------------------------------------------------
-- Pushouts -

-- | 'Diagrammmatic' object for a pushout.
type PushoutDiagrammatic d (n :: N') = d (Star From) (n+1) n :: Type -> Type

-- | 'Diagram' for a pushout.
type PushoutDiagram n = PushoutDiagrammatic Diagram n

-- | 'Conic' object for a pushout.
type PushoutConic c (d :: DiagramType -> N' -> N' -> Type -> Type) (n :: N')
  = c Mlt Injective d (Star From) (n+1) n :: Type -> Type

-- | 'Cone' for a pushout.
type PushoutCone n = PushoutConic Cone Diagram n

-- | generic pushout as 'LimesG'.
type PushoutG c d n = LimesG c Mlt Injective d (Star From) (n+1) n

-- | pushout as 'Limes'.
type Pushout n = PushoutG Cone Diagram n

-- | generic pushouts for 'Multiplicative' structures.
type PushoutsG c d n = LimitsG c Mlt Injective d (Star From) (n+1) n

-- | pushouts for 'Multiplicative' structures.
type Pushouts n = PushoutsG Cone Diagram n


--------------------------------------------------------------------------------
-- pushouts -

-- | promotion of pushouts.
pushouts :: Multiplicative x => Pushouts N2 x -> Pushouts n x
pushouts psh2 = pshs where
  Contravariant2 i      = toDualOpMlt
  SDualBi (Left1 plb2)  = amapF i (SDualBi (Right1 psh2))
  plbs                  = pullbacks plb2
  SDualBi (Right1 pshs) = amapF (inv2 i) (SDualBi (Left1 plbs))
  

-- | 'pushouts' given by a proxy for @n@.
pushouts' :: Multiplicative x => p n -> Pushouts N2 x -> Pushouts n x
pushouts' _ = pushouts

--------------------------------------------------------------------------------
-- pushoutsOrnt -

-- | pushouts for 'Orientation'.
pushoutsOrnt :: Entity p => p -> Pushouts n (Orientation p)
pushoutsOrnt = lmsMltInjOrnt

--------------------------------------------------------------------------------
-- pshSumCoeql2 -

-- | pushouts given by sums and coequalizers.
pshSumCoeql2 :: Multiplicative x => Sums N2 x -> Coequalizers N2 x -> Pushouts N2 x
pshSumCoeql2 sum coeql = pshs where
  Contravariant2 i      = toDualOpMlt
  SDualBi (Left1 prd)   = amapF i (SDualBi (Right1 sum))
  SDualBi (Left1 eql)   = amapF i (SDualBi (Right1 coeql))
  plbs                  = plbPrdEql2 prd eql
  SDualBi (Right1 pshs) = amapF (inv2 i) (SDualBi (Left1 plbs))
  
