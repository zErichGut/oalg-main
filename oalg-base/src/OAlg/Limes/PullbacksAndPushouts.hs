
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts #-}
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
    Pullbacks, Pullback, PullbackCone, PullbackDiagram

    -- ** Construction
  , pullbacks, pullbacks0, pullbacks1, plbPrdEql2

    -- *** Orientation
  , pullbacksOrnt

    -- * Pushouts
  , Pushouts, Pushout, PushoutCone, PushoutDiagram

    -- ** Construction
  , pushouts, pushouts', pshSumCoeql2

    -- *** Orientation
  , pushoutsOrnt

    -- * Duality
  , pshLimitsDuality

  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.MinimaAndMaxima
import OAlg.Limes.ProductsAndSums
import OAlg.Limes.EqualizersAndCoequalizers


--------------------------------------------------------------------------------
-- Pullbacks -

-- | 'Diagram' for a pullback.
type PullbackDiagram n = Diagram (Star To) (n+1) n

-- | 'Cone' for a pullback.
type PullbackCone n = Cone Mlt Projective (Star To) (n+1) n

-- | pullback as 'Limes'.
type Pullback n = Limes Mlt Projective (Star To) (n+1) n

-- | pullbacks for 'Multiplicative' structures.
type Pullbacks n = Limits Mlt Projective (Star To) (n+1) n


--------------------------------------------------------------------------------
-- plbMinimumDiagram0 -

-- | the underlying minimum diagram.
plbMinimumDiagram0 :: PullbackDiagram n a -> MinimumDiagram To N0 a
plbMinimumDiagram0 (DiagramSink e _) = DiagramChainTo e Nil


--------------------------------------------------------------------------------
-- plbMinimumCone0 -

-- | the underlying minimum cone.
plbMinimumCone0 :: PullbackCone n a -> MinimumCone To N0 a
plbMinimumCone0 (ConeProjective d t (c0:|_))
  = ConeProjective (plbMinimumDiagram0 d) t (c0:|Nil)

--------------------------------------------------------------------------------
-- pullbacks0 -

-- | pullbacks for zero arrows as 'Minima'.
pullbacks0 :: Multiplicative a => Pullbacks N0 a
pullbacks0 = Limits (plb minimaTo) where
  plb :: Multiplicative a => Minima To N0 a -> PullbackDiagram N0 a -> Pullback N0 a
  plb min d = LimesProjective l u where
    LimesProjective lMin uMin = limes min (plbMinimumDiagram0 d)
    l = ConeProjective d (tip lMin) (shell lMin)  
    u = uMin . plbMinimumCone0

--------------------------------------------------------------------------------
-- plbMinimumDiagram1 -

-- | the underlying minimum diagram given by the first arrow.
plbMinimumDiagram1 :: PullbackDiagram (n+1) a -> MinimumDiagram To N1 a
plbMinimumDiagram1 (DiagramSink e (a0:|_)) = DiagramChainTo e (a0:|Nil)

--------------------------------------------------------------------------------
-- plbMinimumCone1 -

-- | the underlying minimum cone given by the first arrow.
plbMinimumCone1 :: PullbackCone (n+1) a -> MinimumCone To N1 a
plbMinimumCone1 (ConeProjective d t (c0:|c1:|_))
  = ConeProjective (plbMinimumDiagram1 d) t (c0:|c1:|Nil)

--------------------------------------------------------------------------------
-- pullbacks1 -

-- | pullbacks of one arrow, i.e. 'Minima'.
pullbacks1 :: Multiplicative a => Pullbacks N1 a
pullbacks1 = Limits (plb minimaTo) where
  plb :: Multiplicative a => Minima To N1 a -> PullbackDiagram N1 a -> Pullback N1 a
  plb min d = LimesProjective l u where
    LimesProjective lMin uMin = limes min (plbMinimumDiagram1 d)
    
    l = ConeProjective d (tip lMin) (shell lMin)
    u = uMin . plbMinimumCone1

--------------------------------------------------------------------------------
-- pullbacks2 -

-- | promotion of pullbacks with at least two arrows.
pullbacks2 :: Multiplicative a => Pullbacks N2 a -> Pullbacks (n+2) a
pullbacks2 plb2 = Limits (plb plb2) where
  plb :: Multiplicative a
      => Pullbacks N2 a -> PullbackDiagram (n+2) a -> Pullback (n+2) a
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
pullbacks :: Multiplicative a => Pullbacks N2 a -> Pullbacks n a
pullbacks plb2 = Limits (plb plb2) where
  plb :: Multiplicative a
      => Pullbacks N2 a -> PullbackDiagram n a -> Pullback n a
  plb plb2 d = case dgArrows d of
    Nil     -> limes pullbacks0 d
    _:|Nil  -> limes pullbacks1 d
    _:|_:|_ -> limes (pullbacks2 plb2) d

--------------------------------------------------------------------------------
-- plbPrdEql2 -

-- | pullbacks given by products and equalizers.
plbPrdEql2 :: Multiplicative a => Products N2 a -> Equalizers N2 a -> Pullbacks N2 a
plbPrdEql2 prd eql = Limits (plb prd eql) where
  plb :: Multiplicative a
    => Products N2 a -> Equalizers N2 a -> PullbackDiagram N2 a -> Pullback N2 a
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
pullbacksOrnt = lmsToPrjOrnt

--------------------------------------------------------------------------------
-- Pushouts -

-- | 'Diagram' for a pushout.
type PushoutDiagram n = Diagram (Star From) (n+1) n

-- | 'Cone' for a pushout.
type PushoutCone n = Cone Mlt Injective (Star From) (n+1) n

-- | pushout as 'Limes'.
type Pushout n = Limes Mlt Injective (Star From) (n+1) n

-- | pushouts for a 'Multiplicative' structures.
type Pushouts n       = Limits Mlt Injective (Star From) (n+1) n

--------------------------------------------------------------------------------
-- Pusouts - Duality -

-- | duality between pushouts and pullbacks.
pshLimitsDuality :: Multiplicative a
  => LimitsDuality Mlt (Pushouts n) (Pullbacks n) a
pshLimitsDuality = LimitsDuality ConeStructMlt Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- pushouts -

-- | promotion of pushouts.
pushouts :: Multiplicative a => Pushouts N2 a -> Pushouts n a
pushouts psh2 = lmsFromOp pshLimitsDuality $ pullbacks plb2 where
  plb2 = lmsToOp pshLimitsDuality psh2

-- | 'pushouts' given by a proxy for @n@.
pushouts' :: Multiplicative a => p n -> Pushouts N2 a -> Pushouts n a
pushouts' _ = pushouts

--------------------------------------------------------------------------------
-- pushoutsOrnt -

-- | pushouts for 'Orientation'.
pushoutsOrnt :: Entity p => p -> Pushouts n (Orientation p)
pushoutsOrnt = lmsFromInjOrnt

--------------------------------------------------------------------------------
-- pshSumCoeql2 -

-- | pushouts given by sums and coequalizers.
pshSumCoeql2 :: Multiplicative a => Sums N2 a -> Coequalizers N2 a -> Pushouts N2 a
pshSumCoeql2 sum coeql = lmsFromOp pshLimitsDuality $ plbPrdEql2 prd eql where
  prd = lmsToOp sumLimitsDuality sum
  eql = lmsToOp coeqlLimitsDuality coeql

