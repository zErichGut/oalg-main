
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.EqualizersAndCoequalizers
-- Description : equalizers and coequalizers
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- equalizers and coequalizers, i.e. limits of @'Diagram' ('Parallel' __d__)@.
module OAlg.Limes.EqualizersAndCoequalizers
  (
    -- * Equalizers
    Equalizers, EqualizersG
  , Equalizer, EqualizerG
  , EqualizerCone, EqualizerConic
  , EqualizerDiagram, EqualizerDiagrammatic

    -- ** Construction
  , equalizers, equalizers0, equalizers1, equalizers2

    -- *** Orientation
  , equalizersOrnt

    -- * Coequalizers
  , Coequalizers, CoequalizersG
  , Coequalizer, CoequalizerG
  , CoequalizerCone, CoequalizerConic
  , CoequalizerDiagram, CoequalizerDiagrammatic

    -- ** Construction
  , coequalizers, coequalizers'

    -- *** Orientation
  , coequalizersOrnt

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

--------------------------------------------------------------------------------
-- Equalizers -

-- | 'Diagrammatic' object for a equalizer. 
type EqualizerDiagrammatic d (n :: N') = d (Parallel LeftToRight) N2 n :: Type -> Type

-- | 'Diagram' for a equalizer. 
type EqualizerDiagram n = EqualizerDiagrammatic Diagram n

-- | 'Conic' object for a equalizer.
type EqualizerConic c (d :: DiagramType -> N' -> N' -> Type -> Type) (n :: N')
  = c Mlt Projective d (Parallel LeftToRight) N2 n :: Type -> Type

-- | 'Cone' for a equalizer.
type EqualizerCone n = EqualizerConic Cone Diagram n

-- | generic equalizer as 'LimesG'.
type EqualizerG c d n = LimesG c Mlt Projective d (Parallel LeftToRight) N2 n

-- | equalizer as 'Limes'.
type Equalizer n = EqualizerG Cone Diagram n

-- | generic equalizers for a 'Multiplicative' structures.
type EqualizersG c d n = LimitsG c Mlt Projective d (Parallel LeftToRight) N2 n

-- | equalizers for a 'Multiplicative' structures.
type Equalizers n = EqualizersG Cone Diagram n

--------------------------------------------------------------------------------
-- eqlProductDiagram -

-- | the underlying product diagram.
eqlProductDiagram :: EqualizerDiagram n x -> ProductDiagram N2 x
eqlProductDiagram (DiagramParallelLR p q _) = DiagramDiscrete (p:|q:|Nil)

--------------------------------------------------------------------------------
-- eqlProductCone -

-- | the underlying product cone.
eqlProductCone :: EqualizerCone n x -> ProductCone N2 x
eqlProductCone (ConeProjective d t cs) = ConeProjective (eqlProductDiagram d) t cs

--------------------------------------------------------------------------------
-- equalizers0 -

-- | the induced equalizers of zero parallel arrows.
equalizers0 :: Multiplicative x => Products N2 x -> Equalizers N0 x
equalizers0 prd2 = LimitsG (eql prd2) where
  eql :: Multiplicative x
    => Products N2 x -> EqualizerDiagram N0 x -> Equalizer N0 x
  eql prd2 d = LimesProjective l u where
    LimesProjective lPrd2 uPrd2 = limes prd2 (eqlProductDiagram d)
    l = ConeProjective d (tip lPrd2) (shell lPrd2)
    u = uPrd2 . eqlProductCone

--------------------------------------------------------------------------------
-- eqlHeadDiagram -

-- | the underlying minimum diagram given by the first arrow.
eqlHeadDiagram :: EqualizerDiagram (n+1) x -> MinimumDiagram From N1 x
eqlHeadDiagram (DiagramParallelLR p _ (a:|_)) = DiagramChainFrom p (a:|Nil)

--------------------------------------------------------------------------------
-- eqlHeadCone -

-- | the underlying minimum cone given by the first arrow.
eqlHeadCone :: EqualizerCone (n+1) x -> MinimumCone From N1 x
eqlHeadCone (ConeProjective d t cs) = ConeProjective (eqlHeadDiagram d) t cs

--------------------------------------------------------------------------------
-- equlizers1 -

-- | equalizers of one parallel arrow, i.e. 'Minima'.
equalizers1 :: Multiplicative x => Equalizers N1 x
equalizers1 = LimitsG eql where
  eql :: Multiplicative x => EqualizerDiagram N1 x -> Equalizer N1 x
  eql d = LimesProjective l u where
    LimesProjective lMin uMin = limes minimaFrom (eqlHeadDiagram d)  
    l = ConeProjective d (tip lMin) (shell lMin)
    u = uMin . eqlHeadCone

--------------------------------------------------------------------------------
-- equlizers2 -

-- | promoting equalizers.
--
-- ![image equalizer](c:/Users/zeric/haskell/oalg/src/OAlg/Limes/equalizer.jpg)
equalizers2 :: Multiplicative x => Equalizers N2 x -> Equalizers (n+2) x
equalizers2 eql2 = LimitsG (eql eql2) where
  eql :: (Multiplicative x, n ~ (n'+2))
      => Equalizers N2 x -> EqualizerDiagram n x -> Equalizer n x
  eql eql2 d@(DiagramParallelLR _ _ (_:|_:|Nil))        = limes eql2 d
  eql eql2 d@(DiagramParallelLR p q (a0:|aN@(_:|_:|_))) = LimesProjective l u where
    dN = DiagramParallelLR p q aN
    LimesProjective (ConeProjective _ h (h0:|h1:|Nil)) uN = eql eql2 dN

    d2 = DiagramParallelLR h q (a0*h0:|h1:|Nil)
    LimesProjective (ConeProjective _ k (k0:|k1:|Nil)) u2 = limes eql2 d2
    
    l = ConeProjective d k (h0*k0:|k1:|Nil)
    u (ConeProjective _ x (x0:|x1:|Nil)) = uk where
      uk = u2 (ConeProjective d2 x (uh:|x1:|Nil))
      uh = uN (ConeProjective dN x (x0:|x1:|Nil))

--------------------------------------------------------------------------------
-- equlizers -

-- | equalizers of @n@ arrows given by products of two points and equalizers of two arrows.
equalizers :: Multiplicative x => Products N2 x -> Equalizers N2 x -> Equalizers n x
equalizers prd2 eql2 = LimitsG (eql prd2 eql2) where
  eql :: Multiplicative x
      => Products N2 x -> Equalizers N2 x -> EqualizerDiagram n x -> Equalizer n x
  eql prd2 eql2 d = case dgArrows d of
    Nil      -> limes (equalizers0 prd2) d
    _:|Nil   -> limes equalizers1 d
    _:|_:|_  -> limes (equalizers2 eql2) d 

--------------------------------------------------------------------------------
-- equlizersOrnt -

-- | equalizers for 'Orientation' 
equalizersOrnt :: Entity p => p -> Equalizers n (Orientation p)
equalizersOrnt = lmsMltPrjOrnt

--------------------------------------------------------------------------------
-- Coequalizers -

-- | 'Diagrammatic' object for a coequalizer. 
type CoequalizerDiagrammatic d (n :: N') = d (Parallel RightToLeft) N2 n :: Type -> Type

-- | 'Diagram' for a coequalizer. 
type CoequalizerDiagram n = CoequalizerDiagrammatic Diagram n

-- | 'Conic' object for a coequalizer.
type CoequalizerConic c (d :: DiagramType -> N' -> N' -> Type -> Type) (n :: N')
  = c Mlt Injective d (Parallel RightToLeft) N2 n :: Type -> Type

-- | 'Cone' for a coequalizer.
type CoequalizerCone n = CoequalizerConic Cone Diagram n

-- | generic coequalizer as 'LimesG'.
type CoequalizerG c d n = LimesG c Mlt Injective d (Parallel RightToLeft) N2 n

-- | coequalizer as 'Limes'.
type Coequalizer n = CoequalizerG Cone Diagram n

-- | generic coequalizers for a 'Multiplicative' structures.
type CoequalizersG c d n = LimitsG c Mlt Injective d (Parallel RightToLeft) N2 n

-- | coequalizers for a 'Multiplicative' structures.
type Coequalizers n = CoequalizersG Cone Diagram n

--------------------------------------------------------------------------------
-- coequalizers -

-- | coequalizers of @n@ arrows given by sums of two points and coequalizers of two arrows.
coequalizers :: Multiplicative x => Sums N2 x -> Coequalizers N2 x -> Coequalizers n x
coequalizers sum2 coeql2 = coeqls where
  Contravariant2 i = toDualOpMlt

  SDualBi (Left1 prd2)    = amapF i (SDualBi (Right1 sum2))
  SDualBi (Left1 eql2)    = amapF i (SDualBi (Right1 coeql2))
  eqls                    = equalizers prd2 eql2
  SDualBi (Right1 coeqls) = amapF (inv2 i) (SDualBi (Left1 eqls))

-- | 'coequalizers' given by a proxy for @n@.
coequalizers' :: Multiplicative x
  => p n -> Sums N2 x -> Coequalizers N2 x -> Coequalizers n x
coequalizers' _ = coequalizers

--------------------------------------------------------------------------------
-- coequalizersOrnt -

-- | coequalizers for 'Orientation'.
coequalizersOrnt :: Entity p => p -> Coequalizers n (Orientation p)
coequalizersOrnt = lmsMltInjOrnt
