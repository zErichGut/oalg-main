
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
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
    Equalizers, GenericEqualizers, Equalizer, EqualizerCone, EqualizerDiagram

    -- ** Construction
  , equalizers, equalizers0, equalizers1, equalizers2

    -- *** Orientation
  , equalizersOrnt

    -- * Coequalizers
  , Coequalizers, GenericCoequalizers, Coequalizer, CoequalizerCone, CoequalizerDiagram

    -- ** Construction
  , coequalizers, coequalizers'

    -- *** Orientation
  , coequalizersOrnt

    -- * Duality
  , coeqlLimitsDuality

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
import OAlg.Limes.OpDuality
import OAlg.Limes.Definition
import OAlg.Limes.Limits

import OAlg.Limes.MinimaAndMaxima
import OAlg.Limes.ProductsAndSums

--------------------------------------------------------------------------------
-- Equalizers -

-- | 'Diagram' for a equalizer. 
type EqualizerDiagram n = Diagram (Parallel LeftToRight) N2 n

-- | 'Cone' for a equalizer.
type EqualizerCone n = Cone Mlt Projective (Parallel LeftToRight) N2 n

-- | equalizer as 'Limes'.
type Equalizer n = Limes Mlt Projective (Parallel LeftToRight) N2 n

-- | generic equalizers for a 'Multiplicative' structures.
type GenericEqualizers l n = Limits l Mlt Projective (Parallel LeftToRight) N2 n

-- | equalizers for a 'Multiplicative' structures.
type Equalizers n = GenericEqualizers Limes n


--------------------------------------------------------------------------------
-- eqlProductDiagram -

-- | the underlying product diagram.
eqlProductDiagram :: EqualizerDiagram n a -> ProductDiagram N2 a
eqlProductDiagram (DiagramParallelLR p q _) = DiagramDiscrete (p:|q:|Nil)

--------------------------------------------------------------------------------
-- eqlProductCone -

-- | the underlying product cone.
eqlProductCone :: EqualizerCone n a -> ProductCone N2 a
eqlProductCone (ConeProjective d t cs) = ConeProjective (eqlProductDiagram d) t cs

--------------------------------------------------------------------------------
-- equalizers0 -

-- | the induced equalizers of zero parallel arrows.
equalizers0 :: Multiplicative a => Products N2 a -> Equalizers N0 a
equalizers0 prd2 = Limits (eql prd2) where
  eql :: Multiplicative a
    => Products N2 a -> EqualizerDiagram N0 a -> Equalizer N0 a
  eql prd2 d = LimesProjective l u where
    LimesProjective lPrd2 uPrd2 = limes prd2 (eqlProductDiagram d)
    l = ConeProjective d (tip lPrd2) (shell lPrd2)
    u = uPrd2 . eqlProductCone

--------------------------------------------------------------------------------
-- eqlHeadDiagram -

-- | the underlying minimum diagram given by the first arrow.
eqlHeadDiagram :: EqualizerDiagram (n+1) a -> MinimumDiagram From N1 a
eqlHeadDiagram (DiagramParallelLR p _ (a:|_)) = DiagramChainFrom p (a:|Nil)

--------------------------------------------------------------------------------
-- eqlHeadCone -

-- | the underlying minimum cone given by the first arrow.
eqlHeadCone :: EqualizerCone (n+1) a -> MinimumCone From N1 a
eqlHeadCone (ConeProjective d t cs) = ConeProjective (eqlHeadDiagram d) t cs

--------------------------------------------------------------------------------
-- equlizers1 -

-- | equalizers of one parallel arrow, i.e. 'Minima'.
equalizers1 :: Multiplicative a => Equalizers N1 a
equalizers1 = Limits eql where
  eql :: Multiplicative a => EqualizerDiagram N1 a -> Equalizer N1 a
  eql d = LimesProjective l u where
    LimesProjective lMin uMin = limes minimaFrom (eqlHeadDiagram d)  
    l = ConeProjective d (tip lMin) (shell lMin)
    u = uMin . eqlHeadCone

--------------------------------------------------------------------------------
-- equlizers2 -

-- | promoting equalizers.
--
-- ![image equalizer](c:/Users/zeric/haskell/oalg/src/OAlg/Limes/equalizer.jpg)
equalizers2 :: Multiplicative a => Equalizers N2 a -> Equalizers (n+2) a
equalizers2 eql2 = Limits (eql eql2) where
  eql :: (Multiplicative a, n ~ (n'+2))
      => Equalizers N2 a -> EqualizerDiagram n a -> Equalizer n a
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
equalizers :: Multiplicative a => Products N2 a -> Equalizers N2 a -> Equalizers n a
equalizers prd2 eql2 = Limits (eql prd2 eql2) where
  eql :: Multiplicative a
      => Products N2 a -> Equalizers N2 a -> EqualizerDiagram n a -> Equalizer n a
  eql prd2 eql2 d = case dgArrows d of
    Nil      -> limes (equalizers0 prd2) d
    _:|Nil   -> limes equalizers1 d
    _:|_:|_  -> limes (equalizers2 eql2) d 

--------------------------------------------------------------------------------
-- equlizersOrnt -

-- | equalizers for 'Orientation' 
equalizersOrnt :: Entity p => p -> Equalizers n (Orientation p)
equalizersOrnt = lmsToPrjOrnt

--------------------------------------------------------------------------------
-- Coequalizers -

-- | 'Diagram' for a coequalizer.
type CoequalizerDiagram n = Diagram (Parallel RightToLeft) N2 n

-- | 'Cone' for a coequalizer.
type CoequalizerCone n = Cone Mlt Injective (Parallel RightToLeft) N2 n

-- | coequalizer as 'Limes.
type Coequalizer n = Limes Mlt Injective (Parallel RightToLeft) N2 n

-- | generic coequalizers for a 'Multiplicative' structure.
type GenericCoequalizers l n = Limits l Mlt Injective (Parallel RightToLeft) N2 n

-- | coequalizers for a 'Multiplicative' structure.
type Coequalizers n = GenericCoequalizers Limes n

--------------------------------------------------------------------------------
-- Coequalizer - Duality -

-- | duality between coequalizers and equalizers.
coeqlLimitsDuality :: OpDuality (Limits Limes) Mlt (Coequalizers n) (Equalizers n)
coeqlLimitsDuality = OpDuality Refl Refl

--------------------------------------------------------------------------------
-- coequalizers -

-- | coequalizers of @n@ arrows given by sums of two points and coequalizers of two arrows.
coequalizers :: Multiplicative a => Sums N2 a -> Coequalizers N2 a -> Coequalizers n a
coequalizers sum2 coeql2 = lmsFromOp ConeStructMlt coeqlLimitsDuality $ equalizers prd2 eql2 where
  prd2 = lmsToOp ConeStructMlt sumLimitsDuality sum2
  eql2 = lmsToOp ConeStructMlt coeqlLimitsDuality coeql2

-- | 'coequalizers' given by a proxy for @n@.
coequalizers' :: Multiplicative a
  => p n -> Sums N2 a -> Coequalizers N2 a -> Coequalizers n a
coequalizers' _ = coequalizers

--------------------------------------------------------------------------------
-- coequalizersOrnt -

-- | coequalizers for 'Orientation'.
coequalizersOrnt :: Entity p => p -> Coequalizers n (Orientation p)
coequalizersOrnt = lmsFromInjOrnt


