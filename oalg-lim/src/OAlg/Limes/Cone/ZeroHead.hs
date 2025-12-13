
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.ZeroHead
-- Description : cones with a zero arrow. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- cones having a zero for its first arrow.
module OAlg.Limes.Cone.ZeroHead
  (
    ConeZeroHead(..)
  , cnZeroHead
  , cnKernel, cnCokernel
  , cnDiffHead

    -- * Duality
  , module Dl
    
  ) where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Fibred
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Distributive

import OAlg.Limes.Perspective

import OAlg.Limes.Cone.Definition

import OAlg.Limes.Cone.ZeroHead.Core
import OAlg.Limes.Cone.ZeroHead.Duality as Dl

--------------------------------------------------------------------------------
-- cnDiffHead -

-- | subtracts to every arrow of the underlying parallel diagram the first arrow and
-- adapts the shell accordingly.
cnDiffHead :: (Distributive a, Abelian a)
  => Cone Mlt p Diagram (Parallel d) n (m+1) a -> ConeZeroHead Mlt p Diagram (Parallel d) n (m+1) a
cnDiffHead (ConeProjective d t s) = ConeZeroHead $ case d of
  DiagramParallelLR _ _ _ -> ConeProjective (dgPrlDiffHead d) t (a:|amap1 toZero as) where a:|as = s
  DiagramParallelRL _ _ _ -> ConeProjective (dgPrlDiffHead d) t (toZero a:|as) where a:|as = s
  
  where toZero a = zero (root a)

cnDiffHead c@(ConeInjective (DiagramParallelLR _ _ _) _ _) = cz where
  Contravariant2 (Inv2 t f) = toDualOpDst
  SDualBi (Left1 c')  = amapF t (SDualBi (Right1 c))
  cz'                 = cnDiffHead c'
  SDualBi (Right1 cz) = amapF f (SDualBi (Left1 cz'))
cnDiffHead c@(ConeInjective (DiagramParallelRL _ _ _) _ _) = cz where
  Contravariant2 (Inv2 t f) = toDualOpDst
  SDualBi (Left1 c')  = amapF t (SDualBi (Right1 c))
  cz'                 = cnDiffHead c'
  SDualBi (Right1 cz) = amapF f (SDualBi (Left1 cz'))

--------------------------------------------------------------------------------
-- cnZeroHead -

-- | embedding of a cone in a distributive structure to its multiplicative cone.
cnZeroHead :: Cone Dst p Diagram t n m a -> ConeZeroHead Mlt p Diagram t n (m+1) a
cnZeroHead c@(ConeKernel _ _)   = ConeZeroHead (cnDstAdjZero c)
cnZeroHead c@(ConeCokernel _ _) = ConeZeroHead (cnDstAdjZero c)

--------------------------------------------------------------------------------
-- cnKernel -

-- | the kernel cone of a zero headed parallel cone, i.e. the inverse of 'cnZeroHead'.
cnKernel :: (p ~ Projective, t ~ Parallel LeftToRight)
  => ConeZeroHead Mlt p Diagram t n (m+1) a -> Cone Dst p Diagram t n m a
cnKernel (ConeZeroHead (ConeProjective d _ cs)) = case d of
  DiagramParallelLR l r as -> ConeKernel (DiagramParallelLR l r (tail as)) (head cs)

--------------------------------------------------------------------------------
-- cnCokernel

-- | the cokernel cone of a zero headed parallel cone, i.e. the inverse of 'cnZeroHead'.
cnCokernel :: (p ~ Injective, t ~ Parallel RightToLeft, n ~ N2)
  => ConeZeroHead Mlt p Diagram t n (m+1) a -> Cone Dst p Diagram t n m a
cnCokernel cz@(ConeZeroHead _) = c where
  Contravariant2 (Inv2 t f) = toDualOpDst

  SDualBi (Left1 cz') = amapF t (SDualBi (Right1 cz))
  c'                  = cnKernel cz'
  SDualBi (Right1 c)  = amapF f (SDualBi (Left1 c'))


