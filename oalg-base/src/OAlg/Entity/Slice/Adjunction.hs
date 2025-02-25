
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Slice.Adjunction
-- Description : cokernel-kernel adjunction
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'Cokernel'-'Kernel' 'Adjunction' for 'Slice'd structures. 
module OAlg.Entity.Slice.Adjunction
  ( -- * Adjunction
    slcAdjunction

    -- ** Homomorphism
  , SliceCokernelKernel(..)
  , SliceCokernelTo(..)
  , SliceKernelFrom(..)

    -- ** Unit
  , slcCokerKer, slcKerCoker
  
    -- * X
  , xSliceFactorTo, xSliceFactorFrom
  
    -- * Proposition
  , prpHomMltSliceCokernelKernel
  ) where

import Control.Monad
import Control.Applicative ((<|>))

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Unify

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone
import OAlg.Limes.Universal
import OAlg.Limes.KernelsAndCokernels

import OAlg.Adjunction

import OAlg.Entity.Natural
import OAlg.Entity.Slice.Definition
import OAlg.Entity.Slice.Sliced

--------------------------------------------------------------------------------
-- SliceCokernelKernel -

-- | the left and right homomorphisms for the cokernel-kernel adjunction 'slcAdjunction'.
data SliceCokernelKernel i c x y where  
  SliceCokernel :: SliceCokernelKernel i c (SliceFactor To i c) (SliceFactor From i c)
  SliceKernel   :: SliceCokernelKernel i c (SliceFactor From i c) (SliceFactor To i c) 

--------------------------------------------------------------------------------
-- SliceCokernelKernel - Entity -

deriving instance Show (SliceCokernelKernel i c x y)
instance Show2 (SliceCokernelKernel i c)

deriving instance Eq (SliceCokernelKernel i c x y)
instance Eq2 (SliceCokernelKernel i c)

instance Validable (SliceCokernelKernel i c x y) where
  valid SliceCokernel = SValid
  valid SliceKernel   = SValid
instance Validable2 (SliceCokernelKernel i c)


instance (Typeable i, Typeable c, Typeable x, Typeable y)
  => Entity (SliceCokernelKernel i c x y)
instance (Typeable i, Typeable c) => Entity2 (SliceCokernelKernel i c)

--------------------------------------------------------------------------------
-- SliceCokernelTo -

-- | 'Distributive' structures @__c__@ having to each @'Slice' 'To' __i__ __c__@ a
--   'Cokernel'.
--
--  __Property__ Let @h = 'SliceTo' _ h'@ be in @'Slice' 'To' __i__ __c__@ for a
--  @__i__@ sliced, 'Distributive' structure @__c__@, then holds:
--
--  @'diagram' ('universalCone' coker) '==' 'cokernelDiagram' h'@ where
--  @coker = 'sliceCokernelTo' h@.
class (Distributive c, Sliced i c) => SliceCokernelTo i c where
  sliceCokernelTo :: Slice To i c -> Cokernel N1 c

--------------------------------------------------------------------------------
-- SliceKernelFrom -

-- | 'Distributive' structures @__c__@ having to each @'Slice' 'From' __i__ __c__@ a
--   'Kernel'.
--
--  __Property__ Let @h = 'SliceFrom' _ h'@ be in @'Slice' 'From' __i__ __c__@ for a
--  @__i__@ sliced, 'Distributive' structure @__c__@, then holds:
--
--  @'diagram' ('universalCone' ker) '==' 'kernelDiagram' h'@ where
--  @coker = 'sliceKernelFrom' h@.
class (Distributive c, Sliced i c) => SliceKernelFrom i c where
  sliceKernelFrom :: Slice From i c -> Kernel N1 c

--------------------------------------------------------------------------------
-- SliceCokernelKernel - Morphism -

instance (Multiplicative c, Sliced i c) => Morphism (SliceCokernelKernel i c) where
  type ObjectClass (SliceCokernelKernel i c) = Mlt
  homomorphous SliceCokernel = Struct :>: Struct
  homomorphous SliceKernel = Struct :>: Struct

instance TransformableObjectClassTyp (SliceCokernelKernel i c)

--------------------------------------------------------------------------------
-- SliceCokernelKernel - HomMultiplicative -

instance (Distributive c, SliceCokernelTo i c, SliceKernelFrom i c)
  => Applicative (SliceCokernelKernel i c) where
  
  amap SliceCokernel (SliceFactor a@(SliceTo k _) b _)
    = SliceFactor (SliceFrom k a') (SliceFrom k b') f' where
    aCoker = sliceCokernelTo a
    a' = cokernelFactor $ universalCone aCoker
    b' = cokernelFactor $ universalCone $ sliceCokernelTo b
    f' = universalFactor aCoker (ConeCokernel (diagram aCoker) b')
    -- from SliceFactor a b f valid follwos that
    -- ConeCokernel (diagram aCoker) b' is eligible

  amap SliceKernel (SliceFactor a@(SliceFrom k _) b _)
    = SliceFactor (SliceTo k a') (SliceTo k b') f' where
    bKer = sliceKernelFrom b
    a' = kernelFactor $ universalCone $ sliceKernelFrom a
    b' = kernelFactor $ universalCone $ bKer
    f' = universalFactor bKer (ConeKernel (diagram bKer) a')
    -- from SliceFactor a b f valid follows that ConeKernel (diagram bKer) a' is eligible

instance (Distributive c, SliceCokernelTo i c, SliceKernelFrom i c)
  => HomOriented (SliceCokernelKernel i c) where
  pmap SliceCokernel a@(SliceTo k _) = SliceFrom k a' where
    a' = cokernelFactor $ universalCone $ sliceCokernelTo a
  pmap SliceKernel a@(SliceFrom k _) = SliceTo k a' where
    a' = kernelFactor $ universalCone $ sliceKernelFrom a

instance (Distributive c, SliceCokernelTo i c, SliceKernelFrom i c)
  => HomMultiplicative (SliceCokernelKernel i c)

--------------------------------------------------------------------------------
-- xSliceFactorTo -

-- | random variable for @'SliceFactor' 'To' __i__ __c__@.
xSliceFactorTo :: (Multiplicative c, Sliced i c)
  => XOrtSite To c -> i c -> X (SliceFactor To i c)
xSliceFactorTo (XEnd _ xTo) i = do
  a <- xTo p
  f <- xTo (start a)
  return (SliceFactor (SliceTo i (a*f)) (SliceTo i a) f)
  
  where p = slicePoint i

--------------------------------------------------------------------------------
-- xSliceFactorFrom -

-- | random variable for @'SliceFactor' 'From' __i__ __c__@.
xSliceFactorFrom :: (Multiplicative c, Sliced i c)
  => XOrtSite From c -> i c -> X (SliceFactor From i c)
xSliceFactorFrom (XStart _ xFrom) i = do
  a <- xFrom p
  f <- xFrom (end a)
  return (SliceFactor (SliceFrom i a) (SliceFrom i (f*a)) f)
  
  where p = slicePoint i

--------------------------------------------------------------------------------
-- prpHomOrtSliceCokernelKernel -

-- | validity for the values of 'SliceCokernelKernel' to be 'HomOriented'.
prpHomOrtSliceCokernelKernel
  :: (SliceCokernelTo i c, SliceKernelFrom i c)
  => XOrtSite To c
  -> XOrtSite From c
  -> i c
  -> Statement
prpHomOrtSliceCokernelKernel xTo xFrom i = Prp "HomOrtSliceCokernelKernel"
  :<=>: prpHomOrt (xSliceCokernel xTo i <|> xSliceKernel xFrom i) where
  
  xSliceCokernel :: (Multiplicative c, Sliced i c)
    => XOrtSite To c -> i c -> XHomOrt (SliceCokernelKernel i c)
  xSliceCokernel xTo i = amap1 (SomeApplication SliceCokernel) $ xSliceFactorTo xTo i

  xSliceKernel :: (Multiplicative c, Sliced i c)
    => XOrtSite From c -> i c -> XHomOrt (SliceCokernelKernel i c)
  xSliceKernel xFrom i = amap1 (SomeApplication SliceKernel) $ xSliceFactorFrom xFrom i

--------------------------------------------------------------------------------
-- prpHomMltSliceCokernelKernel -

-- | validity for the values of 'SliceCokernelKernel' to be 'HomMultiplicative'.
prpHomMltSliceCokernelKernel
  :: (SliceCokernelTo i c, SliceKernelFrom i c)
  => XOrtSite To c
  -> XOrtSite From c
  -> i c
  -> Statement
prpHomMltSliceCokernelKernel xTo xFrom i = Prp "HomMltSliceCokernelKernel"
  :<=>: prpHomMlt (xHomMltKernelCokernel xTo xFrom i) where

  xHomMltKernelCokernel :: (Multiplicative c, Sliced i c)
    => XOrtSite To c -> XOrtSite From c -> i c -> XHomMlt (SliceCokernelKernel i c)
  xHomMltKernelCokernel xTo xFrom i
    = XHomMlt (xpCoker <|> xpKer) (xm2Coker <|> xm2Ker) where
    XHomMlt xpCoker xm2Coker = xHomMltCokernel xTo i
    XHomMlt xpKer xm2Ker = xHomMltKernel xFrom i
  
  xHomMltCokernel :: (Multiplicative c, Sliced i c)
    => XOrtSite To c -> i c -> XHomMlt (SliceCokernelKernel i c)
  xHomMltCokernel xTo i = XHomMlt xApplPnt xApplMltp2 where
    xApplPnt = amap1 (SomeApplPnt SliceCokernel) $ xSliceTo xTo i
    xApplMltp2 = amap1 (SomeApplMltp2 SliceCokernel)
               $ xMltp2
               $ xosXOrtSiteToSliceFactorTo xTo i

  xHomMltKernel :: (Multiplicative c, Sliced i c)
    => XOrtSite From c -> i c -> XHomMlt (SliceCokernelKernel i c)
  xHomMltKernel xFrom i = XHomMlt xApplPnt xApplMltp2 where
    xApplPnt = amap1 (SomeApplPnt SliceKernel) $ xSliceFrom xFrom i
    xApplMltp2 = amap1 (SomeApplMltp2 SliceKernel)
               $ xMltp2
               $ xosXOrtSiteFromSliceFactorFrom xFrom i
  
--------------------------------------------------------------------------------
-- slcCokerKer -

-- | the right unit of the cokernel-kernel adjunction 'slcAdjunction'.
slcCokerKer :: (SliceCokernelTo i c, SliceKernelFrom i c)
    => Slice To i c -> SliceFactor To i c 
slcCokerKer a@(SliceTo i a') = SliceFactor a (SliceTo i k) u where
  aCokerKer = sliceKernelFrom (pmap SliceCokernel a)
  k = kernelFactor $ universalCone aCokerKer
  u = universalFactor aCokerKer (ConeKernel (diagram aCokerKer) a') 

--------------------------------------------------------------------------------
-- slcKerCoker -

-- | the left unit of the cokernel-kenrel adjunction 'slcAdjunction'.
slcKerCoker :: (SliceCokernelTo i c, SliceKernelFrom i c)
  => Slice From i c -> SliceFactor From i c
slcKerCoker a@(SliceFrom i a') = SliceFactor (SliceFrom i c) a v where
  aKerCoker = sliceCokernelTo (pmap SliceKernel a)
  c = cokernelFactor $ universalCone aKerCoker
  v = universalFactor aKerCoker (ConeCokernel (diagram aKerCoker) a')

--------------------------------------------------------------------------------
-- slcAdjunction -

-- | the cokernel-kenrel adjunction.
slcAdjunction :: (SliceCokernelTo i c, SliceKernelFrom i c)
  => i c
  -> Adjunction (SliceCokernelKernel i c) (SliceFactor From i c) (SliceFactor To i c)
slcAdjunction _ = Adjunction l r u v where
  l = SliceCokernel
  r = SliceKernel
  u = slcCokerKer
  v = slcKerCoker

