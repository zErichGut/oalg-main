
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
  (
    -- * Adjunction
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

import Data.Kind
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

import OAlg.Entity.Diagram.Definition
import OAlg.Entity.Natural
import OAlg.Entity.Slice.Definition
import OAlg.Entity.Slice.Sliced

--------------------------------------------------------------------------------
-- SliceCokernelKernel -

-- | the left and right homomorphisms for the cokernel-kernel adjunction 'slcAdjunction' within
-- a 'Distributive' structure @__d__@.
data SliceCokernelKernel
       (c :: Type -> Perspective -> DiagramType -> N' -> N' -> Type -> Type)
       (k :: Type -> Perspective -> DiagramType -> N' -> N' -> Type -> Type)
       i d x y where  
  SliceCokernel :: SliceCokernelKernel c k i d (SliceFactor To i d) (SliceFactor From i d)
  SliceKernel   :: SliceCokernelKernel c k i d (SliceFactor From i d) (SliceFactor To i d) 

--------------------------------------------------------------------------------
-- SliceCokernelKernel - Entity -

deriving instance Show (SliceCokernelKernel c k i d x y)
instance Show2 (SliceCokernelKernel c k i d)

deriving instance Eq (SliceCokernelKernel c k i d x y)
instance Eq2 (SliceCokernelKernel c k i d)

instance Validable (SliceCokernelKernel c k i d x y) where
  valid SliceCokernel = SValid
  valid SliceKernel   = SValid
instance Validable2 (SliceCokernelKernel c k i d)


instance (Typeable c, Typeable k, Typeable i, Typeable d, Typeable x, Typeable y)
  => Entity (SliceCokernelKernel c k i d x y)
instance (Typeable c, Typeable k, Typeable i, Typeable d) => Entity2 (SliceCokernelKernel c k i d)

--------------------------------------------------------------------------------
-- SliceCokernelTo -

-- | 'Distributive' structures @__d__@ having for each @'Slice' 'To' __i__ __d__@ a
--   'GenericCokernel'.
--
--  __Property__ Let @h = 'SliceTo' _ h'@ be in @'Slice' 'To' __i__ __d__@ for a
--  @__i__@ sliced, 'Distributive' structure @__d__@, then holds:
--
--  @'diagram' ('universalCone' coker) '==' 'cokernelDiagram' h'@ where
--  @coker = 'sliceCokernelTo' h@.
class (Distributive d, Sliced i d) => SliceCokernelTo c i d where
  sliceCokernelTo :: Slice To i d -> GenericCokernel c N1 d

sliceCokernelTo' :: SliceCokernelTo c i d
  => SliceCokernelKernel c k i d (SliceFactor To i d) (SliceFactor From i d)
  -> Slice To i d -> GenericCokernel c N1 d
sliceCokernelTo' SliceCokernel = sliceCokernelTo

--------------------------------------------------------------------------------
-- SliceKernelFrom -

-- | 'Distributive' structures @__d__@ having for each @'Slice' 'From' __i__ __d__@ a
--   'GenericKernel'.
--
--  __Property__ Let @h = 'SliceFrom' _ h'@ be in @'Slice' 'From' __i__ __d__@ for a
--  @__i__@ sliced, 'Distributive' structure @__c__@, then holds:
--
--  @'diagram' ('universalCone' ker) '==' 'kernelDiagram' h'@ where
--  @coker = 'sliceKernelFrom' h@.
class (Distributive d, Sliced i d) => SliceKernelFrom k i d where
  sliceKernelFrom :: Slice From i d -> GenericKernel k N1 d

sliceKernelFrom' :: SliceKernelFrom k i d
  => SliceCokernelKernel c k i d (SliceFactor From i d) (SliceFactor To i d)
  -> Slice From i d -> GenericKernel k N1 d
sliceKernelFrom' SliceKernel = sliceKernelFrom

--------------------------------------------------------------------------------
-- SliceCokernelKernel - Morphism -

instance (Multiplicative d, Sliced i d) => Morphism (SliceCokernelKernel c k i d) where
  type ObjectClass (SliceCokernelKernel c k i d) = Mlt
  homomorphous SliceCokernel = Struct :>: Struct
  homomorphous SliceKernel = Struct :>: Struct

instance TransformableObjectClassTyp (SliceCokernelKernel c k i d)

--------------------------------------------------------------------------------
-- SliceCokernelKernel - HomMultiplicative -

instance ( Distributive d
         , Universal c, SliceCokernelTo c i d
         , Universal k, SliceKernelFrom k i d
         )
  => Applicative (SliceCokernelKernel c k i d) where

  amap s@SliceCokernel (SliceFactor a@(SliceTo k _) b _)
    = SliceFactor (SliceFrom k a') (SliceFrom k b') f' where
    aCoker = sliceCokernelTo' s a
    a' = cokernelFactor $ universalCone aCoker
    b' = cokernelFactor $ universalCone $ sliceCokernelTo' s b
    f' = universalFactor aCoker (ConeCokernel (diagram aCoker) b')
    -- from SliceFactor a b f valid follwos that
    -- ConeCokernel (diagram aCoker) b' is eligible

  amap s@SliceKernel (SliceFactor a@(SliceFrom k _) b _)
    = SliceFactor (SliceTo k a') (SliceTo k b') f' where
    bKer = sliceKernelFrom' s b
    a' = kernelFactor $ universalCone $ sliceKernelFrom' s a
    b' = kernelFactor $ universalCone $ bKer
    f' = universalFactor bKer (ConeKernel (diagram bKer) a')
    -- from SliceFactor a b f valid follows that ConeKernel (diagram bKer) a' is eligible

instance ( Distributive d
         , Universal c, SliceCokernelTo c i d
         , Universal k, SliceKernelFrom k i d
         )
  => HomOriented (SliceCokernelKernel c k i d) where
  pmap s@SliceCokernel a@(SliceTo k _) = SliceFrom k a' where
    a' = cokernelFactor $ universalCone $ sliceCokernelTo' s a
  pmap s@SliceKernel a@(SliceFrom k _) = SliceTo k a' where
    a' = kernelFactor $ universalCone $ sliceKernelFrom' s a

instance ( Distributive d
         , Universal c, SliceCokernelTo c i d
         , Universal k, SliceKernelFrom k i d
         )
  => HomMultiplicative (SliceCokernelKernel c k i d)

--------------------------------------------------------------------------------
-- xSliceFactorTo -

-- | random variable for @'SliceFactor' 'To' __i__ __d__@.
xSliceFactorTo :: (Multiplicative d, Sliced i d)
  => XOrtSite To d -> i d -> X (SliceFactor To i d)
xSliceFactorTo (XEnd _ xTo) i = do
  a <- xTo p
  f <- xTo (start a)
  return (SliceFactor (SliceTo i (a*f)) (SliceTo i a) f)
  
  where p = slicePoint i

--------------------------------------------------------------------------------
-- xSliceFactorFrom -

-- | random variable for @'SliceFactor' 'From' __i__ __d__@.
xSliceFactorFrom :: (Multiplicative d, Sliced i d)
  => XOrtSite From d -> i d -> X (SliceFactor From i d)
xSliceFactorFrom (XStart _ xFrom) i = do
  a <- xFrom p
  f <- xFrom (end a)
  return (SliceFactor (SliceFrom i a) (SliceFrom i (f*a)) f)
  
  where p = slicePoint i

--------------------------------------------------------------------------------
-- prpHomOrtSliceCokernelKernel -

-- | validity for the values of 'SliceCokernelKernel' to be 'HomOriented'.
prpHomOrtSliceCokernelKernel
  :: (Universal c, SliceCokernelTo c i d, Universal k, SliceKernelFrom k i d)
  => Proxy c
  -> Proxy k
  -> XOrtSite To d
  -> XOrtSite From d
  -> i d
  -> Statement
prpHomOrtSliceCokernelKernel c k xTo xFrom i = Prp "HomOrtSliceCokernelKernel"
  :<=>: prpHomOrt (xSliceCokernel c k xTo i <|> xSliceKernel c k xFrom i) where
  
  xSliceCokernel :: (Multiplicative d, Sliced i d)
    => Proxy c -> Proxy k -> XOrtSite To d -> i d -> XHomOrt (SliceCokernelKernel c k i d)
  xSliceCokernel _ _ xTo i = amap1 (SomeApplication SliceCokernel) $ xSliceFactorTo xTo i

  xSliceKernel :: (Multiplicative d, Sliced i d)
    => Proxy c -> Proxy k -> XOrtSite From d -> i d -> XHomOrt (SliceCokernelKernel c k i d)
  xSliceKernel _ _ xFrom i = amap1 (SomeApplication SliceKernel) $ xSliceFactorFrom xFrom i

--------------------------------------------------------------------------------
-- prpHomMltSliceCokernelKernel -

-- | validity for the values of 'SliceCokernelKernel' to be 'HomMultiplicative'.
prpHomMltSliceCokernelKernel
  :: (Universal c, SliceCokernelTo c i d, Universal k, SliceKernelFrom k i d)
  => Proxy c
  -> Proxy k
  -> XOrtSite To d
  -> XOrtSite From d
  -> i d
  -> Statement
prpHomMltSliceCokernelKernel c k xTo xFrom i = Prp "HomMltSliceCokernelKernel"
  :<=>: prpHomMlt (xHomMltKernelCokernel c k xTo xFrom i) where

  xHomMltKernelCokernel :: (Multiplicative d, Sliced i d)
    => Proxy c -> Proxy k
    -> XOrtSite To d -> XOrtSite From d -> i d -> XHomMlt (SliceCokernelKernel c k i d)
  xHomMltKernelCokernel c k xTo xFrom i
    = XHomMlt (xpCoker <|> xpKer) (xm2Coker <|> xm2Ker) where
    XHomMlt xpCoker xm2Coker = xHomMltCokernel c k xTo i
    XHomMlt xpKer xm2Ker = xHomMltKernel c k xFrom i
  
  xHomMltCokernel :: (Multiplicative d, Sliced i d)
    => Proxy c -> Proxy k
    -> XOrtSite To d -> i d -> XHomMlt (SliceCokernelKernel c k i d)
  xHomMltCokernel _ _ xTo i = XHomMlt xApplPnt xApplMltp2 where
    xApplPnt = amap1 (SomeApplPnt SliceCokernel) $ xSliceTo xTo i
    xApplMltp2 = amap1 (SomeApplMltp2 SliceCokernel)
               $ xMltp2
               $ xosXOrtSiteToSliceFactorTo xTo i

  xHomMltKernel :: (Multiplicative d, Sliced i d)
    => Proxy c -> Proxy k
    -> XOrtSite From d -> i d -> XHomMlt (SliceCokernelKernel c k i d)
  xHomMltKernel _ _ xFrom i = XHomMlt xApplPnt xApplMltp2 where
    xApplPnt = amap1 (SomeApplPnt SliceKernel) $ xSliceFrom xFrom i
    xApplMltp2 = amap1 (SomeApplMltp2 SliceKernel)
               $ xMltp2
               $ xosXOrtSiteFromSliceFactorFrom xFrom i

slcCokernel :: Proxy c -> Proxy k -> Slice To i d
  -> SliceCokernelKernel c k i d (SliceFactor To i d) (SliceFactor From i d)
slcCokernel _ _ _ = SliceCokernel

slcKernel :: Proxy c -> Proxy k -> Slice From i d
  -> SliceCokernelKernel c k i d (SliceFactor From i d) (SliceFactor To i d) 
slcKernel _ _ _ = SliceKernel

--------------------------------------------------------------------------------
-- slcCokerKer -

-- | the right unit of the cokernel-kernel adjunction 'slcAdjunction'.
slcCokerKer :: (Universal c, SliceCokernelTo c i d, Universal k, SliceKernelFrom k i d)
  => Proxy c
  -> Proxy k
  -> Slice To i d -> SliceFactor To i d 
slcCokerKer c k a@(SliceTo i a') = SliceFactor a (SliceTo i b') u where
  f         = pmap (slcCokernel c k a) a
  aCokerKer = sliceKernelFrom' (slcKernel c k f) f
  b'        = kernelFactor $ universalCone aCokerKer
  u         = universalFactor aCokerKer (ConeKernel (diagram aCokerKer) a')
  
--------------------------------------------------------------------------------
-- slcKerCoker -

-- | the left unit of the cokernel-kenrel adjunction 'slcAdjunction'.
slcKerCoker :: (Universal c, SliceCokernelTo c i d, Universal k, SliceKernelFrom k i d)
  => Proxy c
  -> Proxy k
  -> Slice From i d -> SliceFactor From i d
slcKerCoker c k a@(SliceFrom i a') = SliceFactor (SliceFrom i b') a u where
  t = pmap (slcKernel c k a) a
  aKerCoker = sliceCokernelTo' (slcCokernel c k t) t
  b' = cokernelFactor $ universalCone aKerCoker
  u = universalFactor aKerCoker (ConeCokernel (diagram aKerCoker) a')

--------------------------------------------------------------------------------
-- slcAdjunction -

-- | the cokernel-kenrel adjunction.
slcAdjunction :: (Universal c, SliceCokernelTo c i d, Universal k, SliceKernelFrom k i d)
  => Proxy c
  -> Proxy k
  -> i d
  -> Adjunction (SliceCokernelKernel c k i d) (SliceFactor From i d) (SliceFactor To i d)
slcAdjunction c k _ = Adjunction l r u v where
  l = SliceCokernel
  r = SliceKernel
  u = slcCokerKer c k
  v = slcKerCoker c k


