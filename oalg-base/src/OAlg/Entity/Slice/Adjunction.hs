
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
{-
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
-}
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
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.Adjunction

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Slice.Definition
import OAlg.Entity.Slice.Sliced

{-
instance (Typeable c, Typeable k, Typeable i, Typeable d, Typeable x, Typeable y)
  => Entity (SliceCokernelKernel c k i d x y)
instance (Typeable c, Typeable k, Typeable i, Typeable d) => Entity2 (SliceCokernelKernel c k i d)
-}

--------------------------------------------------------------------------------
-- SliceDiagram -

-- | slice as a kernel respectively cokernel diagram.
data SliceDiagram i t n m x where
  SliceDiagramKernel :: Sliced i x => Slice From i x -> SliceDiagram i (Parallel LeftToRight) N2 N1 x
  SliceDiagramCokernel :: Sliced i x => Slice To i x -> SliceDiagram i (Parallel RightToLeft) N2 N1 x

deriving instance Show (SliceDiagram i t n m x)
deriving instance Eq (SliceDiagram i t n m x)

instance Validable (SliceDiagram i t n m x) where
  valid (SliceDiagramKernel f)  = valid f
  valid (SliceDiagramCokernel t) = valid t

--------------------------------------------------------------------------------
-- Diagrammatic -

instance Diagrammatic (SliceDiagram i) where
  diagram (SliceDiagramKernel (SliceFrom _ f)) = DiagramParallelLR s e (f:|Nil)
    where s:>e = orientation f
  diagram (SliceDiagramCokernel (SliceTo _ t)) = DiagramParallelRL e s (t:|Nil)
    where s:>e = orientation t

--------------------------------------------------------------------------------
-- SliceKernels -

-- | generalized kernels according to a slice diagram.
type SliceKernels i c = KernelsG c (SliceDiagram i) N1

--------------------------------------------------------------------------------
-- SlixeCokernels -

-- | generalized cokernels according to a slice diagram.
type SliceCokernels i c = CokernelsG c (SliceDiagram i) N1


--------------------------------------------------------------------------------
-- SliceAdjunction -

-- | the left and right homomorphisms for the cokernel-kernel adjunction 'slcAdjunction' within
-- a 'Distributive' structure @__d__@.
data SliceAdjunction i c d x y where  
  SliceCokernel :: SliceCokernels i c d
                -> SliceAdjunction i c d (SliceFactor To i d) (SliceFactor From i d)
  SliceKernel   :: SliceKernels i c d
                -> SliceAdjunction i c d (SliceFactor From i d) (SliceFactor To i d) 

instance Show2 (SliceAdjunction i c d) where
  show2 (SliceCokernel _) = "SliceCokernel"
  show2 (SliceKernel _)   = "SliceKernel"
  
--------------------------------------------------------------------------------
-- SliceCokernelKernel - Morphism -

instance (Multiplicative d, Sliced i d) => Morphism (SliceAdjunction i c d) where
  type ObjectClass (SliceAdjunction i c d) = Mlt
  homomorphous (SliceCokernel _) = Struct :>: Struct
  homomorphous (SliceKernel _)   = Struct :>: Struct

instance TransformableObjectClassTyp (SliceAdjunction i c d)

--------------------------------------------------------------------------------
-- SliceAdjunction - Entity -

{-
deriving instance Show (SliceAdjunction i c d x y)

instance Show2 (SliceAdjunction c k i d)

deriving instance Eq (SliceAdjunction c k i d x y)
instance Eq2 (SliceAdjunction c k i d)

instance Validable (SliceAdjunction c k i d x y) where
  valid SliceCokernel = SValid
  valid SliceKernel   = SValid
instance Validable2 (SliceAdjunction c k i d)
-}

--------------------------------------------------------------------------------
-- sliceKernel -
sliceKernel ::
  ( Distributive d
  , Sliced i d
  , Conic c
  )
  => SliceKernels i c d -> SliceFactor From i d -> SliceFactor To i d
sliceKernel ks (SliceFactor a@(SliceFrom k _) b _)
    = SliceFactor (SliceTo k a') (SliceTo k b') f' where
    bKer = limes ks (SliceDiagramKernel b)
    bDgm = diagrammaticObject $ cone $ universalCone bKer
    aKer = limes ks (SliceDiagramKernel a)
    
    a' = kernelFactor $ universalCone $ aKer
    b' = kernelFactor $ universalCone $ bKer
    f' = universalFactor bKer (ConeKernel bDgm a')
    -- from SliceFactor a b f valid follows that ConeKernel (diagram bKer) a' is eligible

--------------------------------------------------------------------------------
-- sliceCokernel -

sliceCokernel ::
  ( Distributive d
  , Sliced i d
  , Conic c
  )
  => SliceCokernels i c d -> SliceFactor To i d -> SliceFactor From i d
sliceCokernel cs (SliceFactor a@(SliceTo k _) b _)
    = SliceFactor (SliceFrom k a') (SliceFrom k b') f' where
  
    aCoker = limes cs (SliceDiagramCokernel a)
    aDgm   = diagrammaticObject $ cone $ universalCone aCoker
    bCoker = limes cs (SliceDiagramCokernel b)
    
    a' = cokernelFactor $ universalCone aCoker
    b' = cokernelFactor $ universalCone $ bCoker
    f' = universalFactor aCoker (ConeCokernel aDgm b')
    -- from SliceFactor a b f valid follwos that
    -- ConeCokernel (diagram aCoker) b' is eligible

--------------------------------------------------------------------------------
-- SliceAdjunction - HomMultiplicative -

instance (Distributive d, Sliced i d, Conic c)
  => ApplicativeG Id (SliceAdjunction i c d) (->) where
  
  amapG (SliceCokernel cs) = toIdG (sliceCokernel cs)
  amapG (SliceKernel ks)   = toIdG (sliceKernel ks)

instance (Distributive d, Sliced i d, Conic c)
  => ApplicativeG Pnt (SliceAdjunction i c d) (->) where
  
  amapG (SliceCokernel cs) (Pnt a@(SliceTo k _)) = Pnt (SliceFrom k a') where
    a' = cokernelFactor $ universalCone $ limes cs (SliceDiagramCokernel a)

  amapG (SliceKernel ks) (Pnt a@(SliceFrom k _)) = Pnt (SliceTo k a') where
    a' = kernelFactor $ universalCone $ limes ks (SliceDiagramKernel a)


instance (Distributive d, Sliced i d, Conic c) => HomOriented (SliceAdjunction i c d)
instance (Distributive d, Sliced i d, Conic c) => HomMultiplicative (SliceAdjunction i c d)

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
-- prpHomOrtSliceAdjunction -

-- | validity for the values of 'SliceAdjunction' to be 'HomOriented'.
prpHomOrtSliceAdjunction
  :: (Distributive d, Sliced i d, Conic c)
  => SliceKernels i c d
  -> SliceCokernels i c d
  -> XOrtSite To d
  -> XOrtSite From d
  -> i d
  -> Statement
prpHomOrtSliceAdjunction ks cs xTo xFrom i = Prp "HomOrtSliceAdjunction"
  :<=>: prpHomOriented (xSliceCokernel cs xTo i <|> xSliceKernel ks xFrom i) where
  
  xSliceCokernel :: (Multiplicative d, Sliced i d)
    => SliceCokernels i c d -> XOrtSite To d -> i d -> X (SomeApplication (SliceAdjunction i c d))
  xSliceCokernel cs xTo i = amap1 (SomeApplication (SliceCokernel cs)) $ xSliceFactorTo xTo i

  xSliceKernel :: (Multiplicative d, Sliced i d)
    => SliceKernels i c d -> XOrtSite From d -> i d -> X (SomeApplication (SliceAdjunction i c d))
  xSliceKernel ks xFrom i = amap1 (SomeApplication (SliceKernel ks)) $ xSliceFactorFrom xFrom i

{-
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
-}

--------------------------------------------------------------------------------
-- slcCokerKer -

-- | the right unit of the cokernel-kernel adjunction 'slcAdjunction'.
slcCokerKer :: (Distributive d, Sliced i d, Conic c)
  => SliceCokernels i c d
  -> SliceKernels i c d
  -> Slice To i d -> SliceFactor To i d 
slcCokerKer cs ks a@(SliceTo i a') = SliceFactor a (SliceTo i b') u where
  f       = pmap (SliceCokernel cs) a
  fKer    = limes ks (SliceDiagramKernel f)
  fKerDgm = diagrammaticObject $ cone $ universalCone fKer
  b'      = kernelFactor $ universalCone fKer
  u       = universalFactor fKer (ConeKernel fKerDgm a')

--------------------------------------------------------------------------------
-- slcKerCoker -

-- | the left unit of the cokernel-kenrel adjunction 'slcAdjunction'.
slcKerCoker :: (Distributive d, Sliced i d, Conic c)
  => SliceCokernels i c d
  -> SliceKernels i c d
  -> Slice From i d -> SliceFactor From i d
slcKerCoker cs ks a@(SliceFrom i a') = SliceFactor (SliceFrom i b') a u where
  t         = pmap (SliceKernel ks) a
  tCoker    = limes cs (SliceDiagramCokernel t)
  tCokerDgm = diagrammaticObject $ cone $ universalCone tCoker
  b'        = cokernelFactor $ universalCone tCoker
  u         = universalFactor tCoker (ConeCokernel tCokerDgm a')

--------------------------------------------------------------------------------
-- slcAdjunction -

-- | the cokernel-kenrel adjunction.
slcAdjunction :: (Distributive d, Sliced i d, Conic c)
  => SliceCokernels i c d
  -> SliceKernels i c d
  -> i d
  -> Adjunction (SliceAdjunction i c d) (SliceFactor From i d) (SliceFactor To i d)
slcAdjunction cs ks _ = Adjunction l r u v where
  l = SliceCokernel cs
  r = SliceKernel ks
  u = slcCokerKer cs ks
  v = slcKerCoker cs ks


