
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
    SliceAdjunction(..), slcAdjunction
  , slcCokerKer, slcKerCoker

    -- * Diagram
  , SliceDiagram(..)
  , sdgMapS, sdgMapCov, sdgMapCnt

    -- * Limits
    
  , SliceCokernels, slcCokernelsCone
  , sliceCokernel
  
  , SliceKernels, slcKernelsCone
  , sliceKernel

    -- * X
  , xSliceFactorFrom

    -- * Proposition
  , prpHomOrtSliceAdjunction
  , prpHomMltSliceAdjunction
  ) where

import Control.Monad
import Control.Applicative ((<|>))

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.NaturalTransformable
import OAlg.Category.Unify

import OAlg.Data.Either

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Definition
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
-- sdgMapCov -

-- | mapping a slice diagram according to a covariant homomorphism.
sdgMapCovStruct :: HomSlicedOriented i h
  => Struct (Sld i) y -> Variant2 Covariant h x y -> SliceDiagram i t n m x -> SliceDiagram i t n m y
sdgMapCovStruct Struct h (SliceDiagramKernel d)   = SliceDiagramKernel $ slMapCov h d
sdgMapCovStruct Struct h (SliceDiagramCokernel d) = SliceDiagramCokernel $ slMapCov h d

-- | mapping a slice diagram according to a covariant homomorphism.
sdgMapCov :: HomSlicedOriented i h
  => Variant2 Covariant h x y -> SliceDiagram i t n m x -> SliceDiagram i t n m y
sdgMapCov h = sdgMapCovStruct (tau (range h)) h

--------------------------------------------------------------------------------
-- sdgMapCnt -

-- | mapping a slice diagram according to a contravariant homomorphism.
sdgMapCntStruct :: HomSlicedOriented i h
  => Struct (Sld i) y
  -> Variant2 Contravariant h x y -> SliceDiagram i t n m x -> SliceDiagram i (Dual t) n m y
sdgMapCntStruct Struct h (SliceDiagramKernel d)   = SliceDiagramCokernel $ slMapCnt h d
sdgMapCntStruct Struct h (SliceDiagramCokernel d) = SliceDiagramKernel $ slMapCnt h d

-- | mapping a slice diagram according to a contravariant homomorphism.
sdgMapCnt :: HomSlicedOriented i h
  => Variant2 Contravariant h x y -> SliceDiagram i t n m x -> SliceDiagram i (Dual t) n m y
sdgMapCnt h = sdgMapCntStruct (tau (range h)) h

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (SliceDiagram i t n m) = SliceDiagram i (Dual t) n m

--------------------------------------------------------------------------------
-- sdgMapS -

sdgMapS :: (HomSlicedOriented i h, t ~ Dual (Dual t))
  => h x y -> SDualBi (SliceDiagram i t n m) x -> SDualBi (SliceDiagram i t n m) y
sdgMapS = vmapBi sdgMapCov sdgMapCov sdgMapCnt sdgMapCnt

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
-- slcKernelsCone -

-- | the induced slice kernels for 'Cone's.
slcKernelsCone :: Distributive x => Kernels N1 x -> SliceKernels i Cone x
slcKernelsCone ks = LimitsG sks where
  sks sd = LimesProjective sl su where
    d = diagram sd
    l = limes ks d
    
    sl = ConeKernel sd (kernelFactor $ universalCone l) 
    su (ConeKernel _ x) = universalFactor l (ConeKernel d x)

--------------------------------------------------------------------------------
-- NaturalDiagrammatic -

instance (HomSlicedOriented i h, t ~ Dual (Dual t))
  => ApplicativeG (SDualBi (DiagramG (SliceDiagram i) t n m)) h (->) where
  amapG h = sdbFromDgmObj . sdgMapS h . sdbToDgmObj
  
instance
  ( CategoryDisjunctive h
  , HomSlicedOriented i h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (DiagramG (SliceDiagram i) t n m)) h (->)

instance
  ( CategoryDisjunctive h
  , HomSlicedOriented i h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => NaturalTransformable h (->)
       (SDualBi (DiagramG (SliceDiagram i) t n m)) (SDualBi (DiagramG Diagram t n m))

instance
  ( CategoryDisjunctive h
  , HomSlicedOriented i h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammatic h (SliceDiagram i) t n m

--------------------------------------------------------------------------------
-- SliceCokernels -

-- | generalized cokernels according to a slice diagram.
type SliceCokernels i c = CokernelsG c (SliceDiagram i) N1

--------------------------------------------------------------------------------
-- slcCokernelsCone -

slcCokernelConeStruct :: Distributive x
  => Variant2 Contravariant (IsoO (Dst,Sld i) Op) x (Op x)
  -> Cokernels N1 x -> SliceCokernels i Cone x
slcCokernelConeStruct (Contravariant2 i) cs = scs where
  
  SDualBi (Left1 ks) = amapG i (SDualBi (Right1 cs))
  sks = slcKernelsCone ks
  SDualBi (Right1 scs) = amapG (inv2 i) (SDualBi (Left1 sks))

-- | the induced slice cokernels for 'Cone's.
slcCokernelsCone ::
  ( Distributive x
  , Sliced i x
  )
  => Cokernels N1 x -> SliceCokernels i Cone x
slcCokernelsCone = slcCokernelConeStruct toDualOpDstSld

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
-- SliceAdjunction - Morphism -

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
  => SliceCokernels i c d
  -> SliceKernels i c d
  -> XOrtSite To d
  -> XOrtSite From d
  -> i d
  -> Statement
prpHomOrtSliceAdjunction cs ks xTo xFrom i = Prp "HomOrtSliceAdjunction"
  :<=>: prpHomOriented (xSliceCokernel cs xTo i <|> xSliceKernel ks xFrom i) where
  
  xSliceCokernel :: (Multiplicative d, Sliced i d)
    => SliceCokernels i c d -> XOrtSite To d -> i d -> X (SomeApplication (SliceAdjunction i c d))
  xSliceCokernel cs xTo i = amap1 (SomeApplication (SliceCokernel cs)) $ xSliceFactorTo xTo i

  xSliceKernel :: (Multiplicative d, Sliced i d)
    => SliceKernels i c d -> XOrtSite From d -> i d -> X (SomeApplication (SliceAdjunction i c d))
  xSliceKernel ks xFrom i = amap1 (SomeApplication (SliceKernel ks)) $ xSliceFactorFrom xFrom i

--------------------------------------------------------------------------------
-- prpHomMltSliceAdjunction -

-- | validity for the values of 'SliceAdjunction' being 'HomMultiplicative'.
prpHomMltSliceAdjunction
  :: (Distributive d, Sliced i d, Conic c)
  => SliceCokernels i c d
  -> SliceKernels i c d
  -> XOrtSite To d
  -> XOrtSite From d
  -> i d
  -> Statement
prpHomMltSliceAdjunction cs ks xTo xFrom i = Prp "HomMltSliceAdjunction" :<=>:
  And [ prpHomMultiplicative (SliceCokernel cs) xSlcTo
      , prpHomMultiplicative (SliceKernel ks) xSlcFrom
      ] where

  xSlcTo   = xosHomMlt $ xosXOrtSiteToSliceFactorTo xTo i
  xSlcFrom = xosHomMlt $ xosXOrtSiteFromSliceFactorFrom xFrom i

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


