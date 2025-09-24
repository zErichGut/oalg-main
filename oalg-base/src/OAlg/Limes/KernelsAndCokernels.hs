
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.KernelsAndCokernels
-- Description : kernels and cokernels
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- kernels and cokernels, i.e. limits in a 'Distributive' structure of @'Diagram' ('Parallel' __d__)@
-- making all arrows 'zero'.
module OAlg.Limes.KernelsAndCokernels
  (

    -- * Kernels
    Kernels, KernelsG
  , Kernel, KernelG
  , KernelCone, KernelConic
  , KernelDiagram, KernelDiagrammatic
  , kernelFactor
  , kernelDiagram

    -- ** Construction
  , kernels, kernels', kernels0, kernels1
  , krnEqls, eqlKrns
  , kernelZero

    -- *** Orientation
  , kernelsOrnt

    -- * Cokernels
  , Cokernels, CokernelsG
  , Cokernel, CokernelG
  , CokernelCone, CokernelConic
  , CokernelDiagram, CokernelDiagrammatic
  , cokernelFactor
  , cokernelDiagram

    -- ** Construction
  , cokernels, cokernels'
  , coKernelsG

    -- *** Orientation
  , cokernelsOrnt

    -- * Proposition
  , prpIsKernel, prpIsCokernel

    -- * X
  , XStandardEligibleConeKernel, XStandardEligibleConeKernel1
  , XStandardEligibleConeFactorKernel, XStandardEligibleConeFactorKernel1
  , XStandardEligibleConeCokernel, XStandardEligibleConeCokernel1
  , XStandardEligibleConeFactorCokernel, XStandardEligibleConeFactorCokernel1

  )
  where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList 
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Definition
import OAlg.Hom.Distributive

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.EqualizersAndCoequalizers

--------------------------------------------------------------------------------
-- Kernels -

-- | 'Diagrammatic' object for a kernel.
type KernelDiagrammatic d (n :: N') = d (Parallel LeftToRight) N2 n :: Type -> Type

-- | 'Diagram' for a kernel.
type KernelDiagram n = KernelDiagrammatic Diagram n

-- | 'Conic' object for a kernel.
type KernelConic c (d :: DiagramType -> N' -> N' -> Type -> Type) (n :: N')
  = c Dst Projective d (Parallel LeftToRight) N2 n :: Type -> Type

-- | 'Cone' for a kernel.
type KernelCone n = KernelConic Cone Diagram n

-- | generic kernel as a 'LimesG'.
type KernelG c d n = LimesG c Dst Projective d (Parallel LeftToRight) N2 n

-- | kernel as a 'KernelG'.
type Kernel n = KernelG Cone Diagram n

-- | generic kernels for 'Distributive' structures.
type KernelsG c d n = LimitsG c Dst Projective d (Parallel LeftToRight) N2 n

-- | kernels for 'Distributive' structures.
type Kernels n = KernelsG Cone Diagram n

--------------------------------------------------------------------------------
-- kernelFactor -

-- | the factor of its shell.
kernelFactor :: Conic c => KernelConic c d n x -> x
kernelFactor c = case cone c of ConeKernel _ x -> x

--------------------------------------------------------------------------------
-- kernelDiagram -

-- | the kernel diagram of a given factor.
kernelDiagram :: Oriented x => x -> KernelDiagram N1 x
kernelDiagram f = DiagramParallelLR (start f) (end f) (f:|Nil)

--------------------------------------------------------------------------------
-- kernelZero -

-- | the kernel of the 'zero' factor given by the orientation, i.e. 'one'
kernelZero :: Distributive x => p x -> Orientation (Point x) -> Kernel N1 x
kernelZero _ o = LimesProjective oKer kernelFactor where
  z = zero o
  oKer = ConeKernel (kernelDiagram z) (one (start z))
  
--------------------------------------------------------------------------------
-- kernels0 -

-- | kernels for zero arrows.
kernels0 :: Distributive x => Kernels N0 x
kernels0 = LimitsG krn where
  krn :: Distributive x => KernelDiagram N0 x -> Kernel N0 x
  krn d@(DiagramParallelLR p _ Nil) = LimesProjective l u where
    l = ConeKernel d (one p)
    u :: KernelCone N0 x -> x
    u (ConeKernel _ f) = f

--------------------------------------------------------------------------------
-- krnEqls -

-- | the induced equalizers where its first arrow is 'zero'.
krnEqls :: (Distributive x, Abelian x) => Kernels n x -> Equalizers (n+1) x
krnEqls krn = LimitsG (eql krn) where
  eql :: (Distributive x, Abelian x)
    => Kernels n x -> EqualizerDiagram (n+1) x -> Equalizer (n+1) x
  eql krn d = LimesProjective l u where
    LimesProjective (ConeKernel dKrn k) uKrn = limes krn (dgPrlDiffTail d)
    a0 = head $ dgArrows d
    
    l = ConeProjective d (start k) (k:|a0*k:|Nil)
    u c = uKrn (ConeKernel dKrn (head $ shell c))

--------------------------------------------------------------------------------
-- eqlKrns -

-- | the induced kernels given by adjoining a 'zero' arrow as first arrow.
eqlKrns :: Distributive x => Equalizers (n+1) x -> Kernels n x
eqlKrns eql = LimitsG (krn eql) where
  cnDiagram = diagram . diagrammaticObject
  
  krn :: Distributive x => Equalizers (n+1) x -> KernelDiagram n x -> Kernel n x
  krn eql d = LimesProjective l u where
    LimesProjective lEql uEql = limes eql (dgPrlAdjZero d)
    
    l = ConeKernel d (head $ shell lEql)
    u c = uEql (ConeProjective (cnDiagram lEql) (tip c) (shell c))

--------------------------------------------------------------------------------
-- kenrels1 -

-- | promoting kernels.
kernels1 :: Distributive x => Kernels N1 x -> Kernels (n+1) x
kernels1 krn1 = LimitsG (krn krn1) where
  krn :: Distributive x => Kernels N1 x -> KernelDiagram (n+1) x -> Kernel (n+1) x
  krn krn1 d@(DiagramParallelLR _ _ (_:|Nil))        = limes krn1 d
  krn krn1 d@(DiagramParallelLR p q (a0:|aN@(_:|_))) = LimesProjective l u where
    dN = DiagramParallelLR p q aN
    LimesProjective (ConeKernel _ h) uN = krn krn1 dN

    d1 = DiagramParallelLR (start h) q (a0*h:|Nil)
    LimesProjective (ConeKernel _ k) u1 = limes krn1 d1
    l = ConeKernel d (h*k)
    u (ConeKernel _ x) = uk where
      uk = u1 (ConeKernel d1 uh)
      uh = uN (ConeKernel dN x)

--------------------------------------------------------------------------------
-- kernels -

-- | promoting kernels.
kernels :: Distributive x => Kernels N1 x -> Kernels n x
kernels krn1 = LimitsG (krn krn1) where
  krn :: Distributive x
    => Kernels N1 x -> KernelDiagram n x -> Kernel n x
  krn krn1 d = case dgArrows d of
    Nil     -> limes kernels0 d
    _:|Nil  -> limes krn1 d
    _:|_:|_ -> limes (kernels1 krn1) d

kernels' :: Distributive x => q n -> Kernels N1 x -> Kernels n x
kernels' _ = kernels

--------------------------------------------------------------------------------
-- kernelsOrnt -

-- | kernels for 'Orientation'.
kernelsOrnt :: Entity p => p -> Kernels n (Orientation p)
kernelsOrnt t = LimitsG (krn t) where
  krn :: (Entity p, x ~ Orientation p) => p -> KernelDiagram n x -> Kernel n x
  krn t d@(DiagramParallelLR p _ _) = LimesProjective l u where
    l = ConeKernel d (t:>p)
    u (ConeKernel _ x) = start x :> t

--------------------------------------------------------------------------------
-- Cokernels -

-- | 'Diagrammatic' object for a cokernel.
type CokernelDiagrammatic d (n :: N') = d (Parallel RightToLeft) N2 n :: Type -> Type

-- | 'Diagram' for a cokernel.
type CokernelDiagram n = CokernelDiagrammatic Diagram n

-- | 'Conic' object for a cokernel.
type CokernelConic c (d :: DiagramType -> N' -> N' -> Type -> Type) (n :: N')
  = c Dst Injective d (Parallel RightToLeft) N2 n :: Type -> Type

-- | 'Cone' for a cokernel.
type CokernelCone n = CokernelConic Cone Diagram n

-- | generic cokernel as a 'LimesG'.
type CokernelG c d n = LimesG c Dst Injective d (Parallel RightToLeft) N2 n

-- | cokernel as a 'CokernelG'.
type Cokernel n = CokernelG Cone Diagram n

-- | generic cokernels for 'Distributive' structures.
type CokernelsG c d n = LimitsG c Dst Injective d (Parallel RightToLeft) N2 n

-- | cokernels for 'Distributive' structures.
type Cokernels n = CokernelsG Cone Diagram n

--------------------------------------------------------------------------------
-- coKernelsG -

coKernelsG ::
  ( Distributive x
  , TransformableGRefl o Dst
  , NaturalConicBi (IsoO Dst o) c Dst Projective d (Parallel LeftToRight) N2 n
  )
  => KernelsG c d n x -> CokernelsG c d n (o x)
coKernelsG ks = cks where
  Contravariant2 i    = toDualO (Struct :: Distributive x => Struct Dst x)
  SDualBi (Left1 cks) = amapF i (SDualBi (Right1 ks))

--------------------------------------------------------------------------------
-- cokernelFactor -

-- | the factor of its shell.
cokernelFactor :: Conic c => CokernelConic c d n x -> x
cokernelFactor c = case cone c of ConeCokernel _ x -> x

--------------------------------------------------------------------------------
-- cokernelDiagram -

-- | the cokernel diagram of a given factor.
cokernelDiagram :: Oriented x => x -> CokernelDiagram N1 x
cokernelDiagram f = DiagramParallelRL (end f) (start f) (f:|Nil)

--------------------------------------------------------------------------------
-- cokernels -

-- | promoting cokernels.
cokernels :: Distributive x => Cokernels N1 x -> Cokernels n x
cokernels ck1 = cks where
  Contravariant2 i     = toDualOpDst
  SDualBi (Left1 k1)   = amapF i (SDualBi (Right1 ck1))
  ks                   = kernels k1
  SDualBi (Right1 cks) = amapF (inv2 i) (SDualBi (Left1 ks))

cokernels' :: Distributive x => q n -> Cokernels N1 x -> Cokernels n x
cokernels' _ = cokernels

--------------------------------------------------------------------------------
-- cokernelsOrnt -

-- | cokernels for 'Orientation'.
cokernelsOrnt :: Entity p => p -> Cokernels n (Orientation p)
cokernelsOrnt t = LimitsG (cokrn t) where
  cokrn :: (Entity p, x ~ Orientation p) => p -> CokernelDiagram n x -> Cokernel n x
  cokrn t d@(DiagramParallelRL p _ _) = LimesInjective l u where
    l = ConeCokernel d (p:>t)
    u (ConeCokernel _ x) = t :> end x

--------------------------------------------------------------------------------
-- prpIsKernel -

relIsKernel :: Eq x => Kernel n x -> FinList n x -> x -> Statement
relIsKernel (LimesProjective (ConeKernel d k') _) fs k
  = And [ Label "1" :<=>: (fs == dgArrows d) :?> Params ["fs":=show fs, "d":= show d]
        , Label "2" :<=>: (k == k') :?> Params ["k":= show k, "k'":= show k']
        ]
    
-- | checks if the arrows of the kernel diagram are equal to the given ones and if its
-- shell is equal to the given arrow.
--
-- __Property__ Let
-- @'LimesProjective' ('ConeKerenl d k') _ = ker@ be in @'Kernel' __n__ __a__@,
-- @fs@ in @'FinList' __n__ __a__@ and @k@ be in @__a__@, then the statement
-- @'prpIsKernel' ker fs k@ holds if and only if
--
-- (1) @fs '==' 'dgArrows' d@.
--
-- (2) @k '==' k'@.
prpIsKernel :: Distributive a => Kernel n a -> FinList n a -> a -> Statement
prpIsKernel ker fs k = Prp "IsKernel" :<=>: relIsKernel ker fs k

--------------------------------------------------------------------------------
-- prpIsCokernel -

-- | checks if the arrows of the cokernel diagram are equal to the given ones and if its
-- shell is equal to the given arrow.
--
-- __Property__ Let
-- @'LimesInjective' ('ConeCokerenl d k') _ = coker@ be in @'Cokernel' __n__ __a__@,
-- @fs@ in @'FinList' __n__ __a__@ and @k@ be in @__a__@, then the statement
-- @'prpIsCokernel' coker fs k@ holds if and only if
--
-- (1) @fs '==' 'dgArrows' d@.
--
-- (2) @k '==' k'@.
prpIsCokernel :: Distributive x => Cokernel n x -> FinList n x -> x -> Statement
prpIsCokernel coker fs k = Prp "IsCokernel" :<=>: relIsKernel ker fs' k' where
  Contravariant2 i    = toDualOpDst
  SDualBi (Left1 ker) = amapF i (SDualBi (Right1 coker))
  fs'                 = amap1 (amapf i) fs
  k'                  = amapf i k
  

--------------------------------------------------------------------------------
-- XStandardEligibleConeKernel -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeG Cone Dst Projective Diagram (Parallel LeftToRight) N2 n x
  => XStandardEligibleConeKernel n x

--------------------------------------------------------------------------------
-- XStandardEligibleConeFactorKernel -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeFactorG Cone Dst Projective Diagram (Parallel LeftToRight) N2 n x
  => XStandardEligibleConeFactorKernel n x

--------------------------------------------------------------------------------
-- XStandardEligibleConeCokernel -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeG Cone Dst Injective Diagram (Parallel RightToLeft) N2 n x
  => XStandardEligibleConeCokernel n x

--------------------------------------------------------------------------------
-- XStandardEligibleConeFactorCokernel -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeFactorG Cone Dst Injective Diagram (Parallel RightToLeft) N2 n x
  => XStandardEligibleConeFactorCokernel n x

--------------------------------------------------------------------------------
-- XStandardEligibleConeKernel1 -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeKernel N1 c => XStandardEligibleConeKernel1 c

--------------------------------------------------------------------------------
-- XStandardEligibleConeFactorKernel1 -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeFactorKernel N1 c => XStandardEligibleConeFactorKernel1 c

--------------------------------------------------------------------------------
-- XStandardEligibleConeCokernel1 -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeCokernel N1 c => XStandardEligibleConeCokernel1 c

--------------------------------------------------------------------------------
-- XStandardEligibleConeFactorCokernel1 -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeFactorCokernel N1 c => XStandardEligibleConeFactorCokernel1 c



