
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
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
    Kernels, Kernel, KernelCone, KernelDiagram
  , GenericKernel
  , kernelFactor
  , kernelDiagram

    -- ** Construction
  , kernels, kernels0, kernels1
  , krnEqls, eqlKrns
  , kernelZero

    -- *** Orientation
  , kernelsOrnt

    -- * Cokernels
  , Cokernels, Cokernel, CokernelCone, CokernelDiagram
  , GenericCokernel
  , cokernelFactor
  , cokernelDiagram

    -- ** Construction
  , cokernels, cokernels'

    -- *** Orientation
  , cokernelsOrnt

    -- * Duality
  , krnLimesDuality, cokrnLimesDuality
  , krnLimitsDuality
  , cokrnLimitsDuality

    -- * Proposition
  , prpIsKernel, prpIsCokernel
  )
  where

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList 
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Limes.Cone
import OAlg.Limes.OpDuality
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.EqualizersAndCoequalizers

--------------------------------------------------------------------------------
-- Kernels -

-- | 'Diagram' for a kernel.
type KernelDiagram n = Diagram (Parallel LeftToRight) N2 n

-- | 'Cone' for a kernel.
type KernelCone n = Cone Dst Projective (Parallel LeftToRight) N2 n

-- | generic kenrel over a 'Universal' @__l__@.
type GenericKernel (l :: Type -> Perspective -> DiagramType -> N' -> N' -> Type -> Type) n
  = l Dst Projective (Parallel LeftToRight) N2 n

-- | kernel as a 'Limes'.
type Kernel n = GenericKernel Limes n

-- | kernels for 'Distributive' structures.
type Kernels n       = Limits Dst Projective (Parallel LeftToRight) N2 n

--------------------------------------------------------------------------------
-- kernelFactor -

-- | the factor of its shell.
kernelFactor :: KernelCone N1 c -> c
kernelFactor (ConeKernel _ f) = f

--------------------------------------------------------------------------------
-- kernelDiagram -

-- | the kernel diagram of a given factor.
kernelDiagram :: Oriented c => c -> KernelDiagram N1 c
kernelDiagram f = DiagramParallelLR (start f) (end f) (f:|Nil)

--------------------------------------------------------------------------------
-- kernelZero -

-- | the kernel of the 'zero' factor given by the orientation, i.e. 'one'
kernelZero :: Distributive c => p c -> Orientation (Point c) -> Kernel N1 c
kernelZero _ o = LimesProjective oKer kernelFactor where
  z = zero o
  oKer = ConeKernel (kernelDiagram z) (one (start z))

  
--------------------------------------------------------------------------------
-- kernels0 -

-- | kernels for zero arrows.
kernels0 :: Distributive a => Kernels N0 a
kernels0 = Limits krn where
  krn :: Distributive a => KernelDiagram N0 a -> Kernel N0 a
  krn d@(DiagramParallelLR p _ Nil) = LimesProjective l u where
    l = ConeKernel d (one p)
    u :: KernelCone N0 a -> a
    u (ConeKernel _ f) = f

--------------------------------------------------------------------------------
-- krnEqls -

-- | the induced equalizers where its first arrow is 'zero'.
krnEqls :: (Distributive a, Abelian a) => Kernels n a -> Equalizers (n+1) a
krnEqls krn = Limits (eql krn) where
  eql :: (Distributive a, Abelian a)
    => Kernels n a -> EqualizerDiagram (n+1) a -> Equalizer (n+1) a
  eql krn d = LimesProjective l u where
    LimesProjective (ConeKernel dKrn k) uKrn = limes krn (dgPrlDiffTail d)
    a0 = head $ dgArrows d
    
    l = ConeProjective d (start k) (k:|a0*k:|Nil)
    u c = uKrn (ConeKernel dKrn (head $ shell c))

--------------------------------------------------------------------------------
-- eqlKrns -

-- | the induced kernels given by adjoining a 'zero' arrow as first arrow.
eqlKrns :: Distributive a => Equalizers (n+1) a -> Kernels n a
eqlKrns eql = Limits (krn eql) where
  krn :: Distributive a => Equalizers (n+1) a -> KernelDiagram n a -> Kernel n a
  krn eql d = LimesProjective l u where
    LimesProjective lEql uEql = limes eql (dgPrlAdjZero d)
    
    l = ConeKernel d (head $ shell lEql)
    u c = uEql (ConeProjective (cnDiagram lEql) (tip c) (shell c))

--------------------------------------------------------------------------------
-- kenrels1 -

-- | promoting kernels.
kernels1 :: Distributive a => Kernels N1 a -> Kernels (n+1) a
kernels1 krn1 = Limits (krn krn1) where
  krn :: Distributive a => Kernels N1 a -> KernelDiagram (n+1) a -> Kernel (n+1) a
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
kernels :: Distributive a => Kernels N1 a -> Kernels n a
kernels krn1 = Limits (krn krn1) where
  krn :: Distributive a
    => Kernels N1 a -> KernelDiagram n a -> Kernel n a
  krn krn1 d = case dgArrows d of
    Nil     -> limes kernels0 d
    _:|Nil  -> limes krn1 d
    _:|_:|_ -> limes (kernels1 krn1) d

--------------------------------------------------------------------------------
-- kernelsOrnt -

-- | kernels for 'Orientation'.
kernelsOrnt :: Entity p => p -> Kernels n (Orientation p)
kernelsOrnt t = Limits (krn t) where
  krn :: (Entity p, a ~ Orientation p) => p -> KernelDiagram n a -> Kernel n a
  krn t d@(DiagramParallelLR p _ _) = LimesProjective l u where
    l = ConeKernel d (t:>p)
    u (ConeKernel _ x) = start x :> t
  

--------------------------------------------------------------------------------
-- Cokernels -

-- | 'Diagram' for a cokernel.
type CokernelDiagram n = Diagram (Parallel RightToLeft) N2 n

-- | 'Cone' for a cokernel.
type CokernelCone n = Cone Dst Injective (Parallel RightToLeft) N2 n

-- | generic cokenrel over a 'Universal' @__l__@.
type GenericCokernel (l :: Type -> Perspective -> DiagramType -> N' -> N' -> Type -> Type) n
  = l Dst Injective (Parallel RightToLeft) N2 n

-- | cokernel as 'Limes'.
type Cokernel n = GenericCokernel Limes n -- Limes Dst Injective (Parallel RightToLeft) N2 n

-- | cokernels for 'Distributive' structures.
type Cokernels n       = Limits Dst Injective (Parallel RightToLeft) N2 n

--------------------------------------------------------------------------------
-- cokernelFactor -

-- | the factor of its shell.
cokernelFactor :: CokernelCone N1 c -> c
cokernelFactor (ConeCokernel _ f) = f

--------------------------------------------------------------------------------
-- cokernelDiagram -

-- | the cokernel diagram of a given factor.
cokernelDiagram :: Oriented c => c -> CokernelDiagram N1 c
cokernelDiagram f = DiagramParallelRL (end f) (start f) (f:|Nil)

--------------------------------------------------------------------------------
-- Cokernels - Duality -

-- | duality between cokernels and kernels.
cokrnLimitsDuality :: OpDuality Limits Dst (Cokernels n) (Kernels n)
cokrnLimitsDuality = OpDuality Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- cokrnLimesDuality -

-- | duality between 'Cokernel' to 'Kernel'.
cokrnLimesDuality :: OpDuality Limes Dst (Cokernel n) (Kernel n)
cokrnLimesDuality = OpDuality Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- krnLimesDuality -

-- | duality from 'Kernel' to 'Cokernel'.
krnLimesDuality :: OpDuality Limes Dst (Kernel n) (Cokernel n)
krnLimesDuality = OpDuality Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- krnLimitsDuality -

krnLimitsDuality ::  OpDuality Limits Dst (Kernels n) (Cokernels n)
krnLimitsDuality = OpDuality Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- cokernels -

-- | promoting cokernels.
cokernels :: Distributive a => Cokernels N1 a -> Cokernels n a
cokernels ckrn = lmsFromOp ConeStructDst cokrnLimitsDuality $ kernels krn where
  krn = lmsToOp ConeStructDst cokrnLimitsDuality ckrn

-- | 'cokernels' given by an additional proxy for @n@.
cokernels' :: Distributive a => p n -> Cokernels N1 a -> Cokernels n a
cokernels' _ = cokernels

--------------------------------------------------------------------------------
-- cokernelsOrnt -

-- | cokernels for 'Orientation'.
cokernelsOrnt :: Entity p => p -> Cokernels n (Orientation p)
cokernelsOrnt t = Limits (cokrn t) where
  cokrn :: (Entity p, a ~ Orientation p) => p -> CokernelDiagram n a -> Cokernel n a
  cokrn t d@(DiagramParallelRL p _ _) = LimesInjective l u where
    l = ConeCokernel d (p:>t)
    u (ConeCokernel _ x) = t :> end x

--------------------------------------------------------------------------------
-- prpIsKernel -

relIsKernel :: Eq a => Kernel n a -> FinList n a -> a -> Statement
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
prpIsCokernel :: Distributive a => Cokernel n a -> FinList n a -> a -> Statement
prpIsCokernel coker fs k = Prp "IsCokernel" :<=>: relIsKernel ker (amap1 Op fs) (Op k)
  where ker = lmToOp ConeStructDst cokrnLimesDuality coker
  


