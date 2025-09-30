
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.Deviation
-- Description : measuring the deviation of exactness.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- measuring the deviation exactness.
module OAlg.Limes.Exact.Deviation
  (

    -- * Deviation
    deviation, deviations, Deviation

    -- * Deviation Hom
  , deviationHom, DeviationHom
  
    -- * Variance
  , variance, VarianceG(..), Variance
  , vrcConsZeroHom

  , vrcSite
  , vrcHead, vrcTail

  , NaturalKernelCokernel
  , EntityDiagrammatic
  , ObjectKernelCokernel

    -- ** Duality
  , vrcMapS, vrcMapCov, vrcMapCnt


    -- * Variance Hom
  , varianceHom, VarianceGHom(..), VarianceHom

  , vrcHomSite
  , vrcHomConsZeroHom

    -- ** Duality
  , vrcHomMapS, vrcHomMapCov, vrcHomMapCnt

    -- * Proposition

  , prpVarianceG
  , prpVarianceGHom
  , prpDeviationOrntSymbol

  ) where

import Data.Typeable
import Data.List as L ((++))

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F

import OAlg.Hom.Definition
import OAlg.Hom.Distributive

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsecutiveZero

import OAlg.Data.Symbol

--------------------------------------------------------------------------------
-- VarianceG -

-- | measuring the 'deviation' of a consecutive zero chain of being exact accordind to the given
-- generalized kernels and cokernels. The exactness is given by  'deviations'.
--
-- __Properties__ Let @'VarianceG' c vs@ be in @t'VarianceG' __t k c d n x__@ for a 'Distributive'
-- structure @__x__@, then
-- for all @(ker 0, coker 0), (ker 1, coker 1) .. (ker i,coker i) .. (ker n,coker n)@ in @vs@,
-- and @d 0, d 1 .. d i, d (i+1) .. d (n+1)@ in @'cnzArrows' t@ holds:
--
-- (1) If @t@ matches @'ConsecutiveZero' ('DiagramChainTo' _ _)@ then holds (see diagram below):
--
--     (1) @ker i@ is a kernel of @d i@.
--
--     (2) @coker i@ is a cokernel of @d' (i+1)@, where @d' (i+1)@ is the universal factor given
--     by @ker i@ and @d (i+1)@.
--
-- @
--                d i          d (i+1)               
-- c :  ... a <------------ b <------------ c ...
--                          ^              || 
--                          |              || 
--                          | ker i        || one
--                          |              || 
--                          ^              || 
--          a'<<----------- b'<------------ c 
--               coker i        d' (i+1)
-- @
--
-- (2) If @t@ matches @'ConsecutiveZero' ('DiagramChainFrom' _ _)@ then holds (see diagram below):
--
--     (1) @coker i@ is a cokernel of @d i@.
--
--     (2) @ker i@ is a kernel of @d' (i+1)@, where @d' (i+1)@ is the universal factor given
--     by @coker i@ and @d (i+1)@.
--
-- @
--                d i          d (i+1)               
-- c :  ... a ------------> b ------------> c ...
--                          v              || 
--                          |              || 
--                          | coker i      || one
--                          v              || 
--                          v              || 
--          a'>>----------> b'------------> c 
--               ker i          d' (i+1)
-- @
data VarianceG t k c d n x where
  VarianceG
    :: ConsecutiveZero t n x
    -> FinList (n+1) (KernelG k d N1 x, CokernelG c d N1 x)
    -> VarianceG t k c d n x

--------------------------------------------------------------------------------
-- Variance -

-- | the variance according to 'Kernels' and 'Cokernels'
type Variance t = VarianceG t Cone Cone Diagram
--------------------------------------------------------------------------------
-- vrcSite -

-- | proof that the site is either 'From' or 'To'.
vrcSite :: VarianceG t k c d n x -> Either (t :~: From) (t :~: To)
vrcSite (VarianceG c _) = cnzSite c

--------------------------------------------------------------------------------
-- vrcMapCov -

vrcMapCov ::
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalConic (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Covariant (Inv2 h) x y -> VarianceG t k c d n x -> VarianceG t k c d n y
vrcMapCov i (VarianceG c vs) = VarianceG c' vs' where
  c'  = cnzMapCov i c
  vs' = amap1 (\(ker,coker) -> (lmMapCov i ker, lmMapCov i coker)) vs

--------------------------------------------------------------------------------
-- vrcMapCnt -

vrcMapCnt ::
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalConic (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Contravariant (Inv2 h) x y -> VarianceG t k c d n x -> VarianceG (Dual t) c k d n y
vrcMapCnt i (VarianceG c vs) = VarianceG c' vs' where
  c'  = cnzMapCnt i c
  vs' = amap1 (\(ker,coker) -> (lmMapCnt i coker, lmMapCnt i ker)) vs

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (VarianceG t k c d n) = VarianceG (Dual t) c k d n

--------------------------------------------------------------------------------
-- vrcMapS -

vrcMapS :: 
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalConicBi (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConicBi (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  , t ~ Dual (Dual t)
  )
  => Inv2 h x y -> SDualBi (VarianceG t k c d n) x  -> SDualBi (VarianceG t k c d n) y
vrcMapS = vmapBi vrcMapCov vrcMapCov vrcMapCnt vrcMapCnt

--------------------------------------------------------------------------------
-- NaturalKernelCokernel -

-- | natural conics for kernels and cokenrels.
type NaturalKernelCokernel h k c d =
  ( NaturalConic h k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic h k Dst Injective d (Parallel RightToLeft) N2 N1
  , NaturalConic h c Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic h c Dst Injective d (Parallel RightToLeft) N2 N1
  )
    
--------------------------------------------------------------------------------
-- FunctorialG -

instance
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalKernelCokernel (Inv2 h) k c d
  , t ~ Dual (Dual t)

  )
  => ApplicativeG (SDualBi (VarianceG t k c d n)) (Inv2 h) (->) where
  amapG = vrcMapS

instance
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalKernelCokernel (Inv2 h) k c d
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (VarianceG t k c d n)) (Inv2 h) (->)

--------------------------------------------------------------------------------
-- vrcHead -

vrcHead :: Distributive x => VarianceG t k c d n x -> VarianceG t k c d N0 x
vrcHead (VarianceG c vs) = VarianceG (cnzHead c) (head vs:|Nil)

--------------------------------------------------------------------------------
-- vrcTail -

vrcTail :: Distributive x => VarianceG t k c d (n+1) x -> VarianceG t k c d n x
vrcTail (VarianceG c vs) = VarianceG (cnzTail c) (tail vs)

--------------------------------------------------------------------------------
-- ObjectKernelCokernel -

type ObjectKernelCokernel k c d x =
  ( Diagrammatic d
  , Object (k Dst Projective d (Parallel LeftToRight) N2 N1 x)  
  , Object (k Dst Injective d (Parallel RightToLeft) N2 N1 (Op x))
  , Object (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  , Object (c Dst Projective d (Parallel LeftToRight) N2 N1 (Op x))  
  )

--------------------------------------------------------------------------------
-- EntityDiagrammatic -

type EntityDiagrammatic d x =
  ( Typeable d
  , Entity (d (Parallel LeftToRight) N2 N1 x)
  , Entity (d (Parallel RightToLeft) N2 N1 x)  
  , Entity (d (Parallel LeftToRight) N2 N1 (Op x))
  , Entity (d (Parallel RightToLeft) N2 N1 (Op x))
  )
  
--------------------------------------------------------------------------------
-- prpVarianceG -

relVarianceGTo ::
  ( Distributive x
  
    -- d
  , Diagrammatic d
  , Typeable d
  , Entity (d (Parallel LeftToRight) N2 N1 x)
  , Entity (d (Parallel RightToLeft) N2 N1 x)

    -- k
  , Conic k
  , Object (k Dst Projective d (Parallel LeftToRight) N2 N1 x)

    -- c
  , Conic c
  , Object (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  
  )
  => XEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> XEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> N -> VarianceG To k c d n x -> Statement
relVarianceGTo xeck xecfk xecc xecfc i
  v@(VarianceG c@(ConsecutiveZero (DiagramChainTo _ (f:|g:|ds))) ((ker,coker):|_))
  = And [ valid c
        , Label "ker"   :<=>: prpLimes xeck xecfk ker
        , Label "coker" :<=>: prpLimes xecc xecfc coker        
        , Label "1" :<=>: (kernelDiagram f == diagram (universalDiagram ker))
                            :?> Params [("d " L.++ show i):=show f, ("ker" L.++ show i):=show ker]
        , Label "2" :<=>: (cokernelDiagram g' == diagram (universalDiagram coker))
                            :?> Params [ ("d' " L.++ show i'):=show g'
                                       , ("coker" L.++ show i):=show coker
                                       ]
        , case ds of
            Nil    -> SValid
            _ :| _ -> relVarianceGTo xeck xecfk xecc xecfc i' (vrcTail v)
                        

        ] where g' = universalFactor ker (ConeKernel (universalDiagram ker) g)
                i' = succ i

relVarianceG ::
  ( Distributive x
  , EntityDiagrammatic d x
  , NaturalKernelCokernel (IsoO Dst Op) k c d
  , ObjectKernelCokernel k c d x
  )
  => XEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> XEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> VarianceG t k c d n x -> Statement
relVarianceG xeck xecfk xecc xecfc v@(VarianceG (ConsecutiveZero (DiagramChainTo _ _)) _)
  = relVarianceGTo xeck xecfk xecc xecfc 0 v

relVarianceG xeck xecfk xecc xecfc v@(VarianceG (ConsecutiveZero (DiagramChainFrom _ _)) _)
  = relVarianceGTo xeck' xecfk' xecc' xecfc' 0 v' where
  Contravariant2 i       = toDualOpDst
  
  SDualBi (Left1 v')     = vrcMapS i (SDualBi (Right1 v))
  
  SDualBi (Left1 xeck')  = xecMapS i (SDualBi (Right1 xecc))
  SDualBi (Left1 xecc')  = xecMapS i (SDualBi (Right1 xeck))
  SDualBi (Left1 xecfk') = xecfMapS i (SDualBi (Right1 xecfc))
  SDualBi (Left1 xecfc') = xecfMapS i (SDualBi (Right1 xecfk))
  

-- | validity according to 'VarianceG'.
prpVarianceG ::
  ( Distributive x
  , EntityDiagrammatic d x
  , NaturalKernelCokernel (IsoO Dst Op) k c d
  , ObjectKernelCokernel k c d x
  )
  => XEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> XEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> VarianceG t k c d n x -> Statement
prpVarianceG xeck xecfk xecc xecfc v = Prp "VarianceG"
  :<=>: relVarianceG xeck xecfk xecc xecfc v


instance
  ( Distributive x
  , XStandardEligibleConeKernel N1 x
  , XStandardEligibleConeFactorKernel N1 x
  , XStandardEligibleConeCokernel N1 x
  , XStandardEligibleConeFactorCokernel N1 x
  )
  => Validable (VarianceG t Cone Cone Diagram n x) where
  valid = prpVarianceG xStandardEligibleConeG xStandardEligibleConeFactorG
                      xStandardEligibleConeG xStandardEligibleConeFactorG

--------------------------------------------------------------------------------
-- variance -

-- | the variance for the site 'To' according to 'Kernels' and 'Cokernels'.
varianceTo :: Distributive x
  => Kernels N1 x -> Cokernels N1 x
  -> ConsecutiveZero To n x -> Variance To n x
varianceTo ker coker c = VarianceG c (kcs ker coker c) where

  kc :: Distributive x
    => Kernels N1 x -> Cokernels N1 x
    -> ConsecutiveZero To n x -> (Kernel N1 x,Cokernel N1 x)
  kc ks cs (ConsecutiveZero (DiagramChainTo _ (v:|w:|_))) = (k,c) where
    k  = limes ks (kernelDiagram v)
    w' = universalFactor k (ConeKernel (universalDiagram k) w)
    c  = limes cs (cokernelDiagram w')

  kcs :: Distributive x
    => Kernels N1 x -> Cokernels N1 x
    -> ConsecutiveZero To n x -> FinList (n+1) (Kernel N1 x,Cokernel N1 x)
  kcs ks cs c@(ConsecutiveZero (DiagramChainTo _ (_:|_:|ds)))
    = kc ks cs c :| case ds of
        Nil     -> Nil
        _ :| _  -> kcs ks cs (cnzTail c)

-- | the variance according to 'Kernels' and 'Cokernels'.
variance :: Distributive x
  => Kernels N1 x -> Cokernels N1 x
  -> ConsecutiveZero t n x -> Variance t n x
variance ks cs c@(ConsecutiveZero (DiagramChainTo _ _))   = varianceTo ks cs c
variance ks cs c@(ConsecutiveZero (DiagramChainFrom _ _)) = v where
  Contravariant2 i = toDualOpDst
  SDualBi (Left1 c')  = amapF i (SDualBi (Right1 c))
  SDualBi (Left1 ks') = amapF i (SDualBi (Right1 cs))
  SDualBi (Left1 cs') = amapF i (SDualBi (Right1 ks))

  v' = varianceTo ks' cs' c'
  SDualBi (Right1 v) = amapF (inv2 i) (SDualBi (Left1 v'))

--------------------------------------------------------------------------------
-- vrcConsZeroHom -

vrcConsZeroHomTo ::
  ( Distributive x
  , Conic c, Conic k
  )
  => VarianceG To k c d n x -> ConsecutiveZeroHom To n x
vrcConsZeroHomTo (VarianceG (ConsecutiveZero top@(DiagramChainTo a (_:|w:|ds))) ((ker,coker):|_))
  = ConsecutiveZeroHom (DiagramTrafo bot top ts) where
  bot = DiagramChainTo a' (v':|w':|ds)
  a'  = end v'
  v'  = cokernelFactor $ universalCone coker
  w'  = universalFactor ker (ConeKernel (universalDiagram ker) w)
  
  ts = zero (a':>a):| kernelFactor (universalCone ker) :| amap1 (one . start) (w:|ds)
  

-- | the induce homomorphism of consecutive zero-able chains.
--
-- __Property__ Let @v = 'VarianceG' c vs@ be in @'VarianceG' __t k c d n x__@, then holds:
--
-- (1) If @c@ matches @'ConsecutiveZero' ('DiagramChainTo _ _)@ then holds:
--
--     (1) @'end' ('vrcConsZeroHom' v) '==' c@.
--
--     (2) @ti@ is given by the diagram below.
--
-- @
--                                 v              w               
-- top:      end t         a <------------ b <------------ c <------------ d ...
--             ^           ^               ^              ||              ||
--             |           |               |              ||              ||
--           t |           | t0 = 0        | t1 = ker0 v  || t2 = one c   || t3 = one d ...
--             |           |               |              ||              ||
--             |           |               ^              ||              || 
-- bottom:  start t        a'<<----------- b'<------------ c <------------ d ...
--                           v' = coker0 w'        w' 
-- @
--
-- (2) If @c@ matches @'ConsecutiveZero' ('DiagramChainFrom' _ _)@ then holds:
--
--     (1) @'start' ('vrcConsZeroHom' v) '==' c@.
--
--     (2) @t i@ is given by the diagram below.
--
-- @
--                                  v               w
-- top:      sart t        a ------------> b -------------> c ------------> d ...
--             |           |               |               ||              ||
--             |           |               |               ||              ||
--           t |           | t0 = 0        | t1 = coker0 v || t2 = one c   || t3 = one d ...
--             |           |               v               ||              ||
--             v           v               v               ||              ||
-- bottom:   end t         a'>-----------> b'-------------> c ------------> d ...
--                           v' = ker0 w'          w'
-- @
vrcConsZeroHom :: (Distributive x, NaturalKernelCokernel (IsoO Dst Op) k c d)
  => VarianceG t k c d n x -> ConsecutiveZeroHom t n x
vrcConsZeroHom v@(VarianceG (ConsecutiveZero (DiagramChainTo _ _)) _)   = vrcConsZeroHomTo v
vrcConsZeroHom v@(VarianceG (ConsecutiveZero (DiagramChainFrom _ _)) _) = t where
  Contravariant2 i   = toDualOpDst
  SDualBi (Left1 v') = amapF i (SDualBi (Right1 v))
  t'                 = vrcConsZeroHom v'
  SDualBi (Right1 t) = amapF (inv2 i) (SDualBi (Left1 t'))

--------------------------------------------------------------------------------
-- VarianceGHom -

-- | homomorphism between variances.
--
-- __Property__ Let @t@ be in @'VarianceGHom' __t k c d n x__@, the holds:
--
-- (1) the induced homomorphism @'vrcHomConsZeroHom' t@ is 'valid'.
data VarianceGHom t k c d n x
  = VarianceGHom (VarianceG t k c d n x) (VarianceG t k c d n x) (FinList (n+3) x)

--------------------------------------------------------------------------------
-- VarianceHom -

-- | homomorphism according to 'Kernel' and 'Cokernel'.
type VarianceHom t = VarianceGHom t Cone Cone Diagram

--------------------------------------------------------------------------------
-- vrcHomSite -

-- | proof that the site is either 'From' or 'To'.
vrcHomSite :: VarianceGHom t k c d n x -> Either (t :~: From) (t :~: To)
vrcHomSite (VarianceGHom v _ _) = vrcSite v

--------------------------------------------------------------------------------
-- vrcHomConsZeroHom -

-- | the induce homomorphism between consecutive zero chains.
vrcHomConsZeroHom :: VarianceGHom t k c d n x -> ConsecutiveZeroHom t n x
vrcHomConsZeroHom (VarianceGHom a b fs) = ConsecutiveZeroHom t where
  VarianceG (ConsecutiveZero a') _ = a
  VarianceG (ConsecutiveZero b') _ = b
  t = DiagramTrafo a' b' fs

--------------------------------------------------------------------------------
-- prpVarianceGHom -

prpVarianceGHom ::
  ( Distributive x
  , EntityDiagrammatic d x
  , NaturalKernelCokernel (IsoO Dst Op) k c d
  , ObjectKernelCokernel k c d x
  , Typeable t, Typeable n
  )
  => XEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> XEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> VarianceGHom t k c d n x -> Statement
prpVarianceGHom xeck xecfk xecc xecfc t@(VarianceGHom a b _) = Prp "VarianceGHom" :<=>:
  And [ Label "start" :<=>: prpVarianceG xeck xecfk xecc xecfc a
      , Label "end" :<=>: prpVarianceG xeck xecfk xecc xecfc b
      , Label "trafo" :<=>: valid (vrcHomConsZeroHom t)
      ]

instance
  ( Distributive x
  , XStandardEligibleConeKernel N1 x
  , XStandardEligibleConeFactorKernel N1 x
  , XStandardEligibleConeCokernel N1 x
  , XStandardEligibleConeFactorCokernel N1 x
  , Typeable t, Typeable n
  )
  => Validable (VarianceGHom t Cone Cone Diagram n x) where
  valid = prpVarianceGHom xStandardEligibleConeG xStandardEligibleConeFactorG
                           xStandardEligibleConeG xStandardEligibleConeFactorG

--------------------------------------------------------------------------------
-- vrcHomMapCov -

vrcHomMapCov ::
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h  
  , NaturalConic (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Covariant (Inv2 h) x y -> VarianceGHom t k c d n x -> VarianceGHom t k c d n y
vrcHomMapCov h (VarianceGHom a b fs) = VarianceGHom a' b' fs' where
  a'  = vrcMapCov h a
  b'  = vrcMapCov h b
  fs' = amap1 (amap h) fs

--------------------------------------------------------------------------------
-- vrcHomMapCnt -

vrcHomMapCnt ::
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h  
  , NaturalConic (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Contravariant (Inv2 h) x y
  -> VarianceGHom t k c d n x -> VarianceGHom (Dual t) c k d n y
vrcHomMapCnt h (VarianceGHom a b fs) = VarianceGHom b' a' fs' where
  a'  = vrcMapCnt h a
  b'  = vrcMapCnt h b
  fs' = amap1 (amap h) fs

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (VarianceGHom t k c d n) = VarianceGHom (Dual t) c k d n

--------------------------------------------------------------------------------
-- vrcHomMapS -

vrcHomMapS :: 
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h  
  , NaturalConicBi (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConicBi (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  , t ~ Dual (Dual t)
  )
  => Inv2 h x y -> SDualBi (VarianceGHom t k c d n) x -> SDualBi (VarianceGHom t k c d n) y
vrcHomMapS = vmapBi vrcHomMapCov vrcHomMapCov vrcHomMapCnt vrcHomMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalKernelCokernel (Inv2 h) k c d
  , t ~ Dual (Dual t)

  )
  => ApplicativeG (SDualBi (VarianceGHom t k c d n)) (Inv2 h) (->) where
  amapG = vrcHomMapS

instance
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalKernelCokernel (Inv2 h) k c d
  , t ~ Dual (Dual t)

  )
  => FunctorialG (SDualBi (VarianceGHom t k c d n)) (Inv2 h) (->)

--------------------------------------------------------------------------------
-- varianceHom --

varianceHom :: (Distributive x, Typeable t, Attestable n)
  => Kernels N1 x -> Cokernels N1 x
  -> ConsecutiveZeroHom t n x -> VarianceHom t n x
varianceHom kers cokers h = VarianceGHom a b fs where
  a  = variance kers cokers (start h)
  b  = variance kers cokers (end h)
  fs = cnzHomArrows h

--------------------------------------------------------------------------------
-- deviation -

-- | the 'deviation' of being exact, i.e. the 'Point' @a'@ in the diagram of 'VarianceG'.
deviation ::
  ( Distributive x
  , NaturalKernelCokernel (IsoO Dst Op) k c d
  , Typeable t, Typeable n
  )
  => VarianceG t k c d n x -> Point x
deviation v = case orientation $ vrcConsZeroHom v of
  ConsecutiveZero (DiagramChainTo a' _) :> _   -> a'
  _ :> ConsecutiveZero (DiagramChainFrom a' _) -> a'

--------------------------------------------------------------------------------
-- Deviation -

-- | measuring the deviations.
type Deviation n = Diagram Discrete n N0

--------------------------------------------------------------------------------
-- deviations -

-- | the induced 'Deviation's.
deviations :: 
  ( Distributive x
  , NaturalKernelCokernel (IsoO Dst Op) k c d
  , Typeable t, Attestable n
  )
  => VarianceG t k c d n x -> Deviation (n+1) x
deviations v = DiagramDiscrete (dvs attest v) where

  dvs ::
    ( Distributive x
    , NaturalKernelCokernel (IsoO Dst Op) k c d
    , Typeable t, Attestable n
    )
    => Any n -> VarianceG t k c d n x -> FinList (n+1) (Point x)
  dvs n v = deviation v :| case n of
    W0   -> Nil
    SW n -> case ats n of Ats -> dvs n (vrcTail v)

--------------------------------------------------------------------------------
-- DeviationHom -

-- | transormation between 'Deviation's.
type DeviationHom n = DiagramTrafo Discrete n N0

--------------------------------------------------------------------------------
-- deviationHom -

-- | the induced homomorphism between 'Deviation's.
deviationHomTo ::
  ( Distributive x
  , NaturalKernelCokernel (IsoO Dst Op) k c d
  , Attestable n
  )
  => VarianceGHom To k c d n x -> DeviationHom (n+1) x
deviationHomTo (VarianceGHom a b fs) = DiagramTrafo a' b' fs' where
  a'  = deviations a
  b'  = deviations b
  fs' = trfs a b fs

  trf ::
    ( Distributive x
    , Conic k, Conic c
    )
    => VarianceG To k c d n x -> VarianceG To k c d n x -> x -> x
  trf a b f = f'' where
    VarianceG (ConsecutiveZero (DiagramChainTo _ _)) ((aKer,aCoker):|_) = a
    VarianceG (ConsecutiveZero (DiagramChainTo _ _)) ((bKer,bCoker):|_) = b

    f' = universalFactor bKer (ConeKernel (universalDiagram bKer) (f*ak)) where
      ak = kernelFactor (universalCone aKer)
    f'' = universalFactor aCoker (ConeCokernel (universalDiagram aCoker) (bc*f')) where
      bc = cokernelFactor (universalCone bCoker)

  trfs :: 
    ( Distributive x
    , Conic k, Conic c
    )
    => VarianceG To k c d n x -> VarianceG To k c d n x -> FinList (n+3) x -> FinList (n+1) x
  trfs a b (_:|f:|fs) = trf a b f :| case a of
    VarianceG _ (_:|Nil)  -> Nil
    VarianceG _ (_:|_:|_) -> trfs (vrcTail a) (vrcTail b) (f:|fs)

-- | the induced homomorphism between 'Deviation's.
deviationHom ::
  ( Distributive x
  , NaturalKernelCokernel (IsoO Dst Op) k c d
  , Attestable n
  )
  => VarianceGHom t k c d n x -> DeviationHom (n+1) x
deviationHom h = case vrcHomSite h of
  Right Refl -> deviationHomTo h
  Left Refl  -> dh where
    Contravariant2 i = toDualOpDst

    SDualBi (Left1 hOp) = amapF i (SDualBi (Right1 h))
    dhOp                = deviationHom hOp
    SDualBi (Right1 dh) = amapF (inv2 i) (SDualBi (Left1 dhOp))

--------------------------------------------------------------------------------
-- prpDeviation -

-- | validity of some properties for @__d__ ~ 'Orientation' 'Symbol'@.
prpDeviationOrntSymbol :: Statement
prpDeviationOrntSymbol = Prp "Deviation" :<=>:
  And [ Forall (xSomeConsecutiveZeroHomOrnt 20)
          (\(SomeConsecutiveZeroHom t)
           -> valid (deviationHom $ varianceHom kers cokers t)
          )
      ]
  where kers   = kernelsOrnt X
        cokers = cokernelsOrnt Y

