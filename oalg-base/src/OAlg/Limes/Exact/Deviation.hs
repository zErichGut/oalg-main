
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE UndecidableInstances #-}

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
{-
    -- * Deviation
    Deviation, deviations, deviation

    -- * Deviation Trafo
  , DeviationTrafo, deviationTrafos, deviationTrafo

    -- * Variance
  , Variance(..), variances, variance
  , vrcTop, vrcBottom

    -- ** Duality
  , coVariance, coVarianceInv, vrcFromOpOp

    -- * Variance Trafo
  , VarianceTrafo(..), varianceTrafos, varianceTrafo
  , vrctTop, vrctBottom

    -- ** Duality
  , coVarianceTrafo, coVarianceTrafoInv, vrctFromOpOp
-}
    -- * Proposition
    prpDeviationOrntSymbol

  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsZero


import OAlg.Data.Symbol

{-
--------------------------------------------------------------------------------
-- GenericKernelCokernel -

class Distributive a => GenericKernel l a where
  gKernel                :: KernelDiagram N1 a -> l a
  gKernelUniversalCone   :: l a -> KernelCone N1 a
  gKernelUniversalFactor :: l a -> KernelCone N1 a -> a

instance  GenericKernel (Kernel N1) (Orientation Symbol) where
  gKernel                = limes $ kernelsOrnt X
  gKernelUniversalCone   = universalCone
  gKernelUniversalFactor = universalFactor

class Distributive a => GenericCokernel l a where
  gCokernel                :: CokernelDiagram N1 a -> l a
  gCokernelUniversalCone   :: l a -> CokernelCone N1 a
  gCokernelUniversalFactor :: l a -> CokernelCone N1 a -> a

type instance Dual (Kernel n)   = Cokernel n
type instance Dual (Cokernel n) = Kernel n

instance (GenericCokernel (Dual k) a) => GenericKernel k (Op a) where

instance (GenericKernel (Dual c) a) => GenericCokernel c (Op a) where
{-
instance GenericCokernel (Cokernel N1) a => GenericKernel (Kernel N1) (Op a) where
  gKernel d = coLimes ConeStructDst Refl Refl $ gCokernel $ coDiagramInv Refl d
-}

class Dualisable1 s f where
  toDual1 :: Struct s a ->  f a -> Dual f (Op a)

instance Dualisable1 Dst (Kernel n) where
  toDual1 Struct = coLimes ConeStructDst Refl Refl
  -- toDual1 = lmToOp krnLimesDuality

instance Dualisable1 Dst (Cokernel n) where
  toDual1 Struct = coLimes ConeStructDst Refl Refl


class Reflexive1 s f where
  fromOpOp1 :: Struct s a -> f (Op (Op a)) -> f a
                 
instance Reflexive1 Dst (Kernel n) where
  fromOpOp1 Struct = lmFromOpOp ConeStructDst Refl Refl where

type GenericKernelCokernelDuality k c
  = ( Reflexive1 Dst k, Reflexive1 Dst c
    , Reflexive1 Dst (Dual c), Reflexive1 Dst (Dual k)
    , Dualisable1 Dst k, Dualisable1 Dst c
    , Dualisable1 Dst (Dual c), Dualisable1 Dst (Dual k)
    , Dual (Dual k) ~ k, Dual (Dual c) ~ c
    )

--------------------------------------------------------------------------------
-- Variance -

-- | measuring the 'deviation' of two consecutive zero-able arrows of being exact accordind to
-- the 'variance' of a 'ConsZero'.
--
-- __Properties__ Let @'Variance' t ker coker@ be in @t'Variance' __t__ __d__@ for a 'Distributive'
-- structure @__d__@, then holds:
--
-- (1) If @'end' t@ matches @'ConsZero' ('DiagramChainTo' _ _)@ then holds (see diagram below):
--
--      (1) @ker@ is the kernel of @v@.
--
--      (2) @t1@ is the factor of the universal cone of @ker@.
--
--      (3) @t2@ is 'one'.
--
--      (4) @w'@ is the universal factor of @w '*' t2@.
--
--      (5) @coker@ is the cokernel of @w'@.
--
--      (6) @v'@ is the factor of the universal cone of @coker@.
--
--      (7) @t0@ is the universal arrow of @v '*' t1@ and hence 'zero'.
--
-- @
--                                  v              w
-- top:      end t         a <------------ b <------------ c
--             ^           ^               ^              ||
--             |           |               |              ||
--           t |           | t0 = 0        | t1 = ker v   || t2 = one c
--             |           |               |              ||
--             |           |               ^              ||
-- bottom:  start t        a'<<----------- b'<------------ c
--                           v' = coker w'         w'
-- @
--
-- (2) If @'start' t@ matches @'ConsZero' ('DiagramChainFrom' _ _)@ then holds (see diagram below):
--
--      (1) @coker@ is the cokernel of @v@.
--
--      (2) @t1@ is the factor of the universal cone of @coker@.
--
--      (3) @t2@ is 'one'.
--
--      (4) @w'@ is the universal factor of @t2 '*' w@.
--
--      (5) @ker@ is the kernel of @w'@.
--
--      (6) @v'@ is the factor of the universal cone of @ker@.
--
--      (7) @t0@ is the universal arrow of @t1 '*' v@ and hence 'zero'.
--
-- @
--                                  v              w
-- top:      sart t        a ------------> b ------------> c
--             |           |               |              ||
--             |           |               |              ||
--           t |           | t0 = 0        | t1 = coker v || t2 = one c
--             |           |               v              ||
--             v           v               v              ||
-- bottom:   end t         a'>-----------> b'------------> c
--                           v' = ker w'         w'
-- @
data Variance t k c d where
  Variance
    :: ConsZeroTrafo t N0 d
    -> k d -> c d
    -> Variance t k c d


--------------------------------------------------------------------------------
-- Variance - Duality -

type instance Dual (Variance t k c d) = Variance (Dual t) (Dual c) (Dual k) (Op d)
-- UndecidableInstances needet!


coVariance :: (Distributive d, Dualisable1 Dst k, Dualisable1 Dst c)
  => Variance t k c d -> Dual (Variance t k c d)
coVariance (Variance t k c) = Variance (coConsZeroTrafo t) k' c'  where
  k' = toDual1 (sDst c) c
  c' = toDual1 (sDst k) k

  sDst :: Distributive d => p d -> Struct Dst d
  sDst _ = Struct



vrcFromOpOp :: (Distributive d, Reflexive1 Dst k, Reflexive1 Dst c)
  => Variance t k c (Op (Op d)) -> Variance t k c d
vrcFromOpOp (Variance t k c) = Variance t' k' c' where
  t' = cnztFromOpOp t
  k' = fromOpOp1 (sDst k) k
  c' = fromOpOp1 (sDst c) c

  sDst :: Distributive d => p (Op (Op d)) -> Struct Dst d
  sDst _ = Struct


coVarianceInv :: ( Distributive d
                 , Reflexive1 Dst k, Reflexive1 Dst c
                 , Dualisable1 Dst (Dual c), Dualisable1 Dst (Dual k)
                 , Dual (Dual k) ~ k, Dual (Dual c) ~ c
                 )
  => Dual (Dual t) :~: t -> Dual (Variance t k c d) -> Variance t k c d
coVarianceInv Refl = vrcFromOpOp . coVariance


--------------------------------------------------------------------------------
-- Variance - Validable -

instance ( GenericKernel k d, GenericCokernel c d
         , GenericKernel (Dual c) (Op d), GenericCokernel (Dual k) (Op d)
         , Validable (k d), Validable (c d)
         , Dualisable1 Dst k, Dualisable1 Dst c
         -- , XStandardOrtSiteTo d, XStandardOrtSiteFrom d
         )
  => Validable (Variance t k c d) where
  valid v@(Variance t ker coker) = Label "Variance" :<=>:
    And [ valid t
        , valid ker
        , valid coker
        , case t of
            ConsZeroTrafo _ (ConsZero (DiagramChainTo _ _)) _
              -> Label "To" :<=>: vldVarianceTo v
            ConsZeroTrafo (ConsZero (DiagramChainFrom _ _)) _ _
              -> Label "From" :<=>:  vldVarianceTo $ coVariance v
        ]
    where
      
      vldVarianceTo :: ( GenericKernel k d, GenericCokernel c d)
        => Variance To k c d -> Statement
      vldVarianceTo (Variance t@(ConsZeroTrafo _ _ ts) ker coker)
        = And [ Label "1" :<=>: (v == uKer) :?> Params ["v":=show v]
              , Label "2" :<=>: (t1 == fKer) :?> Params ["t1":=show t1]
              , Label "3" :<=>: isOne t2 :?> Params ["t2":=show t2]
              , Label "4" :<=>: (w' == uw) :?> Params ["w'":=show w']
              , Label "5" :<=>: (w' == uCoker) :?> Params ["w'":=show w']
              , Label "6" :<=>: (v' == fCoker) :?> Params ["v'":=show v']
              , Label "7" :<=>: (t0 == uv' && isZero t0) :?> Params ["t0":=show t0]
              ]
        where
          ConsZero (DiagramChainTo _ (v:|w:|Nil))   = end t
          ConsZero (DiagramChainTo _ (v':|w':|Nil)) = start t
          t0:|t1:|t2:|Nil = ts

          ConeKernel dKer@(DiagramParallelLR _ _ (uKer:|Nil)) fKer         = gKernelUniversalCone ker
          ConeCokernel dCoker@(DiagramParallelRL _ _ (uCoker:|Nil)) fCoker
            = gCokernelUniversalCone coker

          uw  = gKernelUniversalFactor ker (ConeKernel dKer (w * t2))

          uv' = gCokernelUniversalFactor coker (ConeCokernel dCoker (v * t1))





--------------------------------------------------------------------------------
-- vrcTop -

-- | the top 'ConsZero' chain in the diagram for 'Variance'.
vrcTop :: ( Distributive d, Dualisable1 Dst k, Dualisable1 Dst c
          , Dualisable1 Dst (Dual c), Dualisable1 Dst (Dual k)
          , Dual (Dual k) ~ k, Dual (Dual c) ~ c
          )
  => Variance t k c d -> ConsZero t N0 d
vrcTop v@(Variance d2x3 _ _)         = case d2x3 of
  ConsZeroTrafo _ e _               -> case e of
    ConsZero (DiagramChainTo _ _)   -> e
    ConsZero (DiagramChainFrom _ _) -> coConsZeroInv Refl $ vrcTop $ coVariance v
    
--------------------------------------------------------------------------------
-- vrcBottom -

-- | the bottom 'ConsZero' chain in the diagram for 'Variance'.
vrcBottom :: ( Distributive d, Dualisable1 Dst k, Dualisable1 Dst c
             , Dualisable1 Dst (Dual c), Dualisable1 Dst (Dual k)
             , Dual (Dual k) ~ k, Dual (Dual c) ~ c
             )
  => Variance t k c d -> ConsZero t N0 d
vrcBottom v@(Variance d2x3 _ _)      = case d2x3 of
  ConsZeroTrafo s _ _               -> case s of
    ConsZero (DiagramChainTo _ _)   -> s
    ConsZero (DiagramChainFrom _ _) -> coConsZeroInv Refl $ vrcBottom $ coVariance v

--------------------------------------------------------------------------------
-- variance -

-- | the variance of a 'ConsZero'.
variance :: ( GenericKernel k d, GenericCokernel c d
            -- , GenericKernel (Dual c) (Op d), GenericCokernel (Dual k) (Op d)
            , Dualisable1 Dst k, Dualisable1 Dst c
            , Dualisable1 Dst (Dual k), Dualisable1 Dst (Dual c)
            , Reflexive1 Dst k, Reflexive1 Dst c
            , Dual (Dual k) ~ k, Dual (Dual c) ~ c
            )
  => ConsZero t N0 d -> Variance t k c d
variance e@(ConsZero (DiagramChainTo _ (v:|w:|Nil)))
  = Variance (ConsZeroTrafo s e (t0:|t1:|t2:|Nil)) vKer w'Coker where
  t2 = one $ start w

  dv   = kernelDiagram v
  vKer = gKernel dv
  t1   = kernelFactor $ gKernelUniversalCone vKer
  w'   = gKernelUniversalFactor vKer (ConeKernel dv w)

  dw'     = cokernelDiagram w'
  w'Coker = gCokernel dw'
  t0      = gCokernelUniversalFactor w'Coker (ConeCokernel dw' (v * t1))
  v'      = cokernelFactor $ gCokernelUniversalCone w'Coker
  
  s = ConsZero (DiagramChainTo (end v') (v':|w':|Nil))

{-
  = Variance (ConsZeroTrafo s e (t0:|t1:|t2:|Nil)) vKer w'Coker where
  t2 = one $ start w

  dv   = kernelDiagram v
  vKer = limes kers dv
  t1   = kernelFactor $ universalCone vKer
  w'   = universalFactor vKer (ConeKernel dv w)

  dw'     = cokernelDiagram w'
  w'Coker = limes cokers dw'
  t0      = universalFactor w'Coker (ConeCokernel dw' (v * t1))
  v'      = cokernelFactor $ universalCone w'Coker
  
  s = ConsZero (DiagramChainTo (end v') (v':|w':|Nil))
-}


variance c@(ConsZero (DiagramChainFrom _ _))
  = coVarianceInv Refl $ variance' Proxy Proxy c $ coConsZero c where
  variance' :: ( GenericKernel k d, GenericCokernel c d
               , Dualisable1 Dst k, Dualisable1 Dst c
               , Dualisable1 Dst (Dual k), Dualisable1 Dst (Dual c)
               , Dual (Dual k) ~ k
               , Dual (Dual c) ~ c
               )
    => Proxy k -> Proxy c -> ConsZero From N0 d
    -> ConsZero To N0 (Op d) -> Dual (Variance From k c d)
  variance' _ _ _ = variance


{-
variance kers cokers c@(ConsZero (DiagramChainFrom _ _))
  = coVarianceInv Refl $ variance kers' cokers' $ coConsZero c where

  kers' = lmsToOp cokrnLimitsDuality cokers
  cokers' = lmsToOp krnLimitsDuality kers
-}


--------------------------------------------------------------------------------
-- variances -

variances :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZero t n d -> FinList (n+1) (Variance t d)
variances kers cokers c = variance kers cokers (cnzHead c) :| case cnzArrows c of
  _:|_:|Nil  -> Nil
  _:|_:|_:|_ -> variances kers cokers (cnzTail c) 
  

--------------------------------------------------------------------------------
-- deviation -

-- | the 'deviation' of being exact, i.e. the 'Point' @a'@ in the diagram of 'Variance'.
deviation :: Distributive d => Variance t d -> Point d
deviation = head . cnzPoints . vrcBottom

--------------------------------------------------------------------------------
-- Deviation -

-- | measuring the deviations.
type Deviation n = Diagram Discrete n N0

--------------------------------------------------------------------------------
-- deviations -

-- | the induced 'Deviation's.
deviations :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZero t n d -> Deviation (n+1) d
deviations kers cokers = DiagramDiscrete . amap1 deviation . variances kers cokers

--------------------------------------------------------------------------------
-- VarianceTrafo -

-- | transformation between two 'Variance', i.e. the 'ConsZeroTrafo' between its top 'ConeZero' chains
-- given by 'vrcTop' (see diagram for 'Variance'). Such a transformation give rise to a
-- 'ConsZeroTrafo' betweeen its bottom 'ConsZero' chains, given by 'vrctBottom'.
--
-- __Property__ Let @t@ be in @'VarianceTrafo' __t__ __d__@ for a 'Distributive' structure @__d__@,
-- then holds: @t@ is 'valid' iff @'vrctTop' t@ is 'valid'.
data VarianceTrafo t d = VarianceTrafo (Variance t d) (Variance t d) (FinList N3 d)

--------------------------------------------------------------------------------
-- VarianceTrafo - Duality -

type instance Dual (VarianceTrafo t d) = VarianceTrafo (Dual t) (Op d)

coVarianceTrafo :: Distributive d => VarianceTrafo t d -> Dual (VarianceTrafo t d)
coVarianceTrafo (VarianceTrafo a b fs)
  = VarianceTrafo (coVariance b) (coVariance a) (amap1 Op fs)

vrctFromOpOp :: Distributive d => VarianceTrafo t (Op (Op d)) -> VarianceTrafo t d
vrctFromOpOp (VarianceTrafo a b fs) = VarianceTrafo (vrcFromOpOp a) (vrcFromOpOp b) (amap1 fromOpOp fs)

coVarianceTrafoInv :: Distributive d
  => Dual (Dual t) :~: t -> Dual (VarianceTrafo t d) -> VarianceTrafo t d
coVarianceTrafoInv Refl = vrctFromOpOp . coVarianceTrafo

--------------------------------------------------------------------------------
-- vrctTop -

-- | the induced 'ConsZeroTrafo' between the top 'ConsZero' chains (see diagram for 'Variance').
vrctTop :: Distributive d => VarianceTrafo t d -> ConsZeroTrafo t N0 d
vrctTop (VarianceTrafo a b fs) = ConsZeroTrafo (vrcTop a) (vrcTop b) fs

--------------------------------------------------------------------------------
-- VariaceTrafo - Validable -

instance Distributive d => Validable (VarianceTrafo t d) where
  valid v = Label "VarianceTrafo" :<=>: valid (vrctTop v)
  
--------------------------------------------------------------------------------
-- vrctBottom -

-- | the induced 'ConsZeroTrafo' between the bottom 'ConsZero' chains (see diagram for 'Variance').
vrctBottom :: Distributive d => VarianceTrafo t d -> ConsZeroTrafo t N0 d
vrctBottom t@(VarianceTrafo a b fs) = case vrcTop a of
  ConsZero (DiagramChainTo _ _)    -> ConsZeroTrafo (vrcBottom a) (vrcBottom b) fs' where
    fs' = f'0 :| f'1 :| f'2 :| Nil

    _ :| f1 :| f2 :| Nil = fs

    f'2 = f2

    Variance (ConsZeroTrafo _ _ as) _ aCoker = a
    Variance (ConsZeroTrafo (ConsZero (DiagramChainTo _ bs')) _ _) bKer _ = b
    _ :|a1:|_ :|Nil = as
    b'0:|_ :|Nil = bs'

    bKerDgm = cnDiagram $ universalCone bKer
    f'1 = universalFactor bKer (ConeKernel bKerDgm (f1 * a1))

    aCokerDgm = cnDiagram $ universalCone aCoker
    f'0 = universalFactor aCoker (ConeCokernel aCokerDgm (b'0 * f'1))

  ConsZero (DiagramChainFrom _ _)  -> coConsZeroTrafoInv Refl $ vrctBottom $ coVarianceTrafo t 

--------------------------------------------------------------------------------
-- deviationTrafo -

-- | the transformation between the two given 'deviation's. 
deviationTrafo :: Distributive d => VarianceTrafo t d -> d
deviationTrafo t = f'0 where ConsZeroTrafo _ _ (f'0:|_) = vrctBottom t

--------------------------------------------------------------------------------
-- varianceTrafo -

-- | the induced 'VariancTrafo' given by a 'ConsZeroTrafo'.
--
-- __Property__ Let @t@ be in @'ConsZeroTrafo' __t__ 'N0' __d__@ for a 'Distributive' structure
-- @__d__@ and let @kers@ be in @'Kernels' 'N1' __d__@ and @cokers@ be in @'Cokernels' 'N1' __d__@,
-- then holds: @'vrctTop' ('varianceTraof' kers cokers t) '==' t@.
varianceTrafo :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t N0 d -> VarianceTrafo t d
varianceTrafo kers coker (ConsZeroTrafo a b fs) = VarianceTrafo va vb fs where
  va = variance kers coker a
  vb = variance kers coker b

--------------------------------------------------------------------------------
-- varianceTrafos -

varianceTrafos :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t n d -> FinList (n+1) (VarianceTrafo t d)
varianceTrafos kers cokers t
  = varianceTrafo kers cokers (cnztHead t) :| case cnztTrafos t of
      _:|_:|_:|Nil  -> Nil
      _:|_:|_:|_:|_ -> varianceTrafos kers cokers (cnztTail t)

--------------------------------------------------------------------------------
-- DeviationTrafo -

type DeviationTrafo n = Transformation Discrete n N0

--------------------------------------------------------------------------------
-- deviationTrafos -

-- | the induced 'DeviationTrafo's.
--
-- __Properties__ Let @t@ be in @'ConsZeroTrafo __t__ __n__ __d__@ for a 'Distributive' structure
-- @__d__@ and @kers@ be in @'Kernels' 'N1' __d__@ and @cokers@ be in @'Cokernels' 'N1' __d__@,
-- then holds:
--
-- (1) @'start' ('deviationTrafos' kers cokers t) '==' 'deviations' kers cokers ('start' t)@.
--
-- (2) @'end' ('deviationTrafos' kers cokers t) '==' 'deviations' kers cokers ('end' t)@.
--
-- __Note__ The resulting 'DeviationTrafo' dos not really depend on the choice of @kers@ and @cokers@,
-- i.e. the resulting 'DeviationTrafo' for different choices for @kers@ and @cokers@ are
-- /isomorphic/.
deviationTrafos :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t n d -> DeviationTrafo (n+1) d
deviationTrafos kers cokers t = Transformation a' b' ds where
  ds = amap1 deviationTrafo $ varianceTrafos kers cokers t
  
  a' = DiagramDiscrete $ amap1 start ds
  b' = DiagramDiscrete $ amap1 end ds

--------------------------------------------------------------------------------
-- prpDeviationTrafos -

-- | validity for the properties of 'deviationTrafos'.
prpDeviationTrafos :: (Distributive d, Typeable t, Typeable n)
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t n d -> Statement
prpDeviationTrafos kers cokers t = Prp "DeviationTrafos" :<=>:
  And [ Label "1" :<=>:
          (start ds == deviations kers cokers (start t)) :?> Params ["t":=show t]
      , Label "2" :<=>:
          (end ds == deviations kers cokers (end t)) :?> Params ["t":=show t]
      ]
  where
    ds = deviationTrafos kers cokers t
-}
--------------------------------------------------------------------------------
-- prpDeviation -

-- | validity of some properties for @__d__ ~ 'Orientation' 'Symbol'@.
prpDeviationOrntSymbol :: Statement
prpDeviationOrntSymbol = SValid
{-
prpDeviationOrntSymbol = Prp "Deviation" :<=>:
  And [ Forall (xSomeConsZeroTrafoOrnt 20)
          (\(SomeConsZeroTrafo t) -> prpDeviationTrafos kers cokers t)
      ]
  where kers   = kernelsOrnt X
        cokers = cokernelsOrnt Y
-}
