
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.Variance
-- Description : measuring the variance of being exact.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- measuring the variance of being exact.
module OAlg.Limes.Exact.Variance
  (
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
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsZero

--------------------------------------------------------------------------------
-- Variance -

-- | measuring the variance of two consecutive zero-able arrows of being exact.
--
-- __Properties__ Let @'Variance' t ker coker@ be in @t'Variance' __t__ __d__@ for a 'Distributive'
-- structure @__d__@, then holds:
--
-- (1) If @'end' t@ matches @'ConsZero' ('DiagramChainTo' _ _)@ then holds:
--
-- @
--                          v              w
--   end t         a <------------ b <------------ c
--     ^           ^               ^              ||
--     |           |               |              ||
--   t |           | t0 = 0        | t1 = ker v   || t2 = one c
--     |           |               |              ||
--     |           |               ^              ||
--  start t        a'<<----------- b'<------------ c
--                   v' = coker w'         w'
-- @
--
--    (1.1) @ker@ is the kernel of @v@.
--
--    (1.2) @t1@ is the factor of the universal cone of @ker@.
--
--    (1.3) @t2@ is 'one'.
--
--    (1.4) @w'@ is the universal factor of @w '*' t2@.
--
--    (1.5) @coker@ is the cokernel of @w'@.
--
--    (1.6) @v'@ is the factor of the universal cone of @coker@.
--
--    (1.7) @t0@ is the universal arrow of @v '*' t1@ and hence 'zero'.
--
-- (2) If @'start' t@ matches @'ConsZero' ('DiagramChainFrom' _ _)@ then holds:
--
-- @
--                          v              w
--   sart t        a ------------> b ------------> c
--     |           |               |              ||
--     |           |               |              ||
--   t |           | t0 = 0        | t1 = coker v || t2 = one c
--     |           |               v              ||
--     v           v               v              ||
--   end t         a'>-----------> b'------------> c
--                   v' = ker w'         w'
-- @
--
--    (2.1) @coker@ is the cokernel of @v@.
--
--    (2.2) @t1@ is the factor of the universal cone of @coker@.
--
--    (2.3) @t2@ is 'one'.
--
--    (2.4) @w'@ is the universal factor of @t2 '*' w@.
--
--    (2.5) @ker@ is the kernel of @w'@.
--
--    (2.6) @v'@ is the factor of the universal cone of @ker@.
--
--    (2.7) @t0@ is the universal arrow of @t1 '*' v@ and hence 'zero'.
data Variance t d
  = Variance
      (ConsZeroTrafo t N0 d)
      (Kernel N1 d)
      (Cokernel N1 d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Variance - Duality -

type instance Dual (Variance t d) = Variance (Dual t) (Op d)

coVariance :: Distributive d => Variance t d -> Dual (Variance t d)
coVariance (Variance t ker coker) = Variance (coConsZeroTrafo t) ker' coker' where
  ker'   = lmToOp cokrnLimesDuality coker 
  coker' = lmToOp krnLimesDuality ker

--------------------------------------------------------------------------------
-- Variance - Validable -

instance (Distributive d, XStandardOrtSiteTo d, XStandardOrtSiteFrom d)
  => Validable (Variance t d) where
  valid v@(Variance t ker coker) = Label "Variance" :<=>:
    And [ valid t
        , valid ker
        , valid coker
        , case t of
            ConsZeroTrafo _ (ConsZero (DiagramChainTo _ _)) _
              -> Label "To" :<=>: vldVarianceTo v
            ConsZeroTrafo (ConsZero (DiagramChainFrom _ _)) _ _
              -> Label "From" :<=>: vldVarianceTo $ coVariance v
        ]
    where
      vldVarianceTo :: Distributive d => Variance To d -> Statement
      vldVarianceTo (Variance t@(ConsZeroTrafo _ _ ts) ker coker)
        = And [ Label "1" :<=>: (v == uKer) :?> Params ["v":=show v]
              , Label "2" :<=>: (t1 == fKer) :?> Params ["t1":=show t1]
              ]
        where
          ConsZero (DiagramChainTo _ (v:|w:|Nil))   = end t
          ConsZero (DiagramChainTo _ (v':|w':|Nil)) = start t
          t0:|t1:|t2:|Nil = ts

          ConeKernel (DiagramParallelLR _ _ (uKer:|Nil)) fKer = universalCone ker
         
