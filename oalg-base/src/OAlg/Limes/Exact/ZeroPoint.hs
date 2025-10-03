
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.ZeroPoint
-- Description : zero points.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- zero points within a 'Distributive' structure.
module OAlg.Limes.Exact.ZeroPoint
  (
    -- * Zero Point
    ZeroPoint(..), isZeroPoint

    -- * Limes
  , zrPointTerminal, zrPointTerminals
  , zrPointInitial, zrPointInitials
  ) where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Hom.Distributive

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.TerminalAndInitialPoint

import OAlg.Entity.Diagram

--------------------------------------------------------------------------------
-- ZeroPoint -

-- | predicate for a zero point within a 'Distributive' structure @__x__@.
--
-- __Property__ Let @'ZeroPoint' z@ be in @'ZeroPoint' __x__@ within a
-- 'Distributive' structure @__x__@, then holds:
--
-- (1) @'zero' (z ':>' z) '==' 'one' z@,
newtype ZeroPoint x = ZeroPoint (Point x)

deriving instance ShowPoint x => Show (ZeroPoint x)
deriving instance EqPoint x => Eq (ZeroPoint x)

--------------------------------------------------------------------------------
-- isZeroPoint -

-- | testing of being a zero point accroding to the given proxy type.
isZeroPoint :: Distributive x => q x -> Point x -> Bool
isZeroPoint q p = zero' q (p :> p) == one p

instance Distributive x => Validable (ZeroPoint x) where
  valid z@(ZeroPoint p) = Label "ZeroPoint" :<=>: isZeroPoint z p :?> Params ["p":=show p]

--------------------------------------------------------------------------------
-- zrPointTerminal -

-- | a zero point as terminal point.
zrPointTerminal :: Distributive x => ZeroPoint x -> TerminalPoint x
zrPointTerminal (ZeroPoint z) = LimesProjective (trmCone z) (univ z) where
  univ :: Distributive x => Point x -> TerminalCone x -> x
  univ z (ConeProjective DiagramEmpty p _) = zero (p:>z)

-- | the induced terminals.
zrPointTerminals :: Distributive x => ZeroPoint x -> Terminals x
zrPointTerminals = LimitsG . const . zrPointTerminal

--------------------------------------------------------------------------------
-- zrPointInitial -

-- | a zero point as initial point.
zrPointInitial :: Distributive x => ZeroPoint x -> InitialPoint x
zrPointInitial (ZeroPoint z) = intPnt where
  Contravariant2 i        = toDualOpDst
  
  trmPnt                  = zrPointTerminal (ZeroPoint z) -- z as a zero point in Op x
  SDualBi (Right1 intPnt) = amapF (inv2 i) (SDualBi (Left1 trmPnt))

-- | the induced initials.
zrPointInitials :: Distributive x => ZeroPoint x -> Initials x
zrPointInitials = LimitsG . const . zrPointInitial
