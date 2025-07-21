
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Hom.Fibred.Oriented
-- Description : homomorphisms between fibred oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'FibredOOriented' structures
module OAlg.Hom.Fibred.Oriented
  (
    -- * Fibred Oriented
    HomFibredOriented
  , HomFibredOrientedDisjunctive
  , DualisableFibredOriented, toDualRt
  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.Path

import OAlg.Data.Variant

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented hiding (Path(..))

import OAlg.Hom.Fibred.Definition
import OAlg.Hom.Oriented

--------------------------------------------------------------------------------
-- toDualRt -

-- | the dual root induced by @'DualisableG' __s__ (->) __o__ 'Rt'@.
toDualRt :: DualisableFibredOriented s o => q o -> Struct s x -> Root x -> Root (o x)
toDualRt q s = fromRtG (toDualG' (d q s) s) where
  d :: DualisableFibredOriented s o => q o -> Struct s x -> DualityG s (->) o Rt
  d _ _ = DualityG

instance (HomFibredOriented h, DualisableFibredOriented s o)
  => ApplicativeG Rt (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h

instance (HomFibredOriented h, DualisableFibredOriented s o)
  => HomFibred (HomDisj s o h)

instance (HomFibredOriented h, DualisableFibredOriented s o)
  => HomFibredOrientedDisjunctive (HomDisj s o h)

--------------------------------------------------------------------------------
-- isoOpFbrOrt -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOpFbrOrt :: FibredOriented x => Variant2 Contravariant (Inv2 (HomDisjEmpty FbrOrt Op)) x (Op x)
isoOpFbrOrt = isoOp Struct


