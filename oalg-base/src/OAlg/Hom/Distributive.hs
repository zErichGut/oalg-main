
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Hom.Distributive
-- Description : homomorphisms between distributive structure
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Distributive' structure.
module OAlg.Hom.Distributive
  (
    -- * Distributive
    HomDistributive, HomDistributiveDisjunctive
  , DualisableDistributive

    -- * Iso
  , toDualOpDst
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Variant

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Definition
import OAlg.Hom.Multiplicative
import OAlg.Hom.FibredOriented
import OAlg.Hom.Additive

--------------------------------------------------------------------------------
-- HomDistributive -

-- | covariant homomorphisms between 'Distributive' structures.
class (HomFibredOriented h, HomMultiplicative h, HomAdditive h, Transformable (ObjectClass h) Dst)
  => HomDistributive h

instance HomDistributive h => HomDistributive (Path h)
instance
  ( TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
  , TransformableMlt s, TransformableAdd s, TransformableDst s
  )
  => HomDistributive (HomEmpty s)

type instance Hom Dst h = HomDistributive h

--------------------------------------------------------------------------------
-- DualisableDistributive -

-- | duality according to @__o__@ on 'Distributive' structures.
type DualisableDistributive s o
  = ( DualisableFibredOriented s o, DualisableMultiplicative s o, DualisableAdditive s o
    , Transformable s Dst
    )
  
--------------------------------------------------------------------------------
--  HomDistrubutiveDisjunctive -

-- | disjunctive homomorphisms between 'Distributive' structures.
class ( HomFibredOrientedDisjunctive h, HomMultiplicativeDisjunctive h, HomAdditive h
      , Transformable (ObjectClass h) Dst
      )
  => HomDistributiveDisjunctive h

instance (HomDistributive h, DualisableDistributive s o)
  => HomDistributiveDisjunctive (HomDisj s o h)

instance HomDistributiveDisjunctive h => HomDistributive (Variant2 Covariant h)

type instance HomD Dst h = HomDistributiveDisjunctive h

--------------------------------------------------------------------------------
-- toDualOpDst -

-- | the canonical 'Contravariant' isomorphism on 'Distributive' structures
-- between @__x__@ and @'Op' __x__@.
toDualOpDst :: Distributive x => Variant2 Contravariant (IsoO Dst Op) x (Op x)
toDualOpDst = toDualO Struct

