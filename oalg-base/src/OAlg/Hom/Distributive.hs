
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
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
  , isoOpDst
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Oriented hiding (Path(..))
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


--------------------------------------------------------------------------------
-- isoOpDst -

isoOpDst :: Distributive x => IsoO Dst Op x
isoOpDst = isoO Struct

