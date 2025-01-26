
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Hom.Distributive
-- Description : homomorphisms between distributive structure
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Distributive' structure.
module OAlg.Hom.Distributive
  ( -- * Distributive
    HomDistributive, IsoDistributive

    -- * Iso
  , isoFromOpOpDst
  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Constructable

import OAlg.Structure.Distributive.Definition

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition
import OAlg.Hom.Multiplicative.Definition
import OAlg.Hom.Fibred
import OAlg.Hom.Additive

--------------------------------------------------------------------------------
-- HomDistributive -

-- | type family of homomorphisms between 'Distributive' structures.
class (EmbeddableMorphism h Dst, HomFibredOriented h, HomMultiplicative h, HomAdditive h)
  => HomDistributive h

instance HomDistributive h => HomDistributive (Path h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom Dst h = HomDistributive h

--------------------------------------------------------------------------------
-- IsoDistributive -

-- | isomorphisms between 'Distributive' structures.
type IsoDistributive h = ( FunctorialHomOriented h, Cayleyan2 h
                         , HomDistributive h
                         )

--------------------------------------------------------------------------------
-- HomDistributive - Instance -

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s)
  => HomDistributive (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomDistributive (HomOp s)
instance (TransformableOp s, ForgetfulDst s, ForgetfulTyp s, Typeable s)
  => HomDistributive (IsoOp s)

--------------------------------------------------------------------------------
-- isoFromOpOpDst -

-- | the induced isomorphism of 'Distributive' structures given by 'FromOpOp'.
isoFromOpOpDst :: Distributive a => IsoOp Dst (Op (Op a)) a
isoFromOpOpDst = make (FromOpOp :. IdPath Struct)

--------------------------------------------------------------------------------
-- OpHom -

instance HomDistributive h => HomDistributive (OpHom h)
