
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
  , isoToOpOpDst, isoFromOpOpDst
  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Constructable

import OAlg.Structure.Oriented.Definition hiding (Path(..))
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Distributive.Definition

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition
import OAlg.Hom.Multiplicative.Definition
import OAlg.Hom.Fibred
import OAlg.Hom.Additive

--------------------------------------------------------------------------------
-- HomDistributive -

-- | type family of homomorphisms between 'Distributive' structures.
class ( HomMultiplicative h, HomAdditive h
      , HomFibredOriented h, Transformable (ObjectClass h) Dst 
      )
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

instance ( TransformableOrt s, TransformableOp s, TransformableTyp s
         , TransformableMlt s
         , TransformableFbr s, TransformableAdd s
         , TransformableFbrOrt s
         , TransformableDst s
         )
  => HomDistributive (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance ( TransformableOrt s, TransformableOp s, TransformableTyp s
         , TransformableMlt s
         , TransformableFbr s, TransformableAdd s
         , TransformableFbrOrt s
         , TransformableDst s
         , Typeable s
         )
  => HomDistributive (HomOp s)


instance ( TransformableOrt s, TransformableOp s, TransformableTyp s
         , TransformableMlt s
         , TransformableFbr s, TransformableAdd s
         , TransformableFbrOrt s
         , TransformableDst s
         , Typeable s
         )
  => HomDistributive (IsoOp s)

--------------------------------------------------------------------------------
-- isoToOpOpDst -

-- | the induced isomorphism of 'Distributive' structures given by 'ToOpOp'.
isoToOpOpDst :: Distributive a => IsoOp Dst a (Op (Op a))
isoToOpOpDst = make (ToOpOp :. IdPath Struct)

--------------------------------------------------------------------------------
-- isoFromOpOpDst -

-- | the induced isomorphism of 'Distributive' structures given by 'FromOpOp'.
isoFromOpOpDst :: Distributive a => IsoOp Dst (Op (Op a)) a
isoFromOpOpDst = make (FromOpOp :. IdPath Struct)

--------------------------------------------------------------------------------
-- OpHom -

instance HomDistributive h => HomDistributive (OpHom h)

