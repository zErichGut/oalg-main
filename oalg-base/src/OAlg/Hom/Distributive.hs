
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

    -- * Iso
  , isoOpDst
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.Additive

--------------------------------------------------------------------------------
-- HomDistributive -

-- | covariant homomorphisms between 'Distributive' structures.
class (HomFibredOriented h, HomMultiplicative h, HomAdditive h, Transformable (ObjectClass h) Dst)
  => HomDistributive h

instance HomDistributive h => HomDistributive (Path h)
instance ( TransformableOrt s, TransformableFbr s, TransformableMlt s
         , TransformableFbrOrt s, TransformableAdd s
         , TransformableDst s
         ) => HomDistributive (IdHom s)

--------------------------------------------------------------------------------
--  HomDistrubutiveDisjunctive -


-- | disjunctive homomorphisms between 'Distributive' structures.
class ( HomFibredOrientedDisjunctive h, HomMultiplicativeDisjunctive h, HomAdditive h
      , Transformable (ObjectClass h) Dst
      )
  => HomDistributiveDisjunctive h

instance ( HomDistributive h, DualisableMultiplicative s o, DualisableAdditve s o
         , Transformable s Dst
         ) => HomDistributiveDisjunctive (HomDisj s o h)


--------------------------------------------------------------------------------
-- isoOpDst -

isoOpDstStruct :: Struct Dst x -> Variant2 Contravariant (Inv2 (HomDisjEmpty Dst Op)) x (Op x)
isoOpDstStruct s@Struct = isoOp s

isoOpDst :: Distributive x =>  Variant2 Contravariant (Inv2 (HomDisjEmpty Dst Op)) x (Op x)
isoOpDst = isoOpDstStruct Struct

{-
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
         )
  => HomDistributive (HomOp s)


instance ( TransformableOrt s, TransformableOp s, TransformableTyp s
         , TransformableMlt s
         , TransformableFbr s, TransformableAdd s
         , TransformableFbrOrt s
         , TransformableDst s
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

-}
