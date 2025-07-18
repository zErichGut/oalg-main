
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
-- HomFibredOriented -

-- | type family of homomorphisms between 'FibredOriented' structures where 'rmap' is given by
-- 'omap'.
--
-- __Property__ Let @'HomFibredOriented' __h__@, then for all @__x__@, @__y__@ and
-- @h@ in @__h x y__@ holds:
--
-- (1) @'rmap' h '.=.' 'omap' h@.
class (HomOriented h, HomFibred h, Transformable (ObjectClass h) FbrOrt)
  => HomFibredOriented h

instance HomFibredOriented h => HomFibredOriented (Path h)
instance (TransformableOrt s, TransformableFbr s, TransformableFbrOrt s)
  => HomFibredOriented (IdHom s)
instance (TransformableOrt s, TransformableFbr s, TransformableFbrOrt s)
  => HomFibredOriented (HomEmpty s)

--------------------------------------------------------------------------------
-- HomFibredOrientedDisjunctive -

-- | type family of homomorphisms between 'FibredOriented' structures where 'rmap' is given by
-- 'omapDisj'.
--
-- __Property__ Let @'HomFibredOrientedDisjunctive' __h__@, then for all @__x__@, @__y__@ and
-- @h@ in @__h x y__@ holds:
--
-- (1) @'rmap' h '.=.' 'omapDisj' h@.
class (HomOrientedDisjunctive h , HomFibred h, Transformable (ObjectClass h) FbrOrt)
  => HomFibredOrientedDisjunctive h

instance HomFibredOrientedDisjunctive h => HomFibredOrientedDisjunctive (Path h)
instance ( TransformableOrt s, TransformableFbr s
         , TransformableFbrOrt s
         ) => HomFibredOrientedDisjunctive (IdHom s)


--------------------------------------------------------------------------------
-- DualisableFibredOriented -

-- | duality according to @__o__@ on 'FibredOriented'-structures.
--
-- __Property__ Let @'DualisableFibredOriented' __s o__@ then for all @__x__@ and
-- @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'toDualRt' q s '.=.' 'toDualOrt' q s@.
class ( DualisableOriented s o, DualisableG s (->) o Rt
      , Transformable s Fbr
      , Transformable s FbrOrt
      ) => DualisableFibredOriented s o

instance (TransformableType s, TransformableOrt s, TransformableFbrOrt s, TransformableOp s)
  => DualisableFibredOriented s Op

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


