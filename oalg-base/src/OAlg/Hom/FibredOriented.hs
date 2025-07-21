

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}


-- |
-- Module      : OAlg.Hom.FibredOriented
-- Description : definition of homomorphisms between fibred oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of homomorphisms between 'FibreOriented' structures.
module OAlg.Hom.FibredOriented
  (
  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify
import OAlg.Category.Path

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Fibred

import OAlg.Hom.Definition
import OAlg.Hom.Fibred
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
class (HomFibred h, HomOriented h, Transformable (ObjectClass h) FbrOrt)
  => HomFibredOriented h

instance HomFibredOriented h => HomFibredOriented (Path h)
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
class (HomFibred h, HomOrientedDisjunctive h, Transformable (ObjectClass h) FbrOrt)
  => HomFibredOrientedDisjunctive h

instance HomFibredOrientedDisjunctive h => HomFibredOrientedDisjunctive (Path h)

--------------------------------------------------------------------------------
-- DualisableFibredOriented -

-- | duality according to @__o__@ on 'FibredOriented'-structures.
--
-- __Property__ Let @'DualisableFibredOriented' __s o__@ then for all @__x__@ and
-- @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'toDualStk' q s '.=.' 'toDualArw' q s@.
--
-- (2) @'toDualRt' q s '.=.' 'toDualOrt' q s@.
class ( DualisableFibred s o, DualisableOriented s o
      , Transformable s FbrOrt
      ) => DualisableFibredOriented s o

instance (TransformableType s, TransformableOrt s, TransformableFbrOrt s, TransformableOp s)
  => DualisableFibredOriented s Op

instance (HomFibredOriented h, DualisableFibredOriented s o)
  => HomFibredOrientedDisjunctive (HomDisj s o h)

