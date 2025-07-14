
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
  , HomDisjunctiveFibredOriented

    -- * Proposition
  , prpHomFbr
  , prpHomFbrOrt
  , prpHomDisjFbrOrt
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
-- prpHomFbrOrt -

relHomFbrOrtStruct :: (HomFibredOriented h, Show2 h)
  => Homomorphous FbrOrt x y -> h x y -> Root x -> Statement
relHomFbrOrtStruct (Struct :>: Struct) h r
  = (rmap h r == omap h r) :?> Params ["h":=show2 h,"r":=show r]

prpHomFbrOrt :: (HomFibredOriented h, Show2 h)
  => h x y -> Root x -> Statement
prpHomFbrOrt h r = Prp "HomFbrOrt"
  :<=>: relHomFbrOrtStruct (tauHom (homomorphous h)) h r

--------------------------------------------------------------------------------
-- HomDisjunctiveFibredOriented -

-- | type family of homomorphisms between 'FibredOriented' structures where 'rmap' is given by
-- 'omapDisj'.
--
-- __Property__ Let @'HomDisjunctiveFibredOriented' __h__@, then for all @__x__@, @__y__@ and
-- @h@ in @__h x y__@ holds:
--
-- (1) @'rmap' h '.=.' 'omapDisj' h@.
class (HomDisjunctiveOriented h , HomFibred h, Transformable (ObjectClass h) FbrOrt)
  => HomDisjunctiveFibredOriented h

instance HomDisjunctiveFibredOriented h => HomDisjunctiveFibredOriented (Path h)
instance ( TransformableOrt s, TransformableFbr s
         , TransformableFbrOrt s
         ) => HomDisjunctiveFibredOriented (IdHom s)


--------------------------------------------------------------------------------
-- prpHomDisjFbrOrt -

relHomDisjFbrOrtHomomorphous :: (HomDisjunctiveFibredOriented h, Show2 h)
  => Homomorphous FbrOrt x y -> h x y -> Root x -> Statement
relHomDisjFbrOrtHomomorphous (Struct :>: Struct) h r
  = (rmap h r == omapDisj h r) :?> Params ["h":=show2 h,"r":=show r]


-- | validity according to 'HomFibredOriented'.
prpHomDisjFbrOrt :: (HomDisjunctiveFibredOriented h, Show2 h) => h a b -> Root a -> Statement
prpHomDisjFbrOrt f r = Prp "HomDisjFbrOrt"
  :<=>: relHomDisjFbrOrtHomomorphous (tauHom (homomorphous f)) f r

--------------------------------------------------------------------------------
-- DualisableFibredOriented -

-- | duality according to @__o__@ on 'FibredOriented'-structures.
--
-- __Property__ Let @'DualisableFibredOriented' __s o__@ then for all @__x__@ and
-- @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'toDualRt' q s '.=.' 'toDualOrt' q s@.
class ( DualisableOriented s o, DualisableG s (->) o Rt
      , Transformable s FbrOrt
      ) => DualisableFibredOriented s o

instance ( TransformableOrt s, TransformableFbrOrt s, TransformableOp s
         )
  => DualisableFibredOriented s Op

--------------------------------------------------------------------------------
-- prpDualisableFibredOriented -

relDualisableFibredOriented :: DualisableFibredOriented s o
  => q o -> Struct s x -> Struct FbrOrt x -> Struct FbrOrt (o x) -> Root x -> Statement
relDualisableFibredOriented q s Struct Struct r
  = (toDualRt q s r == toDualOrt q s r) :?> Params ["r":=show r]

-- | validity according to 'DualisableFibredOrientd'.
prpDualisableFibredOriented :: DualisableFibredOriented s o
  => q o -> Struct s x -> X (Root x) -> Statement
prpDualisableFibredOriented q s xr = Prp "DualisableFibredOriented" :<=>:
  Forall xr (relDualisableFibredOriented q s (tau s) (tau (tauO s)))

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

instance ( HomFibredOriented h, DualisableFibredOriented s o
         , Transformable s Fbr
         ) => HomFibred (HomDisj s o h)

instance ( HomFibredOriented h, DualisableFibredOriented s o
         , Transformable s Fbr
         ) => HomDisjunctiveFibredOriented (HomDisj s o h)

--------------------------------------------------------------------------------
-- isoOpFbrOrt -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOpFbrOrt :: FibredOriented x => Variant2 Contravariant (Inv2 (HomDisjEmpty FbrOrt Op)) x (Op x)
isoOpFbrOrt = isoOp Struct


