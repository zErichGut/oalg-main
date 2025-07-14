
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds  #-}

-- |
-- Module      : OAlg.Hom.Fibred
-- Description : homomorphisms between fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Fibred' structures
module OAlg.Hom.Fibred
  (

    -- * Fibred
    HomFibred, FunctorialFibred

    -- * Fibred Oriented
  , HomFibredOriented
  , HomDisjunctiveFibredOriented

    -- * Proposition
  , prpHomFbr
  , prpHomFbrOrt
  , prpHomDisjFbrOrt
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented.Definition

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- HomFibred -

-- | homomorphisms between 'Fibred' structures.
--
-- __Property__ Let @'HomFibred' __h__@, then for all @__x__@, @__y__@ and @h@ in
-- @__h x y__@ holds:
--
-- (1) @'root' '.' 'amap' h '.=.' 'rmap' h '.' 'root'@.
class ( Morphism h, Applicative h, ApplicativeRoot h
      , Transformable (ObjectClass h) Fbr
      ) => HomFibred h where

instance HomFibred h => HomFibred (Path h)
instance TransformableFbr s => HomFibred (IdHom s)

--------------------------------------------------------------------------------
-- prpHomFbr -

relHomFbrStruct :: (HomFibred h, Show2 h)
  => Homomorphous Fbr x y -> h x y -> x -> Statement
relHomFbrStruct (Struct :>: Struct) h x
  = (root (amap h x) == rmap h (root x)) :?> Params ["h":=show2 h, "x":=show x]

-- | validity according to 'HomFibred'.
prpHomFbr :: (HomFibred h, Show2 h) => h x y -> x -> Statement
prpHomFbr h x = Prp "HomFbr" :<=>: relHomFbrStruct (tauHom (homomorphous h)) h x

--------------------------------------------------------------------------------
-- Functorialibred -

-- | functorial application of 'Fibred' homomorphisms.
type FunctorialFibred h = (HomFibred h, Functorial h, FunctorialRoot h)

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



{-
--------------------------------------------------------------------------------
-- Hom -

type instance Hom FbrOrt h = HomFibredOriented h

--------------------------------------------------------------------------------
-- IdHom - Hom -

instance ApplicativeRoot (IdHom s) where
  rmap IdHom r = r
  
instance (TransformableFbr s, TransformableTyp s) => HomFibred (IdHom s)
  
instance ( TransformableOp s, TransformableOrt s, TransformableFbr s
         , TransformableFbrOrt s, TransformableTyp s
         )
  => HomFibredOriented (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance TransformableFbrOrt s => ApplicativeRoot (HomOp s)

instance ( TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibred (HomOp s)


instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibredOriented (HomOp s)

instance TransformableFbrOrt s => ApplicativeRoot (IsoOp s)

instance (TransformableFbr s, TransformableFbrOrt s, TransformableTyp s) => HomFibred (IsoOp s)

instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibredOriented (IsoOp s)

--------------------------------------------------------------------------------
-- OpHom -

instance HomFibredOriented h => ApplicativeRoot (OpHom h)
instance HomFibredOriented h => HomFibred (OpHom h)
instance HomFibredOriented h => HomFibredOriented (OpHom h)


-}
