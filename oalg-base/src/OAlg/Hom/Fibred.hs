
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Hom.Fibred
-- Description : definition of homomorphisms between fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of homomorphisms between 'Fibred' structures
module OAlg.Hom.Fibred
  (
    -- * Fibred
    HomFibred, FunctorialFibred

    -- * Duality
  , DualisableFibred
  , toDualStk, toDualRt

    -- * X
  , xsoFbrOrtX

    -- * Proposition
  , prpHomFbr, prpHomDisjOpFbr
  )
  where

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Variant

import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Oriented hiding (Path(..))

import OAlg.Hom.Definition

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
instance TransformableFbr s => HomFibred (HomEmpty s)

instance (HomFibred h, Disjunctive2 h)  => HomFibred (Variant2 v h)

instance HomFibred h => HomFibred (Inv2 h)

--------------------------------------------------------------------------------
-- DualisableFibred -

-- | duality according to @__o__@ on 'FibredOriented' structures.
--
-- __Properties__ Let @'DualisableFibred' __s o__@, then
-- for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'root' '.' 'toDualStk' q s '.=.' 'toDualRt' q s '.' 'root'@.
--
-- where @q@ is any proxy for @__o__@.
class (DualisableG s (->) o Id, DualisableG s (->) o Rt, Transformable s Fbr)
  => DualisableFibred s o

instance (TransformableType s, TransformableFbrOrt s, TransformableOp s) => DualisableFibred s Op

--------------------------------------------------------------------------------
-- toDualStk -

-- | the dual stalk ginven by @'DualisableFibred' __s o__@ and induced by
-- @'DualisableG' __s__ (->) __o__ 'Id'@.
toDualStk :: DualisableFibred s o => q o -> Struct s x -> x -> o x
toDualStk _ s = fromIdG (toDualG' (d s) s) where
  d :: DualisableFibred s o => Struct s x -> DualityG s (->) o Id
  d _ = DualityG

--------------------------------------------------------------------------------
-- toDualRt -

-- | the dual root ginven by @'DualisableFibred' __s o__@ and induced by
-- @'DualisableG' __s__ (->) __o__ 'Rt'@.
toDualRt :: DualisableFibred s o => q o -> Struct s x -> Root x -> Root (o x)
toDualRt q s = fromRtG (toDualG' (d q s) s) where
  d :: DualisableFibred s o => q o -> Struct s x -> DualityG s (->) o Rt
  d _ _ = DualityG

--------------------------------------------------------------------------------
-- HomDisj - HomFibred -

instance (HomFibred h, DualisableG s (->) o Rt) => ApplicativeG Rt (HomDisj s o h) (->) where
  amapG (HomDisj h) = smap h

instance (HomFibred h, DualisableG s (->) o Rt) => FunctorialG Rt (HomDisj s o h) (->)

instance (HomFibred h, DualisableFibred s o) => HomFibred (HomDisj s o h)

--------------------------------------------------------------------------------
-- Functorialibred -

-- | functorial morphism, i.e. 'Functorial' and 'FunctorialRoot'.
--
-- __Note__ It's not mandatory being an homomorphism!
class (Functorial h, FunctorialRoot h) => FunctorialFibred h

instance (HomFibred h, DualisableFibred s o) => FunctorialFibred (HomDisj s o h)

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
-- xsoFbrOrtX -

xsoFbrOrtX :: s ~ FbrOrtX => X (SomeObjectClass (SHom s s Op (HomEmpty s)))
xsoFbrOrtX = xOneOf [ SomeObjectClass (Struct :: Struct FbrOrtX OS)
                    , SomeObjectClass (Struct :: Struct FbrOrtX (Op OS))
                    , SomeObjectClass (Struct :: Struct FbrOrtX N)
                    ]

--------------------------------------------------------------------------------
-- prpHomDisOpFbr -

relHomFbrFbrOrtX :: (HomFibred h, Show2 h)
  => Homomorphous FbrOrtX x y -> h x y -> Statement
relHomFbrFbrOrtX (Struct :>: Struct) h
  = Forall xStandard (prpHomFbr h)

relHomDisjOpFbr :: (HomFibred h, Show2 h, Transformable s FbrOrtX, DualisableFibred s o)
  => X (SomeMorphism (HomDisj s o h)) -> Statement
relHomDisjOpFbr xsh = Forall xsh
  (\(SomeMorphism h) -> relHomFbrFbrOrtX (tauHom (homomorphous h)) h)

prpHomDisjOpFbr :: Statement
prpHomDisjOpFbr = Prp "HomDisjOpFbr" :<=>: relHomDisjOpFbr xsh where
  xsh :: X (SomeMorphism (HomDisjEmpty FbrOrtX Op))
  xsh = amap1 smCmpb2 $ xscmHomDisj xsoFbrOrtX XEmpty
