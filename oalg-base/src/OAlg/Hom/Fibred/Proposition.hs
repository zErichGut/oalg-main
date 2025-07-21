
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
-- Module      : OAlg.Hom.Fibred.Proposition
-- Description : propositions for homomorphisms between fibred structures.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Propositions for homomorphisms between fibred structures.
module OAlg.Hom.Fibred.Proposition
  (
    prpHomFbr    
  , prpHomFbrOrt
  , prpHomDisjFbrOrt
  , prpHomDisjOpFbrOrt
  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented hiding (Path(..))

import OAlg.Hom.Oriented
import OAlg.Hom.Fibred.Definition
import OAlg.Hom.Fibred.Oriented

--------------------------------------------------------------------------------
-- prpHomDisjFbrOrt -

prpHomDisjFbrOrtFbrOrtX :: (HomFibredOrientedDisjunctive h, Show2 h)
  => Homomorphous FbrOrtX x y -> h x y -> Statement
prpHomDisjFbrOrtFbrOrtX (Struct :>: Struct) h = Forall xStandard (prpHomDisjFbrOrt h)

prpHomFbrFbrOrtX :: (HomFibred h, Show2 h)
  => Homomorphous FbrOrtX x y -> h x y -> Statement
prpHomFbrFbrOrtX (Struct :>: Struct) h = Forall xStandard (prpHomFbr h)

relHomDisjFbrOrt :: X (SomeMorphism (HomDisjEmpty FbrOrtX Op)) -> Statement
relHomDisjFbrOrt xsa = Forall xsa
  (\(SomeMorphism h)
  -> And [ prpHomDisjFbrOrtFbrOrtX (tauHom (homomorphous h)) h
         , prpHomFbrFbrOrtX (tauHom (homomorphous h)) h
         ] 
  ) 

-- | validity of @'HomDisjEmpty' 'FbrOrt' 'Op'@ according to 'HomFibred' and
-- 'HomFibredOrientedDisjunctive'.
prpHomDisjOpFbrOrt :: Statement
prpHomDisjOpFbrOrt = Prp "HomDisjOpFbrOrt" :<=>: relHomDisjFbrOrt xsa where
  xsa :: X (SomeMorphism (HomDisjEmpty FbrOrtX Op))
  xsa = amap1 smCmpb2 $ xscmHomDisj xsoFbrOrtX XEmpty

--------------------------------------------------------------------------------
-- xsoFbrtOrtX -

-- | some object classes for 'FbrOrtX'.
xsoFbrOrtX :: X (SomeObjectClass (SHom FbrOrtX FbrOrtX Op (HomEmpty FbrOrtX)))
xsoFbrOrtX = xOneOf [ SomeObjectClass (Struct :: Struct FbrOrtX OS)
               , SomeObjectClass (Struct :: Struct FbrOrtX N)
               , SomeObjectClass (Struct :: Struct FbrOrtX (Op OS))
               , SomeObjectClass (Struct :: Struct FbrOrtX (Id OS))
               , SomeObjectClass (Struct :: Struct FbrOrtX (Id Z))
               ]

