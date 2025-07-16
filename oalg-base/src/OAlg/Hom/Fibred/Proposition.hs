
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
-- prpHomFbr -

relHomFbrStruct :: (HomFibred h, Show2 h)
  => Homomorphous Fbr x y -> h x y -> x -> Statement
relHomFbrStruct (Struct :>: Struct) h x
  = (root (amap h x) == rmap h (root x)) :?> Params ["h":=show2 h, "x":=show x]

-- | validity according to 'HomFibred'.
prpHomFbr :: (HomFibred h, Show2 h) => h x y -> x -> Statement
prpHomFbr h x = Prp "HomFbr" :<=>: relHomFbrStruct (tauHom (homomorphous h)) h x

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
-- prpHomDisjFbrOrt -

prpHomDisjFbrOrtFbrOrtX :: (HomDisjunctiveFibredOriented h, Show2 h)
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
-- 'HomDisjunctiveFibredOriented'.
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

xfgFbrOrtX :: X (SomeCmpb2 (HomDisjEmpty FbrOrtX Op))
xfgFbrOrtX = xscmHomDisj xsoFbrOrtX XEmpty

dstFbrOrtX :: Int -> IO ()
dstFbrOrtX n = putDstr asp n xfgFbrOrtX where
  asp (SomeCmpb2 f g) = [ show $ variant2 (f . g)
                        , show $ variant2 f
                        , show $ variant2 g
                        ]
