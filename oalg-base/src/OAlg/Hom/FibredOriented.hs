
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
  ( -- * Disjunctive
    HomFibredOrientedDisjunctive, DualisableFibredOriented

    -- * Covariant
  , HomFibredOriented

    -- * Iso
  , toDualOpFbrOrt

    -- * Proposition
  , prpHomFbrOrt, prpHomFbrOrtDisj
  , prpDualisableFibredOrientedStk, prpDualisableFibredOrientedRt
  , prpHomDisjOpFbrOrt
  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.Unify
import OAlg.Category.Path

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented

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

instance HomFibredOriented h => HomFibredOriented (Inv2 h)

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

instance HomFibredOrientedDisjunctive h => HomFibredOriented (Variant2 Covariant h)

instance
  ( CategoryDisjunctive h
  , HomFibredOrientedDisjunctive h
  )
  => HomFibredOrientedDisjunctive (Inv2 h)

instance (TransformableFbrOrt s, HomFibredOrientedDisjunctive h)
  => HomFibredOrientedDisjunctive (Sub s h)
  
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

--------------------------------------------------------------------------------
-- toDualOpFbrOrt -

-- | the canonical 'Contravariant' isomorphism on 'FibredOriented' structures
-- between @__x__@ and @'Op' __x__@.
toDualOpFbrOrt :: FibredOriented x => Variant2 Contravariant (IsoO FbrOrt Op) x (Op x)
toDualOpFbrOrt = toDualO Struct

--------------------------------------------------------------------------------
-- prpHomFbrOrt -

relHomFbrOrtStruct :: (HomFibredOriented h, Show2 h)
  => Homomorphous FbrOrt x y -> h x y -> Root x -> Statement
relHomFbrOrtStruct (Struct :>: Struct) h r
  = (rmap h r == omap h r) :?> Params ["h":=show2 h,"r":=show r]

-- | validity accordint to 'HomFibredOriented'.
prpHomFbrOrt :: (HomFibredOriented h, Show2 h)
  => h x y -> Root x -> Statement
prpHomFbrOrt h r = Prp "HomFbrOrt"
  :<=>: relHomFbrOrtStruct (tauHom (homomorphous h)) h r

--------------------------------------------------------------------------------
-- prpHomFbrOrtDisj -

relHomFbrOrtDisjHomomorphous :: (HomFibredOrientedDisjunctive h, Show2 h)
  => Homomorphous FbrOrt x y -> h x y -> Root x -> Statement
relHomFbrOrtDisjHomomorphous (Struct :>: Struct) h r
  = (rmap h r == omapDisj h r) :?> Params ["h":=show2 h,"r":=show r]


-- | validity according to 'HomFibredOrientedDisjunctive'.
prpHomFbrOrtDisj :: (HomFibredOrientedDisjunctive h, Show2 h) => h a b -> Root a -> Statement
prpHomFbrOrtDisj f r = Prp "HomFbrOrtDisj"
  :<=>: relHomFbrOrtDisjHomomorphous (tauHom (homomorphous f)) f r

--------------------------------------------------------------------------------
-- prpDualisableFibredOrientedRt -

relDualisableFibredOrientedRt :: DualisableFibredOriented s o
  => q o -> Struct s x -> Struct FbrOrt x -> Struct FbrOrt (o x) -> Root x -> Statement
relDualisableFibredOrientedRt q s Struct Struct r
  = (toDualRt q s r == toDualOrt q s r) :?> Params ["r":=show r]

-- | validity according to 'DualisableFibredOrientd'.
prpDualisableFibredOrientedRt :: DualisableFibredOriented s o
  => q o -> Struct s x -> Root x -> Statement
prpDualisableFibredOrientedRt q s r = Prp "DualisableFibredOrientedRt" :<=>:
  relDualisableFibredOrientedRt q s (tau s) (tau (tauO s)) r

--------------------------------------------------------------------------------
-- prpDualisableFibredOrientedStk -

relDualisableFibredOrientedStk :: DualisableFibredOriented s o
  => q o -> Struct s x -> Struct FbrOrt x -> Struct FbrOrt (o x) -> x -> Statement
relDualisableFibredOrientedStk q s Struct Struct x
  = (toDualStk q s x == toDualArw q s x) :?> Params ["x":=show x]

-- | validity according to 'DualisableFibredOriented'.
prpDualisableFibredOrientedStk :: DualisableFibredOriented s o
  => q o -> Struct s x -> x -> Statement
prpDualisableFibredOrientedStk q s x = Prp "DualisableFibredOriented" :<=>:
  relDualisableFibredOrientedStk q s (tau s) (tau (tauO s)) x

--------------------------------------------------------------------------------
-- prpHomDisjOpFbrOrt -

relHomFbrOrtDisjFbrOrtX :: (HomFibredOrientedDisjunctive h, Show2 h)
  => Homomorphous FbrOrtX x y -> h x y -> Statement
relHomFbrOrtDisjFbrOrtX (Struct :>: Struct) h
  = Forall xStandard (prpHomFbrOrtDisj h)

relHomDisjOpFbrOrt :: X (SomeMorphism (HomDisjEmpty FbrOrtX Op)) -> Statement
relHomDisjOpFbrOrt xsh = Forall xsh
  (\(SomeMorphism h) -> relHomFbrOrtDisjFbrOrtX (tauHom (homomorphous h)) h)

-- | validity of @'HomDisjEmpty' __FbrOrt Op__@ according to 'HomFibredOrientedDisjunctive'.
prpHomDisjOpFbrOrt :: Statement
prpHomDisjOpFbrOrt = Prp "HomDisjOpFbrOrt" :<=>: relHomDisjOpFbrOrt xsh where
  xsh :: X (SomeMorphism (HomDisjEmpty FbrOrtX Op))
  xsh = amap1 smCmpb2 $ xscmHomDisj xsoFbrOrtX XEmpty

--------------------------------------------------------------------------------
-- dstFbrOrtX -

xfgFbrOrtX :: X (SomeCmpb2 (HomDisjEmpty FbrOrtX Op))
xfgFbrOrtX = xscmHomDisj xsoFbrOrtX XEmpty

dstFbrOrtX :: Int -> IO ()
dstFbrOrtX n = putDstr asp n xfgFbrOrtX where
  asp (SomeCmpb2 f g) = [ show $ variant2 (f . g)
                        , show $ variant2 f
                        , show $ variant2 g
                        ]
