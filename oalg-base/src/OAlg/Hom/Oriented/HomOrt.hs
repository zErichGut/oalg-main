
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.Hom.Oriented.HomOrt
-- Description : homomorpisms between 'Oriented' structure.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Homomorpisms between 'Oriented' structure..
module OAlg.Hom.Oriented.HomOrt
  (
    -- * HomOrt
    HomOrt(..), homOrt

    -- ** HomOrtEmpty
  , HomOrtEmpty, isoOpOrt
  , HomEmpty

    -- * Iso
  , IsoOp
  )
  where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Fibred.Definition

import OAlg.Hom.Oriented.Definition
import OAlg.Hom.Fibred


--------------------------------------------------------------------------------
-- HomEmpty -

-- | the empty homomorphism.
newtype HomEmpty s x y = HomEmpty (EntEmpty2 x y)
  deriving (Show, Show2,Eq,Eq2,EqExt,Validable,Validable2)

--------------------------------------------------------------------------------
-- fromHomEmpty -

fromHomEmpty :: HomEmpty s a b -> x
fromHomEmpty (HomEmpty e) = fromEmpty2 e

--------------------------------------------------------------------------------
-- HomEmpty - Instances -

instance ApplicativeG t (HomEmpty s) c where amapG = fromHomEmpty

--------------------------------------------------------------------------------
-- HomEmpty - HomOriented -

instance Morphism (HomEmpty s) where
  type ObjectClass (HomEmpty s) = s
  domain = fromHomEmpty
  range  = fromHomEmpty

instance TransformableOrt s => HomOriented (HomEmpty s)


--------------------------------------------------------------------------------
-- HomOrt -

newtype HomOrt s o h x y = HomOrt (SHom Ort s o h x y)
  deriving (Show,Show2,Validable,Validable2,Disjunctive,Disjunctive2)

deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq2 (HomOrt s o h)
deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq (HomOrt s o h x y)

instance HomOriented h => Morphism (HomOrt s o h) where
  type ObjectClass (HomOrt s o h) = s
  homomorphous (HomOrt h) = homomorphous h

instance HomOriented h => Category (HomOrt s o h) where
  cOne = HomOrt . cOne 
  HomOrt f . HomOrt g = HomOrt (f . g)

instance HomOriented h => CategoryDisjunctive (HomOrt s o h)

instance (HomOriented h, TransformableGRefl o s) => CategoryDualisable o (HomOrt s o h) where
  cToDual s   = Contravariant2 (HomOrt t) where Contravariant2 t = cToDual s
  cFromDual s = Contravariant2 (HomOrt f) where Contravariant2 f = cFromDual s

instance (HomOriented h, DualisableOriented s o) => ApplicativeG Id (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, DualisableOriented s o) => FunctorialG Id (HomOrt s o h) (->)


instance (HomOriented h, DualisableOriented s o) => ApplicativeG Pnt (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, DualisableOriented s o) => FunctorialG Pnt (HomOrt s o h) (->)

instance (HomOriented h, DualisableOriented s o) => HomDisjunctiveOriented (HomOrt s o h)

instance (HomOriented h, DualisableOriented s o) => FunctorialOriented (HomOrt s o h)

rmapDisjFbrtOrtStruct :: (ApplicativePoint h, Disjunctive2 h)
  => Homomorphous FbrOrt x y -> h x y -> Root x -> Root y
rmapDisjFbrtOrtStruct (Struct :>: Struct) = omapDisj

rmapDisjFbrOrt :: ( Morphism h, Transformable (ObjectClass h) FbrOrt
                  , ApplicativePoint h, Disjunctive2 h
                  )
  => h x y -> Root x -> Root y
rmapDisjFbrOrt h = rmapDisjFbrtOrtStruct (tauHom $ homomorphous h) h
  
instance ( HomOriented h, DualisableOriented s o
         , Transformable s FbrOrt
         ) => ApplicativeG Rt (HomOrt s o h) (->) where
  amapG = amapRt . rmapDisjFbrOrt

instance ( HomOriented h, DualisableOriented s o
         , Transformable s Fbr, Transformable s FbrOrt
         ) => HomFibred (HomOrt s o h)

instance ( HomOriented h, DualisableOriented s o
         , Transformable s Fbr, Transformable s FbrOrt
         ) => HomFibredOriented (HomOrt s o h)

--------------------------------------------------------------------------------
-- homOrt -

-- | embedding of 'HomOriented' to 'HomOrt'.
homOrt :: (HomOriented h, Transformable (ObjectClass h) s)
  => h x y -> Variant2 Covariant (HomOrt s o h) x y
homOrt h = Covariant2 (HomOrt h') where Covariant2 h' = sCov h

--------------------------------------------------------------------------------
-- HomOrtEmpty -

type HomOrtEmpty s o = HomOrt s o (HomEmpty s)

instance TransformableGObjectClassDomain Id (HomOrt OrtX Op (HomEmpty OrtX)) EqEOrt
instance TransformableGObjectClassDomain Pnt (HomOrt OrtX Op (HomEmpty OrtX)) EqEOrt
instance TransformableObjectClass OrtX (HomOrt OrtX Op (HomEmpty OrtX))
instance Transformable s Typ => EqExt (HomOrtEmpty s Op)

--------------------------------------------------------------------------------
-- IsoOp -

type IsoOp s x = Variant2 Contravariant (Inv2 (HomOrtEmpty s Op)) x (Op x)

--------------------------------------------------------------------------------
-- isoOpOrt -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOpOrt :: Oriented x => Variant2 Contravariant (Inv2 (HomOrtEmpty Ort Op)) x (Op x)
isoOpOrt = Contravariant2 (Inv2 t f) where
  Contravariant2 t = cToDual Struct
  Contravariant2 f = cFromDual Struct

--------------------------------------------------------------------------------
-- isoOpFbrOrt -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOpFbrOrt :: FibredOriented x => Variant2 Contravariant (Inv2 (HomOrtEmpty FbrOrt Op)) x (Op x)
isoOpFbrOrt = Contravariant2 (Inv2 t f) where
  Contravariant2 t = cToDual Struct
  Contravariant2 f = cFromDual Struct

