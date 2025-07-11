
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
-- Module      : OAlg.Hom.Oriented.HomDisj
-- Description : disjunctive homomorpisms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Disjunctive homomorpisms between 'Oriented' structure.
module OAlg.Hom.Oriented.HomDisj
  (
    -- * HomDisj
    HomDisj(..), homDisj

    -- ** HomDisjEmpty
  , HomDisjEmpty
  , HomEmpty

    -- * Dualisable
  , DualisableOriented
  , toDualArw, toDualPnt
  
    -- * Iso
  , IsoOp, isoOp
  , isoOpOrt, isoOpFbrOrt
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
-- DualisableOriented -

-- | duality according to @__o__@ on 'Oriented'-structures
--
-- __Properties__ Let @'DualisableOriented' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) @'start' '.' 'toDualArw' q s '.=.' 'toDualPnt' q s '.' 'end'@.
--
-- (2) @'end' '.' 'toDualArw' q s '.=.' 'toDualPnt' q s '.' 'start'@.
--
-- where @q@ is any proxy for @__o__@.
--
-- __Note__ The above property is equivalent to
-- @'orientation' '.' 'toDualArw' '.=.' 'toDualOrt' '.' 'orientation'@.
class (DualisableG s (->) o Id, DualisableG s (->) o Pnt, Transformable s Ort)
  => DualisableOriented s o

instance (TransformableOrt s, TransformableOp s) => DualisableOriented s Op

--------------------------------------------------------------------------------
-- toDualArw -

-- | the dual arrow induced by @'DualisableG __s__ (->) __o__ 'Id'@.
toDualArw :: DualisableOriented s o => q o -> Struct s x -> x -> o x
toDualArw _ s = fromIdG (toDualG' (d s) s) where
  d :: DualisableOriented s o => Struct s x -> DualityG s (->) o Id
  d _ = DualityG

--------------------------------------------------------------------------------
-- toDualPnt -

-- | the dual point induced by @'DualisableG' __s__ (->) __o__ 'Pnt'@.
toDualPnt :: DualisableOriented s o => q o -> Struct s x -> Point x -> Point (o x)
toDualPnt q s = fromPntG (toDualG' (d q s) s) where
  d :: DualisableOriented s o => q o -> Struct s x -> DualityG s (->) o Pnt
  d _ _ = DualityG

--------------------------------------------------------------------------------
-- toDualOrt -

-- | the induced dual orientation.
toDualOrt :: DualisableOriented s o => q o -> Struct s x
  -> Orientation (Point x) -> Orientation (Point (o x))
toDualOrt q st (s :> e) = t e :> t s where t = toDualPnt q st

--------------------------------------------------------------------------------
-- HomDisj -

newtype HomDisj s o h x y = HomDisj (SHom s s o h x y)
  deriving (Show,Show2,Validable,Validable2,Disjunctive,Disjunctive2)

deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq2 (HomDisj s o h)
deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq (HomDisj s o h x y)

instance HomOriented h => Morphism (HomDisj s o h) where
  type ObjectClass (HomDisj s o h) = s
  homomorphous (HomDisj h) = homomorphous h

instance HomOriented h => Category (HomDisj s o h) where
  cOne = HomDisj . cOne 
  HomDisj f . HomDisj g = HomDisj (f . g)

instance HomOriented h => CategoryDisjunctive (HomDisj s o h)

instance (HomOriented h, TransformableGRefl o s) => CategoryDualisable o (HomDisj s o h) where
  cToDual s   = Contravariant2 (HomDisj t) where Contravariant2 t = cToDual s
  cFromDual s = Contravariant2 (HomDisj f) where Contravariant2 f = cFromDual s

instance (HomOriented h, DualisableOriented s o) => ApplicativeG Id (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h

instance (HomOriented h, DualisableOriented s o) => FunctorialG Id (HomDisj s o h) (->)


instance (HomOriented h, DualisableOriented s o) => ApplicativeG Pnt (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h

instance (HomOriented h, DualisableOriented s o) => FunctorialG Pnt (HomDisj s o h) (->)

instance (HomOriented h, DualisableOriented s o) => HomDisjunctiveOriented (HomDisj s o h)


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
-- homDisj -

-- | embedding of 'HomOriented' to 'HomDisj'.
homDisj :: (HomOriented h, Transformable (ObjectClass h) s)
  => h x y -> Variant2 Covariant (HomDisj s o h) x y
homDisj h = Covariant2 (HomDisj h') where Covariant2 h' = sCov h

--------------------------------------------------------------------------------
-- HomDisjEmpty -

type HomDisjEmpty s o = HomDisj s o (HomEmpty s)

instance TransformableGObjectClassDomain Id (HomDisj OrtX Op (HomEmpty OrtX)) EqEOrt
instance TransformableGObjectClassDomain Pnt (HomDisj OrtX Op (HomEmpty OrtX)) EqEOrt
instance TransformableObjectClass OrtX (HomDisj OrtX Op (HomEmpty OrtX))
instance Transformable s Typ => EqExt (HomDisjEmpty s Op)

--------------------------------------------------------------------------------
-- IsoOp -

type IsoOp s x = Variant2 Contravariant (Inv2 (HomDisjEmpty s Op)) x (Op x)

--------------------------------------------------------------------------------
-- isoOp -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOp :: (TransformableOrt s, TransformableGRefl Op s)
  => Struct s x -> Variant2 Contravariant (Inv2 (HomDisjEmpty s Op)) x (Op x)
isoOp s = Contravariant2 (Inv2 t f) where
  Contravariant2 t = cToDual s
  Contravariant2 f = cFromDual s


--------------------------------------------------------------------------------
-- isoOpOrt -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOpOrt :: Oriented x => Variant2 Contravariant (Inv2 (HomDisjEmpty Ort Op)) x (Op x)
isoOpOrt = isoOp Struct

--------------------------------------------------------------------------------
-- isoOpFbrOrt -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOpFbrOrt :: FibredOriented x => Variant2 Contravariant (Inv2 (HomDisjEmpty FbrOrt Op)) x (Op x)
isoOpFbrOrt = isoOp Struct

