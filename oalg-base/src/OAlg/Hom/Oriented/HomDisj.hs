
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

-- | duality according to @__o__@ on @__s__@-structured 'Oriented' types,
--
-- __Properties__ Let @'DualisableOriented' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) @'start' '.' 'toDualArw' q s '.=.' 'toDualPnt' q s '.' 'end'@.
--
-- (2) @'end' '.' 'toDualArw' q s '.=.' 'toDualPnt' q s '.' 'start'@.
--
-- where @q@ is any proxy for @__o__@.
class ( DualisableG s (->) o Id, DualisableG s (->) o Pnt
      , TransformableG o s s, Transformable s Ort
      )
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

{-
--------------------------------------------------------------------------------
-- DualisableFibredOriented -

-- ff :: Struct Ort x -> Rt x -> Rt (o (o x))
newtype OrtPnt x = OrtPnt (Orientation (Point x))

data ReflectionG r c o d where
  ReflectionG :: ReflexiveG r c o d => ReflectionG r c o d

reflGTo :: ReflectionG r c o d -> Struct r x -> c (d x) (d (o (o x)))
reflGTo r@ReflectionG s = t where Inv2 t _ = reflG' r s

reflGFrom :: ReflectionG r c o d -> Struct r x -> c (d (o (o x))) (d x)
reflGFrom r@ReflectionG s = f where Inv2 _ f = reflG' r s

ff :: ReflectionG r (->) o Pnt -> Struct r x -> OrtPnt x -> OrtPnt (o (o x))
ff r s (OrtPnt (p :> q)) = OrtPnt (t p :> t q) where
  t = fromPntG (reflGTo r s)

ff' :: (Root x ~ Orientation (Point x), Root (o (o x)) ~ Orientation (Point (o (o x))))
  => ReflectionG Ort (->) o Pnt -> Struct Ort x -> Rt x -> Rt (o (o x))
ff' r s (Rt rt) = Rt rt' where
  OrtPnt rt' = ff r s (OrtPnt rt)

gg :: ReflectionG Ort (->) o Pnt -> Struct Ort x -> OrtPnt (o (o x)) -> OrtPnt x
gg r s (OrtPnt (p :> q)) = OrtPnt (f p :> f q) where f = fromPntG (reflGFrom r s)

hh :: ReflexiveG Ort (->) o Pnt => Struct Ort x -> Inv2 (->) (OrtPnt x) (OrtPnt (o (o x)))
hh s = Inv2 (ff r s) (gg r s) where
  r = ReflectionG

instance ReflexiveG Ort (->) o Pnt => ReflexiveG Ort (->) o OrtPnt where
  reflG = hh

{-
ff s@Struct (OrtPnt (p :> q)) = OrtPnt (t p :> t q) where
  Inv2 t f = reflG s
-}

class ( DualisableOriented s o, DualisableG Ort (->) o Rt
      , Transformable s FbrOrt
      ) => DualisableFibredOriented s o

instance (HomFibredOriented h, DualisableFibredOriented s o)
  => ApplicativeG Rt (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h


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
         ) => ApplicativeG Rt (HomDisj s o h) (->) where
  amapG = amapRt . rmapDisjFbrOrt

instance ( HomOriented h, DualisableOriented s o
         , Transformable s Fbr, Transformable s FbrOrt
         ) => HomFibred (HomDisj s o h)

instance ( HomOriented h, DualisableOriented s o
         , Transformable s Fbr, Transformable s FbrOrt
         ) => HomDisjunctiveFibredOriented (HomDisj s o h)
-}

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

