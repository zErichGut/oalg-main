
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
-- Module      : OAlg.Hom.Oriented.Definition
-- Description : definition of homomorphisms between oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of homomorphisms between 'Oriented' structures.
module OAlg.Hom.Oriented.Definition
  (

    -- * Disjunctive
    HomDisjunctiveOriented

    -- * Covariant
  , HomOriented, HomEmpty

    -- * Dualisable
  , HomDualisableOriented(..)
  , SDualisableOriented
  , toDualArw, toDualPnt
  
    -- * Applicative
  , ApplicativePoint, pmap, omap
  , FunctorialPoint

    -- * Instances
    -- ** HomOrt
    
  , HomOrt, homOrt

    -- ** HomOrtEmpty
  , HomOrtEmpty
  , toOpOrt, fromOpOrt

  , module V

  )
  where

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.SDuality

import OAlg.Data.Identity
import OAlg.Data.Variant as V

import OAlg.Structure.Oriented hiding (Path(..))

--------------------------------------------------------------------------------
-- ApplicativePoint -

-- | applications on 'Point's.
type ApplicativePoint h = ApplicativeG Pnt h (->)

--------------------------------------------------------------------------------
-- pmap -

-- | the induced mapping of 'Point's given by 'amapG'. 
pmap :: ApplicativePoint h => h x y -> Point x -> Point y
pmap h = fromPntG (amapG h)

--------------------------------------------------------------------------------
-- omap -

-- | the induced mapping of 'Orientation'.
omap :: ApplicativePoint h => h a b -> Orientation (Point a) -> Orientation (Point b)
omap = amapG . pmap

--------------------------------------------------------------------------------
-- FunctorialPoint -

type FunctorialPoint h = FunctorialG Pnt h (->)

--------------------------------------------------------------------------------
-- HomOriented -

-- | covariant homomorphisms between 'Oriented' structures.
--
-- __Property__ Let @__h__@ be an instance of 'HomOriented', then
-- for all  @__a__@, @__b__@ and @h@ in @__h a b__@ holds:
--
-- (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
-- (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      ) => HomOriented h where

instance HomOriented h => HomOriented (Path h)

--------------------------------------------------------------------------------
-- HomDisjunctiveOriented -

-- | disjunctive homomorphism between 'Oriented' structures.
--
-- __Properties__ Let @'HomDisjunctiveOriented' __h__@, then
-- for all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
--
-- (1) If @'variant2' h '==' 'Covariant'@ then holds:
--
--     (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
--     (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
-- (2) If @'variant2' h '==' 'Contravariant'@ then holds:
--
--     (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
--     (2) @'end' ',' 'amap' h '.=.' 'pmap' h '.' 'start'@.
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      , Disjunctive2 h
      )
  => HomDisjunctiveOriented h where

instance HomDisjunctiveOriented h => HomOriented (SVariant Covariant h)

--------------------------------------------------------------------------------
-- SDualisableOriented -

-- | duality according to @__o__@ on @__s__@-structured 'Oriented' types,
--
-- __Properties__ Let @'SDualisableOriented' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) @'start' '.' 'toDualArw' q '.=.' 'toDualPnt' q '.' 'end'@.
--
-- (2) @'end' '.' 'toDualArw' q '==' 'toDualPnt' q '.' 'start'@.
--
-- where @q@ is any proxy for @__o__@.
class ( DualisableG Ort (->) o Id, DualisableG Ort (->) o Pnt
      , Transformable s Ort, TransformableG o s s
      )
  => SDualisableOriented s o

instance (TransformableOrt s, TransformableOp s) => SDualisableOriented s Op

--------------------------------------------------------------------------------
-- toDualArw -

-- | the dual arrow induced by @'DualisableG __s__ (->) __o__ 'Id'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualArw :: SDualisableOriented s o => q o -> Struct s x -> x -> o x
toDualArw q s = fromIdG (toDualG' (d q s) (tauOrt s)) where
  d :: SDualisableOriented s o => q o -> Struct s x -> SDualityG Ort (->) o Id
  d _ _ = SDualityG

--------------------------------------------------------------------------------
-- toDualPnt -

-- | the dual point induced by @'DualisableG' __s__ (->) __o__ 'Pnt'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualPnt :: SDualisableOriented s o => q o -> Struct s x -> Point x -> Point (o x)
toDualPnt q s = fromPntG (toDualG' (d q s) (tauOrt s)) where
  d :: SDualisableOriented s o => q o -> Struct s x -> SDualityG Ort (->) o Pnt
  d _ _ = SDualityG

--------------------------------------------------------------------------------
-- HomDualisableOrientedDualisable -

-- | dualisable disjunctive homomorphisms between 'Oriented' structures.
--
-- __Property__ Let @'HomDualisableOriented' __o h__@, then for all @__x__@ and @s@ in
-- @'Struct' ('ObjectClass __h__) __x__@holds:
--
-- (1) @f '.' t '.=.' 'cOne' ('domain' t)@.
--
-- (2) @t '.' f '.=.' 'cOne' ('domain' f)@.
--
-- where @'Contravariant2' t = 'homOrtToDual' s@ and @'Contravariant2' f = 'homOrtFromDual' s@.
class ( HomDisjunctiveOriented h
      , CategoryDisjunctive h, Functorial1 h Id, Functorial1 h Pnt
      ) => HomDualisableOriented o h where
  homOrtToDual :: Struct (ObjectClass h) x -> SVariant Contravariant h x (o x)
  homOrtFromDual :: Struct (ObjectClass h) x -> SVariant Contravariant h (o x) x

--------------------------------------------------------------------------------
-- homOrtToDual' -

homOrtToDual' :: HomDualisableOriented o h
  => q o h -> Struct (ObjectClass h) x -> SVariant Contravariant h x (o x)
homOrtToDual' _ = homOrtToDual

--------------------------------------------------------------------------------
-- homOrtFromDual' -

homOrtFromDual' :: HomDualisableOriented o h
  => q o h -> Struct (ObjectClass h) x -> SVariant Contravariant h (o x) x
homOrtFromDual' _ = homOrtFromDual

--------------------------------------------------------------------------------
-- prpHomDualisableOriented o h -

relHomDualisableOriented :: (HomDualisableOriented o h, EqExt h)
  => q o h -> Struct (ObjectClass h) x -> Statement
relHomDualisableOriented q s 
  = And [ Label "1" :<=>: (f . t .=. cOne (domain t))
        , Label "2" :<=>: (t . f .=. cOne (domain f))
        ]
  where Contravariant2 t = homOrtToDual' q s
        Contravariant2 f = homOrtFromDual' q s

prpHomDualisableOriented :: (HomDualisableOriented o h, EqExt h)
  => q o h -> Struct (ObjectClass h) x -> Statement
prpHomDualisableOriented q s = Prp "HomDualisableOriented"
  :<=>: relHomDualisableOriented q s
  
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
  deriving (Show,Validable,Validable2,Disjunctive,Disjunctive2)

deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq2 (HomOrt s o h)
deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq (HomOrt s o h x y)

instance HomOriented h => Morphism (HomOrt s o h) where
  type ObjectClass (HomOrt s o h) = s
  homomorphous (HomOrt h) = homomorphous h

instance HomOriented h => Category (HomOrt s o h) where
  cOne = HomOrt . cOne 
  HomOrt f . HomOrt g = HomOrt (f . g)

instance HomOriented h => CategoryDisjunctive (HomOrt s o h)

instance (HomOriented h, SDualisableOriented s o) => ApplicativeG Id (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, SDualisableOriented s o) => ApplicativeGMorphism Id (HomOrt s o h) (->)
instance (HomOriented h, SDualisableOriented s o) => FunctorialG Id (HomOrt s o h) (->)


instance (HomOriented h, SDualisableOriented s o) => ApplicativeG Pnt (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, SDualisableOriented s o) => ApplicativeGMorphism Pnt (HomOrt s o h) (->)
instance (HomOriented h, SDualisableOriented s o) => FunctorialG Pnt (HomOrt s o h) (->)

instance (HomOriented h, SDualisableOriented s o) => HomDisjunctiveOriented (HomOrt s o h)


instance (HomOriented h, SDualisableOriented s o) => HomDualisableOriented o (HomOrt s o h) where
  homOrtToDual s = Contravariant2 (HomOrt t) where Contravariant2 t = sToDual s
  homOrtFromDual s = Contravariant2 (HomOrt f) where Contravariant2 f = sFromDual s

--------------------------------------------------------------------------------
-- homOrt -

-- | embedding of 'HomOriented' to 'HomOrt'.
homOrt :: (HomOriented h, Transformable (ObjectClass h) s)
  => h x y -> SVariant Covariant (HomOrt s o h) x y
homOrt h = Covariant2 (HomOrt h') where Covariant2 h' = sCov h

--------------------------------------------------------------------------------
-- HomOrtEmpty -

type HomOrtEmpty s o = HomOrt s o (HomEmpty s)

--------------------------------------------------------------------------------
-- toOpOrt -

toOpOrt :: Oriented x => SVariant Contravariant (HomOrtEmpty Ort Op) x (Op x)
toOpOrt = homOrtToDual Struct

--------------------------------------------------------------------------------
-- fromOpOrt -

fromOpOrt :: Oriented x => SVariant Contravariant (HomOrtEmpty Ort Op) (Op x) x
fromOpOrt = homOrtFromDual Struct







{-
--------------------------------------------------------------------------------
-- HomDisjunctiveOriented -

-- | disjunctive homomorphism between 'Oriented' structures.
--
-- __Properties__ Let @'HomDisjunctiveOriented' __h__@, then holds:
--
-- (1) For all @__x__@ and @s@ in @'Struct' ('ObjectClass' __h__) __x__ holds:
-- @'homOrtDual' s@ is 'valid'. 
--
-- (2) For all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
--
--     (1) If @'variant2' h '==' 'Covariant'@ then holds:
--
--         (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
--         (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
--     (2) If @'variant2' h '==' 'Contravariant'@ then holds:
--
--         (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
--         (2) @'end' ',' 'amap' h '.=.' 'pmap' h '.' 'start'@.
class ( CategoryDisjunctive h
      , Functorial h, FunctorialPoint h
      , Transformable (ObjectClass h) Ort
      )
  => HomDisjunctiveOriented h o where
  homOrtToDual :: Struct (ObjectClass h) x -> SVariant Contravariant h x (o x)
  homOrtFromDual :: Struct (ObjectClass h) x -> SVariant Contravariant h (o x) x

--------------------------------------------------------------------------------
-- homOrtDual -

-- | the induced isomorphism.
homOrtDual :: HomDisjunctiveOriented h o => Struct (ObjectClass h) x -> Inv2 h x (o x)
homOrtDual s = Inv2 t f where
  Contravariant2 t = homOrtToDual s
  Contravariant2 f = homOrtFromDual s

-- | the induced isomorphism.
homOrtDual'  :: HomDisjunctiveOriented h o => q h o -> Struct (ObjectClass h) x -> Inv2 h x (o x)
homOrtDual' _ = homOrtDual

--------------------------------------------------------------------------------
-- homOrtToCov -

-- | mapping a 'Contravariant' homomoprphism to its 'Covariant'. 
homOrtToCov :: HomDisjunctiveOriented h o
  => SVariant Contravariant h x y -> SVariant Covariant h x (o y)
homOrtToCov (Contravariant2 h) = Covariant2 (t . h) where
  Contravariant2 t = homOrtToDual (range h)

-- | mapping a 'Contravariant' homomoprphism to its 'Covariant'. 
homOrtToCov' :: HomDisjunctiveOriented h o
  => q o -> SVariant Contravariant h x y -> SVariant Covariant h x (o y)
homOrtToCov' _ = homOrtToCov

--------------------------------------------------------------------------------
-- SDualisableOriented -

-- | duality according to @__o__@ on @__s__@-structured 'Oriented' types,
--
-- __Properties__ Let @'SDualisableOriented' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) @'start' '.' 'toDualArw' q '.=.' 'toDualPnt' q '.' 'end'@.
--
-- (2) @'end' '.' 'toDualArw' q '==' 'toDualPnt' q '.' 'start'@.
--
-- where @q@ is any proxy for @__o__@.
class ( DualisableG Ort (->) o Id, DualisableG Ort (->) o Pnt
      , Transformable s Ort, Transformable1 o s
      )
  => SDualisableOriented s o

instance (TransformableOrt s, TransformableOp s) => SDualisableOriented s Op

--------------------------------------------------------------------------------
-- toDualArw -

-- | the dual arrow induced by @'DualisableG __s__ (->) __o__ 'Id'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualArw :: SDualisableOriented s o => q o -> Struct s x -> x -> o x
toDualArw q s = fromIdG (toDualG' (d q s) (tauOrt s)) where
  d :: SDualisableOriented s o => q o -> Struct s x -> SDualityG Ort (->) o Id
  d _ _ = SDualityG

--------------------------------------------------------------------------------
-- toDualPnt -

-- | the dual point induced by @'DualisableG' __s__ (->) __o__ 'Pnt'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualPnt :: SDualisableOriented s o => q o -> Struct s x -> Point x -> Point (o x)
toDualPnt q s = fromPntG (toDualG' (d q s) (tauOrt s)) where
  d :: SDualisableOriented s o => q o -> Struct s x -> SDualityG Ort (->) o Pnt
  d _ _ = SDualityG

--------------------------------------------------------------------------------
-- HomOrt -

type HomOrt = SHom Ort

instance (HomOriented h, SDualisableOriented s o) => HomDisjunctiveOriented (HomOrt s o h) o where
  homOrtToDual   = sToDual
  homOrtFromDual = sFromDual

--------------------------------------------------------------------------------
-- homOrt -

-- | embedding of 'HomOriented' to 'HomOrt'.
homOrt :: (HomOriented h, Transformable (ObjectClass h) s)
  => h x y -> SVariant Covariant (HomOrt s o h) x y
homOrt = sCov

--------------------------------------------------------------------------------
-- homOrtToDualEmpty -

-- | from 'homOrtToDual' induced.
homOrtToDualEmpty :: (TransformableOrt s, SDualisableOriented s o)
  => Struct s x -> SVariant Contravariant (HomOrtEmpty s o) x (o x)
homOrtToDualEmpty = homOrtToDual 

--------------------------------------------------------------------------------
-- homOrtFromDualEmpty -

-- | from 'homOrtFromDual' induced.
homOrtFromDualEmpty :: (TransformableOrt s, SDualisableOriented s o)
  => Struct s x -> SVariant Contravariant (HomOrtEmpty s o) (o x) x
homOrtFromDualEmpty = homOrtFromDual


--------------------------------------------------------------------------------
-- toOpOrt -

toOpOrt :: Oriented x => SVariant Contravariant (HomOrtEmpty Ort Op) x (Op x)
toOpOrt = homOrtToDualEmpty Struct

--------------------------------------------------------------------------------
-- fromOpOrt -

fromOpOrt :: Oriented x => SVariant Contravariant (HomOrtEmpty Ort Op) (Op x) x
fromOpOrt = homOrtFromDualEmpty Struct
-}
