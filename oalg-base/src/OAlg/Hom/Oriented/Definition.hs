
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
{-
    -- * Homomorphism
    HomOrientedCovariant  -- , omap, IsoOrt, IsoOriented
  , SDualisableOriented
  , HomEmpty(), fromHomEmpty
  , homToDual, homFromDual
    
    -- * Applications
  , ApplicativePoint(..), pmap, omap
  , FunctorialPoint

  , module V
  , module S
  , module D
-}

{-
    -- * Functorial
  , FunctorialHomOriented

    -- * Duality
  , SDualityOriented(..)
  , OpDuality(..)

    -- * IdHom
  , IdHom(..)

    -- * OpHom
  , OpHom(..)

    -- * HomOp
  , HomOp(..)

    -- * IsoOp
  , IsoOp(), PathHomOp -- , opPathOrt
  , isoToOpOp, isoToOpOp', isoFromOpOp, isoFromOpOp'
  , isoToOpOpOrt, isoFromOpOpOrt
  , isoToOpOpStruct, isoFromOpOpStruct

    -- * IsoOpMap
  , IsoOpMap(), PathOpMap
  , OpMap(..)
  , toOp1Struct, fromOp1Struct

    -- ** Path
  , isoCoPath
-}
  )
  where

import Control.Monad
import Control.Applicative ((<|>))

import Data.Kind
import Data.Typeable
import Data.List((++))

import OAlg.Prelude

import OAlg.Category.Path as C
import OAlg.Category.SDual as D
import OAlg.Category.Unify

import OAlg.Data.Proxy
import OAlg.Data.Either
import OAlg.Data.Constructable
import OAlg.Data.Reducible
import OAlg.Data.Identity
import OAlg.Data.Variant as V
import OAlg.Data.SDualisable as S

import OAlg.Structure.Oriented as O
import OAlg.Structure.Multiplicative
-- import OAlg.Structure.Fibred
-- import OAlg.Structure.Additive
-- import OAlg.Structure.Distributive

-- import OAlg.Hom.Definition

--------------------------------------------------------------------------------
-- ApplicativePoint -

-- | applications on 'Point's.
type ApplicativePoint h = ApplicativeG Pnt h (->)

--------------------------------------------------------------------------------
-- pmap -

-- | the induced mapping of 'Point's given by 'amapG'. 
pmap :: ApplicativePoint h => h x y -> Point x -> Point y
pmap h p = q where Pnt q = amapG h (Pnt p)

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
      , Transformable (ObjectClass h) Ort, Transformable (ObjectClass h) Typ
      ) => HomOriented h where

instance HomOriented h => HomOriented (C.Path h)

--------------------------------------------------------------------------------
-- SDualisableOrietend -

-- | contravariant duality of @__s__@-structured types according to @__o__@.
--
-- __Property__ Let @'SDualisableOriented' __s o__@. then for all @__x__@ and
-- @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'start' '.' 'amap' t '.=.' 'pmap' t '.' 'end'@.
--
-- (2) @'end' '.' 'amap' t '.=.' 'pmap' t '.' 'start'@.
--
-- where @q@ is any proxy in @__q o__@ and @'Contravariant' t = 'homToDual' q s@.
class ( SDualisableG (->) s o Id, SDualisableG (->) s o Pnt
      , Transformable s Ort, Transformable1 o Ort
      )
  => SDualisableOriented s o

instance (TransformableOrt s, TransformableOp s) => SDualisableOriented s Op

--------------------------------------------------------------------------------
-- sdlToDualArw -

sdlToDualArw :: SDualisableOriented s o => q o -> Struct s x -> x -> (o x)
sdlToDualArw _ = fromIdG . sdlToDual

--------------------------------------------------------------------------------
-- sdlToDualPnt - 

sdlToDualPnt :: SDualisableOriented s o => q o -> Struct s x -> Point x -> Point (o x)
sdlToDualPnt q s x = x' where
  Pnt x' = toDualPnt q s (Pnt x)
  
  toDualPnt :: SDualisableOriented s o => q o -> Struct s x -> Pnt x -> Pnt (o x)
  toDualPnt _ = sdlToDual

--------------------------------------------------------------------------------
-- prpSDualisableOriented -

-- | validity according to 'SDualisableOriented'.
relSDualisableOriented :: SDualisableOriented s o
  => q o -> Struct s x -> Struct Ort x -> Struct Ort (o x) -> XOrt x -> Statement
relSDualisableOriented q s Struct Struct xx = Forall xx
    (\x -> And [ Label "1" :<=>: ((start $ tArw x) == (tPnt $ end x)) :?> Params ["x":=show x]
               , Label "2" :<=>: ((end $ tArw x) == (tPnt $ start x)) :?> Params ["x":=show x]
               ]
    )
  where
    tArw = sdlToDualArw q s
    tPnt = sdlToDualPnt q s


-- | validity according to 'SDualisableOriented'.
prpSDualisableOriented :: SDualisableOriented s o
  => q o -> Struct s x -> XOrt x -> Statement
prpSDualisableOriented q s xx = Prp "SDualisableOriented" :<=>:
  relSDualisableOriented q s sOrt (tau1 sOrt) xx where sOrt = tauOrt s

--------------------------------------------------------------------------------
-- HomEmpty -

-- | the empty homomorphism.
newtype HomEmpty s x y = HomEmpty (EntEmpty2 x y)
  deriving (Show, Show2,Eq,Eq2,Validable,Validable2,Entity,Entity2)

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

instance (TransformableOrt s, TransformableTyp s)
  => HomOriented (HomEmpty s)

--------------------------------------------------------------------------------
-- HomVariant -

type HomVariant = Variant2

--------------------------------------------------------------------------------
-- HomDisjunctiveOriented -

-- | disjunctive homomorphism between 'Oriented' structures.
class ( CategoryDisjunctive h
      , Functorial h, FunctorialPoint h
      , ObjectClass h ~ s, Transformable s Ort, Transformable1 o s
      )
  => HomDisjunctiveOriented s o h where
  homOrtToDual :: Struct s x -> HomVariant Contravariant h x (o x)
  homOrtFromDual :: Struct s x -> HomVariant Contravariant h (o x) x

--------------------------------------------------------------------------------
-- homOrtToDual' -

homOrtToDual' :: HomDisjunctiveOriented s o h
  => q o h -> Struct s x -> HomVariant Contravariant h x (o x)
homOrtToDual' _ = homOrtToDual

--------------------------------------------------------------------------------
-- homOrtToCovariant -

homOrtToCovariant :: HomDisjunctiveOriented s o h
  => q o h -> Struct s x -> HomVariant Contravariant h x y -> HomVariant Covariant h x (o y)
homOrtToCovariant q _ h = toCov q (range h) h where
  toCov :: HomDisjunctiveOriented s o h
    => q o h -> Struct s y -> HomVariant Contravariant h x y -> HomVariant Covariant h x (o y)
  toCov q s (Contravariant2 h) = Covariant2 (t . h) where
    Contravariant2 t = homOrtToDual' q s

--------------------------------------------------------------------------------
-- homOrtFromDual -

homOrtFromDual' :: HomDisjunctiveOriented s o h
  => q o h -> Struct s x -> HomVariant Contravariant h (o x) x
homOrtFromDual' _ = homOrtFromDual

--------------------------------------------------------------------------------
-- prpHomDisjunctiveOriented -

relHomOrtDVariantOne :: HomDisjunctiveOriented s o h
  => q o h -> Struct s x -> Statement
relHomOrtDVariantOne q s = (variant2 (cOne' (qh q) s) == Covariant) :?> Params []
  where
    qh :: forall q (o :: Type -> Type) (h :: Type -> Type -> Type) . q o h -> Proxy h
    qh _ = Proxy

relHomOrtDVariantMlt :: HomDisjunctiveOriented s o h
  => p o -> Struct s x -> h y z -> h x y -> Statement
relHomOrtDVariantMlt _ _ f g
  = Label "1.2" :<=>: (variant2 (f . g) == variant2 f * variant2 g) :?> Params []

relHomOrtDApplCovariant :: (HomDisjunctiveOriented s o h, Show2 h)
  => q o -> Struct s x -> Homomorphous Ort x y -> HomVariant Covariant h x y  -> x -> Statement
relHomOrtDApplCovariant _ _ (Struct:>:Struct) h  x = Label "Covariant" :<=>:
  And [ (start (amap h x) == pmap h (start x)) :?> Params ["h":= show2 h, "x":=show x]
      , (end (amap h x) == pmap h (end x)) :?> Params ["h":= show2 h, "x":=show x]
      ]

relHomOrtDApplVariant :: (HomDisjunctiveOriented s o h, Show2 h)
  => q o -> Either2 (HomVariant Contravariant h) (HomVariant Covariant h) x y
  -> Struct s x -> x -> Statement
relHomOrtDApplVariant q h s x = case h of
  Right2 hCov -> relHomOrtDApplCovariant q s (tauHom (homomorphous h)) hCov x
  Left2 hCnt  -> relHomOrtDApplVariant q (Right2 (homOrtToCovariant (q' q hCnt) s hCnt)) s x
  where q' :: forall q f (h :: Type -> Type -> Type) (o :: Type -> Type) x y
            . q o -> f h x y -> Proxy2 o h
        q' _ _ = Proxy2

prpHomOrtDApplVariant :: (HomDisjunctiveOriented s o h, Show2 h)
  => q s o -> X (SomeApplication h) -> Statement
prpHomOrtDApplVariant q xsa = Prp "HomOrtDApplVariant" :<=>: Forall xsa
  (\(SomeApplication h x) -> relHomOrtDApplVariant q (toVariant2 h) (domain h) x
  )
  

prpHomDisjunctiveOriented :: (HomDisjunctiveOriented s o h, Show2 h)
  => q s o -> X (SomeApplication h) -> Statement
prpHomDisjunctiveOriented q xsa = Prp "HomDisjunctiveOriented" :<=>:
  And [ prpHomOrtDApplVariant q xsa
      ]

{-
hdoXSomeCmpb2 :: HomDisjunctiveOriented s o h
  => q s o -> X (SomeCmpb2 h) -> X (SomeCmpb2 h)
hdoXSomeCmpb2 q xsc = xscN 10 q xsc where
  xscN :: HomDisjunctiveOriented s o h
    => N -> q s o -> X (SomeCmpb2 h) -> X (SomeCmpb2 h)
  xscN 0 _ xsc = xsc
  xscN n q xsc = xsc <|> xscN (pred n) q (adjDualN n q xsc)

  adjDualN :: HomDisjunctiveOriented s o h
    => N -> q s o -> X (SomeCmpb2 h) -> X (SomeCmpb2 h)
  adjDualN 0 _ xsc = xsc
  adjDualN n q xsc = adjToDualN n q xsc <|> adjFromDualN n q xsc

  adjToDualN :: HomDisjunctiveOriented s o h
    => N -> q s o -> X (SomeCmpb2 h) -> X (SomeCmpb2 h)
  adjToDualN n q xsc = xsc' <|> adjDualN (pred n) q xsc' where
    xsc' = amap1 (adjToDual q) xsc

  adjToDual :: HomDisjunctiveOriented s o h
    => q s o -> SomeCmpb2 h -> SomeCmpb2 h
  adjToDual q sc@(SomeCmpb2 f g) = SomeCmpb2 (d . f) g where
    Contravariant2 d = homOrtToDual' (qoh q sc) (range f)

  adjFromDualN :: HomDisjunctiveOriented s o h
    => N -> q s o -> X (SomeCmpb2 h) -> X (SomeCmpb2 h)
  adjFromDualN n q xsc = xsc' <|> adjDualN (pred n) q xsc' where
    xsc' = amap1 (adjFromDual q) xsc

  adjFromDual :: HomDisjunctiveOriented s o h
    => q s o -> SomeCmpb2 h -> SomeCmpb2 h
  adjFromDual q sc@(SomeCmpb2 f g) = SomeCmpb2 f (g . d) where
    Contravariant2 d = homOrtFromDual' (qoh q sc) (domain g)
  
  qoh :: forall q s (o :: Type -> Type) f (h :: Type -> Type -> Type) . q s o -> f h -> Proxy2 o h
  qoh _ _ = Proxy2

type HomOrtOpEmpty s = HomOrt s Op (HomEmpty s)

ff :: Statement
ff = prpHomDisjunctiveOriented qso xo xfg xsa where

  qoh = Proxy2 :: Proxy2 Op (HomOrtOpEmpty Ort)
  qso = Proxy2 :: Proxy2 Ort Op
  sOS = Struct :: Struct Ort OS
  sN  = Struct :: Struct Ort N

  Contravariant2 fOS = homOrtFromDual' qoh sOS
  Contravariant2 tOS = homOrtToDual' qoh sOS
    
  Contravariant2 fN = homOrtFromDual' qoh sN
  Contravariant2 tN = homOrtToDual' qoh sN

  xo :: X (SomeObjectClass (HomOrtOpEmpty Ort))
  xo  = return (SomeObjectClass (Struct :: Struct Ort OS))
  
  xfg :: X (SomeCmpb2 (HomOrtOpEmpty Ort))
  xfg = hdoXSomeCmpb2 qso xsc where
    xsc =   return (SomeCmpb2 fOS tOS)
        <|> return (SomeCmpb2 fOS (cOne (domain fOS)))
        <|> return (SomeCmpb2 (cOne (range tOS)) tOS)
        <|> return (SomeCmpb2 fN tN)
            

  xsa :: X (SomeApplication (HomOrtOpEmpty Ort))
  xsa = amap1 (\x -> SomeApplication tOS x) xStandard
-}  
--------------------------------------------------------------------------------
-- HomOrt -

newtype HomOrt s o h x y = HomOrt (SDualCat s o h x y)
  deriving (Show,Show2,Disjunctive,Disjunctive2,CategoryDisjunctive)

deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq (HomOrt s o h x y)
deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq2 (HomOrt s o h)

--------------------------------------------------------------------------------
-- homOrtCov -

homOrtCov :: (HomOriented h, Transformable (ObjectClass h) s) => h x y -> HomOrt s o h x y
homOrtCov = HomOrt . sctCov

--------------------------------------------------------------------------------
-- HomOrt - Category -

instance Morphism h => Morphism (HomOrt s o h) where
  type ObjectClass (HomOrt s o h) = s
  homomorphous (HomOrt h) = homomorphous h

instance Morphism h => Category (HomOrt s o h) where
  cOne = HomOrt . cOne
  HomOrt f . HomOrt g = HomOrt (f . g)

--------------------------------------------------------------------------------
-- HomOrt - Functorial -

instance (HomOriented h, SDualisableOriented s o) => ApplicativeG Id (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, SDualisableOriented s o) => ApplicativeGMorphism Id (HomOrt s o h) (->)
instance (HomOriented h, SDualisableOriented s o) => FunctorialG Id (HomOrt s o h) (->)

instance (HomOriented h, SDualisableOriented s o) => ApplicativeG Pnt (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, SDualisableOriented s o) => ApplicativeGMorphism Pnt (HomOrt s o h) (->)
instance (HomOriented h, SDualisableOriented s o) => FunctorialG Pnt (HomOrt s o h) (->)


--------------------------------------------------------------------------------
-- HomOrt - HomDisjunctiveOriented -

instance (HomOriented h, SDualisableOriented s o, Transformable1 o s)
  => HomDisjunctiveOriented s o (HomOrt s o h) where
  homOrtToDual s = Contravariant2 (HomOrt t) where Contravariant2 t = sctToDual s
  homOrtFromDual s = Contravariant2 (HomOrt f) where Contravariant2 f = sctFromDual s


{-
--------------------------------------------------------------------------------
-- SDualCat - HomOriented -

instance (HomOriented h, SDualisableOriented s o, Transformable s Typ)
  => HomOriented (Variant2 Covariant (SDualCat s o h))

--------------------------------------------------------------------------------
-- HomOrt -

-- | category of homomorphisms between oriented structures given by a type family @__h__@ of
-- covariant homomorphisms and a oriented duality @__o__@.
--
-- __Properties__ Let @h@ be in @'HomOriented' __o__ __h__@ with
-- @'HomOriented' __h__@ and @'SDualisableOriented' Ort __o__@, then holds:
--
-- (1) If @'variant' h '==' 'Covariant'@ then holds:
--
--     (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
--     (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
-- (2) If @'variant' h '==' 'Contravariant'@ then holds:
--
--     (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
--     (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
newtype HomOrt o h x y = HomOrt (SDualCat Ort o h x y)
  deriving (Show,Show2,Eq,Eq2)

--------------------------------------------------------------------------------
-- HomOrt - Disjunctive -

instance Disjunctive (HomOrt o h x y) where variant (HomOrt h) = variant h
instance Disjunctive2 (HomOrt o h)

--------------------------------------------------------------------------------
-- HomOrt - Category -
instance HomOriented h => Morphism (HomOrt o h) where
  type ObjectClass (HomOrt o h) = Ort
  homomorphous (HomOrt h) = homomorphous h

instance HomOriented h => Category (HomOrt o h) where
  cOne = HomOrt . cOne
  HomOrt f . HomOrt g = HomOrt (f . g)

--------------------------------------------------------------------------------
-- HomOrt - Applicative -

instance (HomOriented h, SDualisableOriented Ort o)
  => ApplicativeG Id (HomOrt o h) (->) where
  amapG (HomOrt f) = amapG f

instance (HomOriented h, SDualisableOriented Ort o)
  => ApplicativeG Pnt (HomOrt o h) (->) where
  amapG (HomOrt f) = amapG f

instance (HomOriented h, SDualisableOriented Ort o)
  => HomOriented (Variant2 Covariant (HomOrt o h))

--------------------------------------------------------------------------------
-- homOrt -

homOrt :: HomOriented h => h x y -> HomOrt o h x y
homOrt h = HomOrt $ make (SDualMap h :. IdPath (tauOrt $ domain h))

--------------------------------------------------------------------------------
-- homOrtForget -

homOrtForget :: (HomOriented h, Transformable s Ort) => SDualCat s o h x y -> HomOrt o h x y
homOrtForget = HomOrt . sctForget

--------------------------------------------------------------------------------
-- homOrtToDual -

homOrtToDual :: Transformable1 o Ort
  => q o h -> Struct Ort x -> Variant2 Contravariant (HomOrt o h) x (o x)
homOrtToDual q s = Contravariant2 (HomOrt t) where Contravariant2 t = sctToDual' q s

--------------------------------------------------------------------------------
-- homOrtToDualEmpty -

homOrtToDualEmpty :: Transformable1 o Ort
  => q o -> Struct Ort x -> Variant2 Contravariant (HomOrt o (HomEmpty Ort)) x (o x)
homOrtToDualEmpty q = homOrtToDual (q' q)
  where q' :: forall q (o :: Type -> Type) . q o -> Proxy2 o (HomEmpty Ort)
        q' _ = Proxy2
        
--------------------------------------------------------------------------------
-- homOrtFromDual -

homOrtFromDual :: Transformable1 o Ort
  => q o h -> Struct Ort x -> Variant2 Contravariant (HomOrt o h) (o x) x
homOrtFromDual q s = Contravariant2 (HomOrt t) where Contravariant2 t = sctFromDual' q s

--------------------------------------------------------------------------------
-- homOrtToCovariant -

homOrtToCovariant :: (HomOriented h, Transformable1 o Ort)
  => Variant2 Contravariant (HomOrt o h) x y -> Variant2 Covariant (HomOrt o h) x (o y)
homOrtToCovariant (Contravariant2 h) = Covariant2 (t . h) where
  Contravariant2 t = homOrtToDual (q h) (range h)
  q :: HomOrt o h x y -> Proxy2 o h
  q _ = Proxy2
  
--------------------------------------------------------------------------------
-- prpHomOriented -

-- | validity of homomorphisms between 'Oriented' for a given value in the domain.
relHomOriented :: (HomOriented h, Show2 h)
  => Homomorphous Ort x y -> h x y -> x -> Statement
relHomOriented (Struct:>:Struct) h x
  = And [ Label "1" :<=>: (start (amap h x) == pmap h (start x)) :?> Params ["h":=show2 h,"x":=show x]
        , Label "2" :<=>: (end (amap h x) == pmap h (end x)) :?> Params ["h":=show2 h,"x":=show x]
        ]

--------------------------------------------------------------------------------
-- prpHomOrt -

prpHomOrt :: (HomOriented h, SDualisableOriented Ort o, Show2 h)
  => HomOrt o h x y -> XOrt x -> Statement
prpHomOrt h xx = Prp "HomOriented" :<=>: case toVariant2 h of
  Right2 hCov -> Forall xx (relHomOriented (tauHom (homomorphous h)) hCov)
  Left2  hCnt -> prpHomOrt hCnt' xx where Covariant2 hCnt' = homOrtToCovariant hCnt

--------------------------------------------------------------------------------
-- HomOrt - Entity -

instance (HomOriented h, SDualisableOriented Ort o, Show2 h, XStandard x)
  => Validable (HomOrt o h x y) where
  valid h = prpHomOrt h xStandard

instance ( HomOriented h, SDualisableOriented Ort o, Entity2 h, XStandard x
         , Typeable o, Typeable x, Typeable y
         )
  => Entity (HomOrt o h x y)
-}




{-
--------------------------------------------------------------------------------
-- prpSDualisableOriented -

prpSDualisableOrientedOp :: Statement
prpSDualisableOrientedOp = Prp "SDualisableOrientedOp"
  :<=>: prpSDualisableOriented (Proxy :: Proxy Op) (Struct :: Struct Ort OS) xStanard
-}




{-
--------------------------------------------------------------------------------
-- HomOrientedV -

type HomOrientedV v s o h = Variant2 v (SDualCat s o h)
-}

{-
--------------------------------------------------------------------------------
-- homToDual -

-- | 'ToDual' as a 'Contravaraint' morphism.
homToDual :: Transformable1 o Ort
  -- => q o -> Struct s x -> HomOrientedV Contravariant s o (HomEmpty s) x (o x)
  => q o -> Struct Ort x -> Variant2 Contravariant (HomOriented o (HomEmpty Ort)) x (o x) 
homToDual _ = sctToDual

--------------------------------------------------------------------------------
-- homFromDual -

-- | 'FromDual' as a 'Contravaraint' morphism.
homFromDual :: Transformable1 o Ort
  => q o -> Struct Ort x -> Variant2 Contravariant (HomOriented o (HomEmpty Ort)) (o x) x
homFromDual _ = sctFromDual
-}


{-

instance (HomOriented h, Transformable t Ort, Transformable t Typ)
  => HomOriented (Forget t h)


--------------------------------------------------------------------------------
-- FunctorialHomOriented -

-- | functorial application on 'Oriented' structures.
type FunctorialHomOriented h = (HomOriented h, Functorial h, FunctorialPoint h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom Ort h = HomOriented h

--------------------------------------------------------------------------------
-- IsoOrt -

-- | @s@-isomoprhisms.
type IsoOrt s h = (FunctorialHomOriented h, Cayleyan2 h, Hom s h)

--------------------------------------------------------------------------------
-- IsoOriented -

-- | isomorphisms between 'Oriented' structures.
type IsoOriented h = (FunctorialHomOriented h, Cayleyan2 h)


--------------------------------------------------------------------------------
-- IdHom -

-- | identity morphism.
data IdHom s a b where
  IdHom :: Structure s a => IdHom s a a

instance TransformableTyp s => TransformableObjectClassTyp (IdHom s)

--------------------------------------------------------------------------------
-- IdHom - Morphism -

instance Morphism (IdHom s) where
  type ObjectClass (IdHom s) = s
  homomorphous IdHom = Struct :>: Struct

--------------------------------------------------------------------------------
-- IdHom - Entity -

deriving instance Show (IdHom s a b)
instance Show2 (IdHom s)

deriving instance Eq (IdHom s a b)
instance Eq2 (IdHom s)

instance Validable (IdHom s a b) where
  valid IdHom = SValid
instance Validable2 (IdHom s)

instance (Typeable s, Typeable a, Typeable b) => Entity (IdHom s a b)
instance Typeable s => Entity2 (IdHom s)

--------------------------------------------------------------------------------
-- IdHom - Category -

instance Category (IdHom s) where
  cOne Struct = IdHom
  IdHom . IdHom = IdHom

instance Cayleyan2 (IdHom s) where
  invert2 IdHom = IdHom

--------------------------------------------------------------------------------
-- IdHom - HomOriented -

instance Applicative (IdHom s) where
  amap IdHom = id

instance ApplicativePoint (IdHom s) where
  pmap IdHom = id

instance Functorial (IdHom s)
instance FunctorialPoint (IdHom s)

instance ( TransformableOp s, TransformableOrt s, TransformableTyp s)
  => HomOriented (IdHom s)


--------------------------------------------------------------------------------
-- HomOp -

-- | the @a -> 'Op' ('Op' a))@ isomorphism between @__s__@-structures with its 'invert2'.
data HomOp s a b where  
  FromOpOp  :: ( Structure s (Op (Op a))
               , Structure s a
               ) => HomOp s (Op (Op a)) a
  ToOpOp :: ( Structure s (Op (Op a))
            , Structure s a
            ) => HomOp s a (Op (Op a))
{-            
  OpPath    :: ( Structure s a
               , Structure s (Op (O.Path a))
               , Structure s (O.Path (Op a))
               ) => HomOp s (Op (O.Path a)) (O.Path (Op a))
  OpPathInv :: ( Structure s a
               , Structure s (Op (O.Path a))
               , Structure s (O.Path (Op a))
               ) => HomOp s (O.Path (Op a)) (Op (O.Path a)) 
  Opposite    :: ( Structure s (Op (Orientation p))
               , Structure s (Orientation p)
               ) => HomOp s (Op (Orientation p)) (Orientation p)
  OppositeInv :: ( Structure s (Op (Orientation p))
               , Structure s (Orientation p)
               ) => HomOp s (Orientation p) (Op (Orientation p))
-}

--------------------------------------------------------------------------------
-- invHomOp -

-- | the inverse morphism.
invHomOp :: HomOp s a b -> HomOp s b a
invHomOp h = case h of
  FromOpOp    -> ToOpOp
  ToOpOp      -> FromOpOp
{-
  OpPath      -> OpPathInv
  OpPathInv   -> OpPath

  Opposite    -> OppositeInv
  OppositeInv -> Opposite
-}

--------------------------------------------------------------------------------
-- HomOp - Morphism -

instance Morphism (HomOp s) where
  type ObjectClass (HomOp s) = s

  homomorphous FromOpOp = Struct :>: Struct
  homomorphous ToOpOp   = Struct :>: Struct
{-
  homomorphous OpPath    = Struct :>: Struct
  homomorphous OpPathInv = Struct :>: Struct
  
  homomorphous Opposite    = Struct :>: Struct
  homomorphous OppositeInv = Struct :>: Struct
-}

instance TransformableTyp s => TransformableObjectClassTyp (HomOp s)

--------------------------------------------------------------------------------
-- HomOp - Entity -

deriving instance Show (HomOp s a b)
instance Show2 (HomOp s)

deriving instance Eq (HomOp s a b)
instance Eq2 (HomOp s)

instance Validable (HomOp s a b) where
  valid FromOpOp  = SValid
  valid _         = SValid
instance Validable2 (HomOp s)

instance (Typeable s, Typeable a, Typeable b) => Entity (HomOp s a b)
instance Typeable s => Entity2 (HomOp s)

--------------------------------------------------------------------------------
-- HomOp - Hom -

instance Applicative (HomOp s) where
  amap FromOpOp (Op (Op x)) = x
  amap ToOpOp x             = Op (Op x)
{-
  amap h@OpPath (Op pth) = toDualOrt (tau (aStruct h)) h pth where
    aStruct :: HomOp s (Op (O.Path a)) (O.Path (Op a)) -> Struct s a
    aStruct OpPath = Struct
    
    toDualOrt :: Struct Ort a
      -> h (Op (O.Path a)) b -> O.Path a -> O.Path (Op a)
    toDualOrt Struct _ = toDual

  amap h@OpPathInv pth' = fromDualOrt (tau (aStruct h)) h pth' where
    aStruct :: HomOp s (O.Path (Op a)) (Op (O.Path a)) -> Struct s a
    aStruct OpPathInv = Struct

    fromDualOrt :: Struct Ort a
      -> h (O.Path (Op a)) b -> O.Path (Op a) -> Op (O.Path a)
    fromDualOrt Struct _ = Op . fromDual

  amap Opposite (Op o) = opposite o
  amap OppositeInv o = Op (opposite o)
-}

instance ApplicativePoint (HomOp s) where
  pmap FromOpOp = id
  pmap ToOpOp   = id
{-
  pmap OpPath    = id
  pmap OpPathInv = id

  pmap Opposite    = id
  pmap OppositeInv = id
-}

instance (TransformableOrt s, TransformableTyp s, TransformableOp s) => HomOriented (HomOp s)

--------------------------------------------------------------------------------
-- PathHomOp -

-- | paths of 'HomOp'.
type PathHomOp s a b = C.Path (HomOp s) a b

--------------------------------------------------------------------------------
-- IsoOp -

-- | isomorphisms induced by paths of 'HomOp'.
newtype IsoOp s a b = IsoOp (PathHomOp s a b)
  deriving (Show,Show2,Validable,Validable2,Eq,Eq2,Entity,Entity2)

--------------------------------------------------------------------------------
-- IsoOp - Constructable -

-- | reducing paths of 'HomOp'.
rdcPathHomOp :: PathHomOp s a b -> Rdc (PathHomOp s a b)
rdcPathHomOp pth = case pth of
  FromOpOp :. ToOpOp :. p -> reducesTo p >>= rdcPathHomOp
  ToOpOp :. FromOpOp :. p -> reducesTo p >>= rdcPathHomOp
{-
  OpPath :. OpPathInv :. p -> reducesTo p >>= rdcPathHomOp
  OpPathInv :. OpPath :. p -> reducesTo p >>= rdcPathHomOp
  
  Opposite :. OppositeInv :. p -> reducesTo p >>= rdcPathHomOp
  OppositeInv :. Opposite :. p -> reducesTo p >>= rdcPathHomOp
-}  
  h :. p              -> rdcPathHomOp p >>= (return . (h:.))
  p                   -> return p


instance Reducible (PathHomOp s a b) where
  reduce = reduceWith rdcPathHomOp

instance Exposable (IsoOp s a b) where
  type Form (IsoOp s a b) = PathHomOp s a b
  form (IsoOp p) = p
  
instance Constructable (IsoOp s a b) where
  make p = IsoOp (reduce p)

--------------------------------------------------------------------------------
-- IsoOp - Cayleyan2 -

instance Morphism (IsoOp s) where
  type ObjectClass (IsoOp s) = s
  homomorphous = restrict homomorphous

instance TransformableTyp s => TransformableObjectClassTyp (IsoOp s)

instance Category (IsoOp s) where
  cOne o  = IsoOp (IdPath o)
  IsoOp f . IsoOp g = make (f . g)

instance TransformableTyp s => Cayleyan2 (IsoOp s) where
  invert2 (IsoOp p) = IsoOp (reverse id invHomOp p)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

-- instance TransformableOrt s => Applicative (IsoOp s) where
instance Applicative (IsoOp s) where
  amap = restrict amap

instance Functorial (IsoOp s)

instance ApplicativePoint (IsoOp s) where
  pmap = restrict pmap

instance FunctorialPoint (IsoOp s)

instance (TransformableOp s, TransformableOrt s, TransformableTyp s) => HomOriented (IsoOp s)

{-
--------------------------------------------------------------------------------
-- opPathOrt -

-- | the induced isomorphism given by 'OpPath'.
opPathOrt :: Oriented a => IsoOp Ort (Op (O.Path a)) (O.Path (Op a)) 
opPathOrt = make (OpPath :. IdPath Struct) 
-}


--------------------------------------------------------------------------------
-- isoToOpOp -

-- | the isomorphism given by 'ToOpOp'.
isoToOpOp :: (Structure s a, Structure s (Op (Op a))) => IsoOp s a (Op (Op a))
isoToOpOp = make (ToOpOp :. IdPath Struct)

isoToOpOp' :: ( Transformable t s, TransformableTyp t
              , Structure t a, Structure t (Op (Op a))
              , Structure s a
              )
  => Forget' s (IsoOp t) a (Op (Op a))
isoToOpOp' = forget' Proxy isoToOpOp

--------------------------------------------------------------------------------
-- isoToOpOpStruct -

-- | the induced 'IsoOp'.
isoToOpOpStruct :: Transformable1 Op s => Struct s a -> IsoOp s a (Op (Op a))
isoToOpOpStruct s = iso s (tauOp (tauOp s)) where
  iso :: Struct s a -> Struct s (Op (Op a)) -> IsoOp s a (Op (Op a))
  iso Struct Struct = isoToOpOp
  
--------------------------------------------------------------------------------
-- isoToOpOpOrt -

-- | the induced isomorphism of 'Oriented' structures given by 'ToOpOp'.
isoToOpOpOrt :: Oriented a => IsoOp Ort a (Op (Op a))
isoToOpOpOrt = isoToOpOp

--------------------------------------------------------------------------------
-- isoFromOpOp -

-- | the isomorphism given by 'FromOpOp'.
isoFromOpOp :: (Structure s a, Structure s (Op (Op a))) => IsoOp s (Op (Op a)) a
isoFromOpOp = make (FromOpOp :. IdPath Struct)

isoFromOpOp' :: ( Transformable t s, TransformableTyp t
                , Structure t a, Structure t (Op (Op a))
                , Structure s (Op (Op a))
                )
 => Forget' s (IsoOp t) (Op (Op a)) a
isoFromOpOp' = forget' Proxy isoFromOpOp

--------------------------------------------------------------------------------
-- isoFromOpOpStruct -

-- | the induced 'IsoOp'.
isoFromOpOpStruct :: Transformable1 Op s => Struct s a -> IsoOp s (Op (Op a)) a
isoFromOpOpStruct s = iso s (tauOp (tauOp s)) where
  iso :: Struct s a -> Struct s (Op (Op a)) -> IsoOp s (Op (Op a)) a
  iso Struct Struct = isoFromOpOp
  
--------------------------------------------------------------------------------
-- isoFromOpOpOrt -

-- | the induced isomorphism of 'Oriented' structures given by 'FromOpOp'.
--
-- __Examples__
--
-- @
-- let tOS = invert2 (isoFromOpOpOrt :: IsoOp Ort (Op (Op OS)) OS)
-- let f = isoFromOpOpOrt :: Oriented a =>IsoOp Ort (Op (Op a)) a
-- let t = invert2 f
-- @
--
-- >>> tOS
-- IsoOp Path[ToOpOp]
--
-- >>> t . t . tOS
-- IsoOp Path[ToOpOp,ToOpOp,ToOpOp]
--
-- >>> f . f . t . f . t . tOS
-- IsoOp Path[]
--
-- >>> f . f . t . f . t . tOS == cOne Struct
-- True
isoFromOpOpOrt :: Oriented a => IsoOp Ort (Op (Op a)) a
isoFromOpOpOrt = isoFromOpOp

--------------------------------------------------------------------------------
-- IsoOp - SReflexive -

instance (TransformableTyp s, Transformable1 Op s) => SReflexive s (IsoOp s) Op where
  sdlRefl _ s = Inv2 (isoToOpOpStruct s) (isoFromOpOpStruct s)
  
--------------------------------------------------------------------------------
-- OpMap -

-- | contravariant @__s__@-isomorphisms between @__f__ __x__@ and @__f__ ('Op' __x__)@.
data OpMap f s a b where
  
  -- | contravariant @__s__@-isomorphism from __@f x@__ to @__f__ ('Op' __x__)@.
  ToOp1 :: (Structure s (Op (f x)), Structure s (f (Op x)), Structure s x)
    => OpMap f s (Op (f x)) (f (Op x))
    
  -- | the inverse of 'ToOp1'.
  FromOp1 :: (Structure s (Op (f x)), Structure s (f (Op x)), Structure s x)
    => OpMap f s (f (Op x)) (Op (f x))

--------------------------------------------------------------------------------
-- toOp1Struct -

-- | structural attest for 'ToOp1'.
toOp1Struct :: OpMap f s (Op (f x)) (f (Op x)) -> Struct s x
toOp1Struct ToOp1 = Struct
toOp1Struct f     = throw $ InvalidData $ show f

--------------------------------------------------------------------------------
-- fromOp1Struct -

-- | structural attest for 'FromOp1'.
fromOp1Struct :: OpMap f s (f (Op x)) (Op (f x)) -> Struct s x
fromOp1Struct FromOp1 = Struct
fromOp1Struct f       = throw $ InvalidData $ show f

--------------------------------------------------------------------------------
-- invOpMap -

-- | the inverse morphism.
invOpMap :: OpMap f s a b -> OpMap f s b a
invOpMap h = case h of
  ToOp1   -> FromOp1
  FromOp1 -> ToOp1

--------------------------------------------------------------------------------
-- OpMap - Morphism -

instance Morphism (OpMap f s) where
  type ObjectClass (OpMap f s) = s
  homomorphous ToOp1   = Struct :>: Struct
  homomorphous FromOp1 = Struct :>: Struct

instance TransformableTyp s => TransformableObjectClassTyp (OpMap f s)

--------------------------------------------------------------------------------
-- OpMap - Entity -

deriving instance Show (OpMap f s a b)
instance Show2 (OpMap f s)

deriving instance Eq (OpMap f s a b)
instance Eq2 (OpMap f s)

instance Validable (OpMap f s a b) where
  valid ToOp1 = SValid
  valid _     = SValid
instance Validable2 (OpMap f s)

instance (Typeable f, Typeable s, Typeable a, Typeable b) => Entity (OpMap f s a b)
instance (Typeable f, Typeable s) => Entity2 (OpMap f s)

--------------------------------------------------------------------------------
-- PathOpMap -

-- | paths of 'OpMap'.
type PathOpMap f s = C.Path (OpMap f s)

-- | isomorphisms induced by paths of 'OpMap'.
newtype IsoOpMap f s a b = IsoOpMap (PathOpMap f s a b)
  deriving (Show,Show2,Validable,Validable2,Eq,Eq2,Entity,Entity2)

--------------------------------------------------------------------------------
-- IsoOpMap - Constructable -

rdcPathOpMap :: PathOpMap f s a b -> Rdc (PathOpMap f s a b)
rdcPathOpMap pth = case pth of
  ToOp1 :. FromOp1 :. p -> reducesTo p >>= rdcPathOpMap
  FromOp1 :. ToOp1 :. p -> reducesTo p >>= rdcPathOpMap
  h :. p                -> rdcPathOpMap p >>= (return . (h:.))
  p                     -> return p

instance Reducible (PathOpMap f s a b) where
  reduce = reduceWith rdcPathOpMap

instance Exposable (IsoOpMap f s a b) where
  type Form (IsoOpMap f s a b) = PathOpMap f s a b
  form (IsoOpMap p) = p

instance Constructable (IsoOpMap f s a b) where
  make p = IsoOpMap (reduce p)

--------------------------------------------------------------------------------
-- IsoOpMap - Cayleyan2 -

instance Morphism (IsoOpMap f s) where
  type ObjectClass (IsoOpMap f s) = s
  homomorphous = restrict homomorphous

instance TransformableTyp s => TransformableObjectClassTyp (IsoOpMap f s)

instance Category (IsoOpMap f s) where
  cOne o = IsoOpMap (IdPath o)
  IsoOpMap f . IsoOpMap g = make (f . g)

instance TransformableTyp s => Cayleyan2 (IsoOpMap f s) where
  invert2 (IsoOpMap p) = IsoOpMap (reverse id invOpMap p)

--------------------------------------------------------------------------------
-- OpMap Path s - Hom -

instance TransformableOrt s => Applicative (OpMap O.Path s) where
  amap h@ToOp1 = coPath (tau (toOp1Struct h)) where
    coPath :: Struct Ort x -> Op (O.Path x) -> O.Path (Op x)
    coPath Struct = toDual . fromOp

  amap h@FromOp1 = coPathInv (tau (fromOp1Struct h)) where
    coPathInv :: Struct Ort x -> O.Path (Op x) -> Op (O.Path x)
    coPathInv Struct = Op . fromDual

instance ApplicativePoint (OpMap O.Path s) where
  pmap ToOp1 = id
  pmap FromOp1 = id
  
instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => HomOriented (OpMap O.Path s)

--------------------------------------------------------------------------------
-- IsoOpMap Path s - Hom -

instance TransformableOrt s => Applicative (IsoOpMap O.Path s) where
  amap = restrict amap

instance ApplicativePoint (IsoOpMap O.Path s) where
  pmap = restrict pmap
  
instance (TransformableOp s, TransformableOrt s, TransformableTyp s)
  => HomOriented (IsoOpMap O.Path s) 

--------------------------------------------------------------------------------
-- IsoOpMap Path s - Functorial -

instance TransformableOrt s => Functorial (IsoOpMap O.Path s)
instance FunctorialPoint (IsoOpMap O.Path s)

--------------------------------------------------------------------------------
-- isoCoPath -

-- | contravariant isomorphism from @'O.Path' __x__@ to @'O.Path' ('Op'__x__)@ .
isoCoPath :: Oriented x => IsoOpMap O.Path Ort (Op (O.Path x)) (O.Path (Op x))
isoCoPath = make (ToOp1 :. IdPath Struct)

--------------------------------------------------------------------------------
-- OpHom -

-- | induced homomorphism on 'Op'.
data OpHom h x y where
  OpHom :: Transformable1 Op (ObjectClass h) => h x y -> OpHom h (Op x) (Op y)

instance TransformableObjectClassTyp h => TransformableObjectClassTyp (OpHom h)

instance Show2 h => Show2 (OpHom h) where
  show2 (OpHom h) = "OpHom[" ++ show2 h ++ "]"

instance Eq2 h => Eq2 (OpHom h) where
  eq2 (OpHom f) (OpHom g) = eq2 f g

instance Validable2 h => Validable2 (OpHom h) where
  valid2 (OpHom h) = valid2 h

instance Entity2 h => Entity2 (OpHom h)

--------------------------------------------------------------------------------
-- OpHom - Hom -

instance Morphism h => Morphism (OpHom h) where
  type ObjectClass (OpHom h) = ObjectClass h
  homomorphous (OpHom h) = tau1Hom (homomorphous h)
  
instance Applicative h => Applicative (OpHom h) where
  amap (OpHom h) (Op x) = Op (amap h x)

instance ApplicativePoint h => ApplicativePoint (OpHom h) where
  pmap (OpHom h) = pmap h
  

instance HomOriented h => HomOriented (OpHom h)
  
--------------------------------------------------------------------------------
-- Forget' - HomOriented -

instance ApplicativePoint h => ApplicativePoint (Forget' t h) where
  pmap h = pmap (form h)

instance (FunctorialPoint h, Eq2 h, TransformableObjectClassTyp h) => FunctorialPoint (Forget' t h)

instance ( HomOriented h
         , Transformable t Ort, Transformable t Typ
         , Transformable1 Op t
         ) => HomOriented (Forget' t h)

--------------------------------------------------------------------------------
-- Variance -

-- | the variance of a homomorphism on 'Oriented' structures.
data Variance = Covariant | Contravariant deriving (Read,Show,Eq,Enum,Bounded)
-}


{-
--------------------------------------------------------------------------------
-- OpDuality -

-- | 'Op' duality according to 'IsoOp'.
data OpDuality i o where
  OpDuality    :: OpDuality (IsoOp s) Op

--------------------------------------------------------------------------------
-- OpDuality - SDuality -

instance (TransformableTyp s, Transformable1 Op s)
  => SDuality OpDuality s (IsoOp s) Op where
  sdlToDual _ _   = Op
  sdlFromDual _ _ = fromOp

--------------------------------------------------------------------------------
-- SDualityOriented -

-- | structural duality of a @__i__@-'FunctorialHomOriented' according to a @__o__@-duality.
--
-- __Property__  For all @d@ in @__d__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'SDuality' __d__ __s__ __i__ __o__@ holds:
--
-- (1) @'sdlFromDualPnt' d s '.' 'sdlToDualPnt' d s '.=.' 'id'@
--
-- (2) @'sdlToDualPnt' d ('sdlTau' d s) '.' 'sdlToDualPnt' d s '.=.' 'pmap' r@
-- where @'Inv2' r _ = 'sdlRefl' d s@.
--
-- (3) @'sdlToDualPnt' d s'' '.' 'pmap' r = pmap r'' '.' 'sdlToDualPnt' d s@, where
-- @s' = 'sdlTau' d s@, @s'' = 'sdlTau' d s'@, @'Inv2' r _ '.=.' 'sdlRefl' d s@ and
-- @'Inv2' r'' _ = 'sdlRefl' d s'@.
--
-- (4) @'sdlFromDualPnt' d s '.' 'sdlFromDualPnt' d ('sdlTau' d s) '.=.' 'pmap' r'@
-- where @'Inv2' _ r' = 'sdlRefl' d s@.
--
-- (5) @'start' '.' 'sdlToDual' d s '.=.' 'sdlToDualPnt' d s '.' 'end'@
-- and @'end' '.' 'sdlToDual' d s '.=.' 'sdlToDualPnt' '.' 'start'@.
--
-- (6) @'start' '.' 'sdlFromDual' d s '.=.' 'sdlFromDualPnt' '.' 'end'@
-- and @'end' '.' 'sdlFromDual' d s '.=.' 'sdlFromDualPnt' '.' 'start'@.
--
-- __Note__
--
-- (1) @'sdlToDual' d s@ together with @'sdlToDualPnt' d s@ and
-- @'sdlFromDual' d s@ together with @'sdlFromDualPnt' d s@ constitute a __contravariant__
-- homomorphisms between 'Oriented' structures.
--
-- (2) The relation @'SDualityOriented' __d__ __s__ __i__ __o__@ is not necessarily
-- /symmetric/, i.e. @'sdlToDual' d s' '.' 'sdlFromDual' d s' '.=.' 'id'@ may not hold in general!
--
-- (3) A sufficient condition for the property 1 and 4 above is: The properties 2 and 3 hold an
-- @'sdlFromDualPnt' d s '.=.' 'pmap' r' '.' 'sdlToDualPnt' d ('sdlTau' d s)@ where
-- @'Inv2' _ r' = sdlRefl1 d s@. Hence it is sufficient to implement 'sdlToDualPnt' 
-- such that the properties 2 and 3 hold and leaving the implementation of 'sdlFromDualPnt' 
-- as provided. 
class (SDuality d s i o, FunctorialHomOriented i, Transformable s Ort)
  => SDualityOriented d s i o where
  {-# MINIMAL (sdlToDualPnt | sdlFromDualPnt) #-}

  -- | to @'Point' __x__@-dual.
  sdlToDualPnt :: d i o -> Struct s x -> Point x -> Point (o x)
  sdlToDualPnt d s = sdlFromDualPnt d (sdlTau d s) . pmap r where Inv2 r _ = sdlRefl d s

  -- | from @'Pioint' __x__@-dual.
  sdlFromDualPnt :: d i o -> Struct s x -> Point (o x) -> Point x
  sdlFromDualPnt d s = pmap r' . sdlToDualPnt d (sdlTau d s) where Inv2 _ r' = sdlRefl d s 

--------------------------------------------------------------------------------
-- OpDuality - SDualityOriented -

instance (TransformableTyp s, Transformable1 Op s, TransformableOp s, TransformableOrt s)
  => SDualityOriented OpDuality s (IsoOp s) Op where
  sdlToDualPnt _ _   = id
  sdlFromDualPnt _ _ = id
-}

