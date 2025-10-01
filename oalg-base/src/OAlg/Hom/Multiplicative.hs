

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
-- Module      : OAlg.Hom.Multiplicative
-- Description : definition of homomorphisms between multiplicative structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of homomorphisms between 'Multiplicative' structures.
module OAlg.Hom.Multiplicative
  (
    -- * Disjunctive
    HomMultiplicativeDisjunctive
  , toDualOpMlt, homDisjOpMlt

    -- * Covariant
  , HomMultiplicative

    -- * Dualisable
  , DualisableMultiplicative

    -- * X
  , XHomMlt, xMltHomMlt
  , xosHomMlt
  
    -- * Proposition
  , prpHomMultiplicativeDisjunctive
  , prpHomMultiplicative
  , prpHomDisjMultiplicative, prpHomDisjOpMlt
  , prpDualisableMultiplicativeOne
  , prpDualisableMultiplicativeMlt
  , relMapMltOne, relMapMltCov, relMapMltCnt
  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify
import OAlg.Category.Path

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Oriented

--------------------------------------------------------------------------------
-- HomMultiplicative -

-- | covariant family of homomorphisms between 'Multiplicative' structures.
--
-- __Propoerty__ Let @'HomMultiplicative' __h__@, then
-- for all __@a@__, __@b@__ and @h@ in __@h@__ __@a@__ __@b@__ holds:
--
-- (1) For all @p@ in @'Point' __a__@ holds:
--     @'amap' h ('one' p) '==' 'one' ('pmap' h p)@.
--
-- (2) For all @x@, @y@ in __@a@__ with @'start' x '==' 'end' y@ holds:
--     @'amap'h (x '*' y) '==' 'amap' h x '*' 'amap' h y@.
class (HomOriented h, Transformable (ObjectClass h) Mlt) => HomMultiplicative h

instance HomMultiplicative h => HomMultiplicative (Path h)

instance TransformableMlt s => HomMultiplicative (HomEmpty s)

type instance Hom Mlt h = HomMultiplicative h

instance HomMultiplicative h => HomMultiplicative (Inv2 h)

--------------------------------------------------------------------------------
-- HomMultiplicativeDisjunctive -

-- | disjunctive family of homomorphisms between 'Multiplicative' structures.
--
-- __Propoerty__ Let @'HomMultiplicativeDisjunctive' __h__@, then
-- for all __@a@__, __@b@__ and @h@ in __@h@__ __@a@__ __@b@__ holds:
--
-- (1) If @'variant2' h '==' 'Covariant'@ then holds:
--
--     (1) For all @p@ in @'Point' __a__@ holds:
--     @'amap' h ('one' p) '==' 'one' ('pmap' h p)@.
--
--     (2) For all @x@, @y@ in __@a@__ with @'start' x '==' 'end' y@ holds:
--     @'amap' h (x '*' y) '==' 'amap' h x '*' 'amap' h y@.
--
-- (2) If @'variant2' h '==' 'Contravariant'@ then holds:
--
--     (1) For all @p@ in @'Point' __a__@ holds:
--     @'amap' h ('one' p) '==' 'one' ('pmap' h p)@.
--
--     (2) For all @x@, @y@ in __@a@__ with @'start' x '==' 'end' y@ holds:
--     @'amap' h (x '*' y) '==' 'amap' h y '*' 'amap' h x@.
class (HomOrientedDisjunctive h, Transformable (ObjectClass h) Mlt) => HomMultiplicativeDisjunctive h

instance
  ( CategoryDisjunctive h
  , HomMultiplicativeDisjunctive h
  )
  => HomMultiplicativeDisjunctive (Inv2 h)


instance HomMultiplicativeDisjunctive h => HomMultiplicative (Variant2 Covariant h)

instance
  ( TransformableMlt s
  , HomMultiplicativeDisjunctive h
  )
  => HomMultiplicativeDisjunctive (Sub s h)


type instance HomD Mlt h = HomMultiplicativeDisjunctive h

--------------------------------------------------------------------------------
-- DualisableMultiplicative -

-- | duality according to @__o__@ on @__s__@-structured 'Multiplicative' types,
--
-- __Properties__ Let @'DualisableMultiplicative' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) For all @p@ in @'Point' __x__@ holds:
-- @'toDualArw' q s ('one' p) '==' 'one' ('toDualPnt' q s p)@. 
--
-- (2) For all @x@, @y@ in @__x__@ with @'start' x '==' 'end' y@ holds:
-- @'toDualArw' q s (x '*' y) '==' 'toDualArw' q s y '*' 'toDualArw' q s x@.
--
-- where @q@ is any proxy for @__o__@.
class (DualisableOriented s o, Transformable s Mlt) => DualisableMultiplicative s o

instance (HomMultiplicative h, DualisableMultiplicative s o)
  => HomMultiplicativeDisjunctive (HomDisj s o h)

instance ( TransformableOrt s, TransformableMlt s, TransformableOp s
         , TransformableType s
         ) => DualisableMultiplicative s Op

--------------------------------------------------------------------------------
-- toDualOpMlt -

-- | the canonical 'Contravariant' isomorphism on 'Multiplicative' structures
-- between @__x__@ and @'Op' __x__@.
toDualOpMlt :: Multiplicative x => Variant2 Contravariant (IsoO Mlt Op) x (Op x)
toDualOpMlt = toDualO Struct

--------------------------------------------------------------------------------
-- relMapMltOne -

-- | validity that 'one' maps to 'one' according to the given mapplings.
relMapMltOne :: Struct Mlt x -> Struct Mlt y
  -> (x -> y) -> (Point x -> Point y) -> X (Point x) -> Statement
relMapMltOne Struct Struct mArw mPnt xp = Forall xp
  (\p -> (mArw (one p) == one (mPnt p)) :?> Params ["p":=show p])

--------------------------------------------------------------------------------
-- relMapMlt -

-- | validity of '*' as covariant operation according to the given mapping. 
relMapMltCov :: Struct Mlt x -> Struct Mlt y -> (x -> y) -> X (Mltp2 x) -> Statement
relMapMltCov Struct Struct mArw xmp = Label "Cov" :<=>: Forall xmp
  (\(Mltp2 f g) -> (mArw (f * g) == mArw f * mArw g) :?> Params ["f":=show f,"g":=show g])

-- | validity of '*' as contravariant operation according to the given mapping. 
relMapMltCnt :: Struct Mlt x -> Struct Mlt y -> (x -> y) -> X (Mltp2 x) -> Statement
relMapMltCnt Struct Struct mArw xmp = Label "Cnt" :<=>: Forall xmp
  (\(Mltp2 f g) -> (mArw (f * g) == mArw g * mArw f) :?> Params ["f":=show f,"g":=show g])
  
--------------------------------------------------------------------------------
-- prpDualisableMultiplicativeOne -

-- | validity according to 'DualisableMultiplicative', property 1.
prpDualisableMultiplicativeOne :: DualisableMultiplicative s o
  => q o -> Struct s x -> X (Point x) -> Statement
prpDualisableMultiplicativeOne q s xp = Prp "DualisableMultiplicativeOne" :<=>: Label "1" :<=>:
  relMapMltOne (tau s) (tau (tauO s)) mArw mPnt xp where
    mArw = toDualArw q s
    mPnt = toDualPnt q s

--------------------------------------------------------------------------------
-- prpDualisableMultiplicativeMlt -

-- | validity according to 'DualisableMultiplicative', property 2.
prpDualisableMultiplicativeMlt :: DualisableMultiplicative s o
  => q o -> Struct s x -> X (Mltp2 x) -> Statement
prpDualisableMultiplicativeMlt q s xmp = Prp "DualisableMultiplicativeMlt" :<=>: Label "2" :<=>:
  relMapMltCnt (tau s) (tau (tauO s)) mArw xmp where
    mArw = toDualArw q s

--------------------------------------------------------------------------------
-- XHomMlt -

-- | random variable for testing multiplicative homomorphisms.
data XHomMlt x = XHomMlt (X (Point x)) (X (Mltp2 x))

--------------------------------------------------------------------------------
-- xMltXHomMlt -

-- | the underlying 'XMomMlt'.
xMltHomMlt :: XMlt x -> XHomMlt x
xMltHomMlt (XMlt _ xp _ _ xm2 _) = XHomMlt xp xm2

--------------------------------------------------------------------------------
-- xosHomMlt -

-- | the 'XHomMlt' given by a @'XOrtSite' __d__@
xosHomMlt :: Multiplicative x => XOrtSite d x -> XHomMlt x
xosHomMlt xos = XHomMlt (xosPoint xos) (xMltp2 xos)

--------------------------------------------------------------------------------
-- prpHomMultiplicativeDisjunctive -

-- | validity according to 'HomMultiplicativeDisjunctive'.
prpHomMultiplicativeDisjunctive :: HomMultiplicativeDisjunctive h
  => h x y -> XHomMlt x -> Statement
prpHomMultiplicativeDisjunctive h (XHomMlt xp xm2) = Prp "HomDisjunctiveMultipliative"
  :<=>: case variant2 h of
    Covariant     -> Label "Cov" :<=>:
      And [ relMapMltOne sx sy mArw mPnt xp
          , relMapMltCov sx sy mArw xm2
          ]
    Contravariant -> Label "Cnt" :<=>:
      And [ relMapMltOne sx sy mArw mPnt xp
          , relMapMltCnt sx sy mArw xm2
          ]
  where
    sx = tau (domain h)
    sy = tau (range h)
    
    mArw = amap h
    mPnt = pmap h

--------------------------------------------------------------------------------
-- homDisjOpMlt -

-- | embedding a multiplicative homomorphism into a covariant @'HomDisj' __Mlt Op__@.
homDisjOpMlt :: HomMultiplicative h
  => h x y -> Variant2 Covariant (HomDisj Mlt Op h) x y
homDisjOpMlt = homDisj

--------------------------------------------------------------------------------
-- prpHomMultiplicative -

-- | validity according to 'HomMultiplicative'.
prpHomMultiplicative :: HomMultiplicative h
  => h x y -> XHomMlt x -> Statement
prpHomMultiplicative h xhMlt = Prp "HomMultiplicative"
  :<=>: prpHomMultiplicativeDisjunctive h' xhMlt where Covariant2 h' = homDisjOpMlt h

--------------------------------------------------------------------------------
-- prpHomDisjMultiplicative -

-- | validity according to 'HomMultiplicativeDisjunctive'.
prpHomDisjMultiplicative :: (HomMultiplicative h, DualisableMultiplicative s o)
  => Struct MltX x -> HomDisj s o h x y -> Statement
prpHomDisjMultiplicative Struct h = prpHomMultiplicativeDisjunctive h (xMltHomMlt xStandardMlt)

--------------------------------------------------------------------------------
-- xsoMltX -

-- | random variable for some 'Multiplicative' object classes .
xsoMltX :: s ~ MltX => X (SomeObjectClass (SHom s s Op (HomEmpty s)))
xsoMltX = xOneOf [ SomeObjectClass (Struct :: Struct MltX OS)
                 , SomeObjectClass (Struct :: Struct MltX N)
                 , SomeObjectClass (Struct :: Struct MltX (Op OS))
                 , SomeObjectClass (Struct :: Struct MltX (Id OS))
                 ]

--------------------------------------------------------------------------------
-- prpHomDisjOpMlt -

-- | validity for @'HomDisjEmpty' 'MltX' 'Op'@ beeing 'HomMultiplicativeDisjunctive'.
prpHomDisjOpMlt :: Statement
prpHomDisjOpMlt = Prp "prpHomDisjOpMlt" :<=>:
  And [ Forall xm (\(SomeMorphism h) -> prpHomDisjMultiplicative (domain h) h)
      ]
  where
    xm :: X (SomeMorphism (HomDisjEmpty MltX Op))
    xm = amap1 smCmpb2 $ xscmHomDisj xsoMltX XEmpty


