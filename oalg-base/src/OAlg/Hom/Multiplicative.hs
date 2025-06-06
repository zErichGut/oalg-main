

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
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
    HomDisjunctiveMultiplicative
  , FunctorialMultiplicative
  , isoOpMlt

    -- * Covariant
  , HomMultiplicative

    -- * Dualisable
  , DualisableMultiplicative

    -- * Proposition
  , prpHomDisjunctiveMultiplicative
  , prpHomOrtMultiplicative, prpHomOrtOpEmptyMlt
  , prpDualisableMultiplicativeOne
  , prpDualisableMultiplicativeMlt
  , relMapMltOne, relMapMltCov, relMapMltCnt

  )
  where

import OAlg.Prelude

import OAlg.Data.Identity

import OAlg.Category.SDuality
import OAlg.Category.Unify
import OAlg.Category.Path

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative

import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- HomMultiplicative -

-- | covariant homomorphisms between 'Multiplicative' structures.
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

instance (TransformableOrt s, TransformableMlt s) => HomMultiplicative (HomEmpty s)

--------------------------------------------------------------------------------
-- HomDisjunctiveMultiplicative -

-- | disjunctive homomorphisms between 'Multiplicative' structures.
--
-- __Propoerty__ Let @'HomDisjunctiveMultiplicative' __h__@, then
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
class (HomDisjunctiveOriented h, Transformable (ObjectClass h) Mlt) => HomDisjunctiveMultiplicative h

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
  => HomDisjunctiveMultiplicative (HomOrt s o h)

instance DualisableMultiplicative Mlt Op
instance DualisableMultiplicative MltX Op

--------------------------------------------------------------------------------
-- FunctorialMultiplicative -

class (FunctorialOriented h, HomDisjunctiveMultiplicative h) => FunctorialMultiplicative h

instance (HomMultiplicative h, DualisableMultiplicative s o)
  => FunctorialMultiplicative (HomOrt s o h)

--------------------------------------------------------------------------------
-- isoOpMlt -

isoOpMlt :: Multiplicative x => Variant2 Contravariant (Inv2 (HomOrtEmpty Mlt Op)) x (Op x)
isoOpMlt = Contravariant2 (Inv2 t f) where
  Contravariant2 t = cToDual Struct
  Contravariant2 f = cFromDual Struct

--------------------------------------------------------------------------------
-- relMapMltOne -

relMapMltOne :: Struct Mlt x -> Struct Mlt y
  -> (x -> y) -> (Point x -> Point y) -> X (Point x) -> Statement
relMapMltOne Struct Struct mArw mPnt xp = Forall xp
  (\p -> (mArw (one p) == one (mPnt p)) :?> Params ["p":=show p])

--------------------------------------------------------------------------------
-- relMapMlt -

relMapMltCov :: Struct Mlt x -> Struct Mlt y -> (x -> y) -> X (Mltp2 x) -> Statement
relMapMltCov Struct Struct mArw xmp = Label "Cov" :<=>: Forall xmp
  (\(Mltp2 f g) -> (mArw (f * g) == mArw f * mArw g) :?> Params ["f":=show f,"g":=show g])

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
-- prpHomDisjunctiveMultiplicative -

prpHomDisjunctiveMultiplicative :: HomDisjunctiveMultiplicative h
  => h x y -> XMlt x -> Statement
prpHomDisjunctiveMultiplicative h (XMlt _ xp _ _ xm2 _) = Prp "HomDisjunctiveMultipliative"
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
-- prpHomOrtMultiplicative -

prpHomOrtMultiplicative :: (HomMultiplicative h, DualisableMultiplicative s o)
  => Struct MltX x -> HomOrt s o h x y -> Statement
prpHomOrtMultiplicative Struct h = prpHomDisjunctiveMultiplicative h xStandardMlt
  
--------------------------------------------------------------------------------
-- prpHomOrtOpEmptyMlt -

-- | validity for @'HomOrtEmpty' 'MltX' 'Op'@ beeing 'HomDisjunctiveMultiplicative'.
prpHomOrtOpEmptyMlt :: Statement
prpHomOrtOpEmptyMlt = Prp "prpHomOrtOpEmptyMlt" :<=>:
  And [ Forall xm (\(SomeMorphism h) -> prpHomOrtMultiplicative (domain h) h)
      ]

  where

    xo :: X (SomeObjectClass (SHom Ort MltX Op (HomEmpty MltX)))
    xo = xOneOf [ SomeObjectClass (Struct :: Struct MltX OS)
                , SomeObjectClass (Struct :: Struct MltX N)
                , SomeObjectClass (Struct :: Struct MltX (Op OS))
                , SomeObjectClass (Struct :: Struct MltX (Id OS))
                ]

    
    xm :: X (SomeMorphism (HomOrtEmpty MltX Op))
    xm = amap1 (\(SomeMorphism h) -> SomeMorphism (HomOrt h)) $ xSctSomeMrph 10 xo

