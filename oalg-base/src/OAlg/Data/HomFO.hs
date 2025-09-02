
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Data.HomFO
-- Description : parameterized contravariant homomorphisms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- parameterized contravariant homomorphisms.
module OAlg.Data.HomFO
  ( -- * Category
    HomFO()
  , PathFO(..), rdcFOToFromFO, rdcFOToFromDual, rdcPathFO

    -- * Functor
  , FunctorFO(..), FunctorialFO

    -- * Iso
  , isoFO

    -- * Proposition
  , prpFunctorialFO  
  )
  where

import Control.Monad

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.Dualisable
import OAlg.Category.Path

import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Variant

-- MorFO is HomOriented, HomMultipicative ...
-- HomFO is HomOrientedDisjunctive, HomMultipicativeDisjunctive ...

--------------------------------------------------------------------------------
-- MorFO -

data MorFO s f o x y where
  ToFO   :: (Structure s (f (o x)), Structure s (o (f x))) => MorFO s f o (o (f x)) (f (o x))
  FromFO :: (Structure s (f (o x)), Structure s (o (f x))) => MorFO s f o (f (o x)) (o (f x))

instance Morphism (MorFO s f o) where
  type ObjectClass (MorFO s f o) = s
  homomorphous ToFO   = Struct :>: Struct
  homomorphous FromFO = Struct :>: Struct

--------------------------------------------------------------------------------
-- tauFO -

tauFO :: (TransformableG f s s, TransformableG o s s) => Struct s x -> Struct s (f (o x))
tauFO = tauO . tauO

tauOF :: (TransformableG f s s, TransformableG o s s) => Struct s x -> Struct s (o (f x))
tauOF = tauO . tauO
--------------------------------------------------------------------------------
-- toFO -

toFOStruct :: Struct s (f (o x)) -> Struct s (o (f x)) -> MorFO s f o (o (f x)) (f (o x))
toFOStruct Struct Struct = ToFO

toFO :: (TransformableG f s s, TransformableG o s s)
  => Struct s x -> MorFO s f o (o (f x)) (f (o x))
toFO s = toFOStruct (tauFO s) (tauFO s)

--------------------------------------------------------------------------------
-- fromFO -

fromFOStruct :: Struct s (f (o x)) -> Struct s (o (f x)) -> MorFO s f o (f (o x)) (o (f x))
fromFOStruct Struct Struct = FromFO

fromFO :: (TransformableG f s s, TransformableG o s s)
  => Struct s x -> MorFO s f o (f (o x)) (o (f x))
fromFO s = fromFOStruct (tauFO s) (tauFO s)

--------------------------------------------------------------------------------
-- PathFO -

newtype PathFO s f o x y = PathFO (Path (SMorphism s s o (MorFO s f o)) x y)

rdcFOToFromFO :: PathFO s f o x y -> Rdc (PathFO s f o x y)
rdcFOToFromFO (PathFO p) = case p of
  SCov ToFO :. SCov FromFO :. p' -> reducesTo (PathFO p')    >>= rdcFOToFromFO
  SCov FromFO :. SCov ToFO :. p' -> reducesTo (PathFO p')    >>= rdcFOToFromFO  
  p' :. p''                      -> rdcFOToFromFO (PathFO p'')
                                >>= \(PathFO p'') -> return (PathFO (p' :. p''))
  _                              -> return (PathFO p)

rdcFOToFromDual :: PathFO s f o x y -> Rdc (PathFO s f o x y)
rdcFOToFromDual (PathFO p) = rdcPathSMorphism p >>= return . PathFO

rdcPathFO :: PathFO s f o x y -> Rdc (PathFO s f o x y)
rdcPathFO = rdcFOToFromFO >>>= rdcFOToFromDual

instance Reducible (PathFO s f o x y) where reduce = reduceWith rdcPathFO

--------------------------------------------------------------------------------
-- HomFO -

newtype HomFO s f o x y = HomFO (PathFO s f o x y)

--------------------------------------------------------------------------------
-- Constructable -

instance Exposable (HomFO s f o x y) where
  type Form (HomFO s f o x y) = PathFO s f o x y
  form (HomFO p) = p

instance Constructable (HomFO s f o x y) where make = HomFO . reduce

--------------------------------------------------------------------------------
-- sHomFO -

-- | functorial projection to 'HomFO'.
sHomFO :: SHom s s o (MorFO s f o) x y -> HomFO s f o x y
sHomFO = make . PathFO . form

--------------------------------------------------------------------------------
-- Category -

instance Morphism (HomFO s f o) where
  type ObjectClass (HomFO s f o) = s
  homomorphous (HomFO (PathFO p)) = homomorphous p

instance Category (HomFO s f o) where
  cOne = make . PathFO . cOne

  HomFO (PathFO f) . HomFO (PathFO g) = make (PathFO (f . g))

instance Disjunctive (HomFO s f o x y) where variant (HomFO (PathFO p)) = variant p
instance Disjunctive2 (HomFO s f o)
instance CategoryDisjunctive (HomFO s f o)

--------------------------------------------------------------------------------
-- IsoFO -

-- | isomorphism for 'HomFO'.
type IsoFO s f o = Inv2 (HomFO s f o)

--------------------------------------------------------------------------------
-- isoFO -

isoFOStruct :: Struct s (f (o x)) -> Struct s (o (f x)) -> Struct s (f x)
  -> Variant2 Contravariant (IsoFO s f o) (f x) (f (o x))
isoFOStruct sfo@Struct Struct sf@Struct = Contravariant2 (Inv2 t f) where
  t = make (PathFO (SCov ToFO :. SToDual :. IdPath sf))
  f = make (PathFO (SFromDual :. SCov FromFO :. IdPath sfo)) 

-- | contravariant isomorphism.
isoFO ::(TransformableG f s s, TransformableG o s s)
  => Struct s x -> Variant2 Contravariant (IsoFO s f o) (f x) (f (o x))
isoFO s = isoFOStruct (tauO $ tauO s) (tauO $ tauO s) (tauO s)

--------------------------------------------------------------------------------
-- ApplicativeG -

instance
  ( ApplicativeG d (MorFO s f o) (->)
  , DualisableG s (->) o d
  )
  => ApplicativeG (SVal d) (HomFO s f o) (->) where
  amapG (HomFO (PathFO p)) = amapG p

--------------------------------------------------------------------------------
-- FunctorialFO -

-- | functorial predicat for 'HomFO'.
--
-- __Properties__ Let @'FunctorialFO' __d s f o c__@, then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'amapG' ('fromFO' s) '.'  'amapG' ('toFO' s) '.=.' 'cOneDOF' f s@.
--
-- (2) @'amapG' ('toFO' s) '.' 'amapG' ('fromFO' s)  '.=.' 'cOneDFO' f s@.
--
-- where @f@ is anay proxy in @__q d s f o c__@.
class
  ( Category c
  , ApplicativeG d (MorFO s f o) c
  , TransformableG f s s, TransformableG o s s
  , TransformableG d s (ObjectClass c)
  ) => FunctorialFO d s f o c

--------------------------------------------------------------------------------
-- FunctorFO -

-- | whiteness of being 'FunctorialFO'.
data FunctorFO d s f o c where
  FunctorFO :: FunctorialFO d s f o c => FunctorFO d s f o c
  
--------------------------------------------------------------------------------
-- prpFunctorialFO -

cOneDOF :: FunctorFO d s f o c -> Struct s x -> c (d (o (f x))) (d (o (f x)))
cOneDOF FunctorFO = cOne . tauG . tauO . tauO

cOneDFO :: FunctorFO d s f o c -> Struct s x -> c (d (f (o x))) (d (f (o x)))
cOneDFO FunctorFO = cOne . tauG . tauO. tauO

relFunctorialFO :: EqExt c => FunctorFO d s f o c -> Struct s x -> Statement
relFunctorialFO f@FunctorFO s
  = And [ Label "1" :<=>: (amapG (fromFO s) .  amapG (toFO s) .=. cOneDOF f s)
        , Label "2" :<=>: (amapG (toFO s) . amapG (fromFO s)  .=. cOneDFO f s)
        ]

-- | validity according to 'FunctorialFO'.
prpFunctorialFO :: EqExt c => FunctorFO d s f o c -> Struct s x -> Statement
prpFunctorialFO f s = Prp "FunctoiralFO" :<=>: relFunctorialFO f s

--------------------------------------------------------------------------------
-- FunctorialG -

instance (FunctorialFO d s f o (->) , DualisableG s (->) o d)
  => FunctorialG (SVal d) (HomFO s f o) (->)

