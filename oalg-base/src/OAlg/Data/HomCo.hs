
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Data.HomCo
-- Description : mapping between an object and its co-object.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- mapping between an object @m@ in @__m x__@ and its co-object, where @'Dual1' __m___ ~ __m__@.
module OAlg.Data.HomCo
  (
    -- * Category
    HomCo()
  , PathCo(..), rdcCoToFromCo, rdcCoToFromDual, rdcPathCo
  , MorCo(..), mcoStruct

    -- * Functor
  , FunctorCo(..), FunctorialCo

    -- * Iso
  , isoCo, IsoCo

    -- * Proposition
  , prpFunctorialCo
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

--------------------------------------------------------------------------------
-- MorCo -

data MorCo m s o x y where
  ToCo   :: (Structure s x, TransformableG m s s, TransformableG o s s)
         => MorCo m s o (o (m x)) (m (o x))
  FromCo :: (Structure s x, TransformableG m s s, TransformableG o s s)
         => MorCo m s o (m (o x)) (o (m x))

--------------------------------------------------------------------------------
-- mcoStruct -

-- | whitness that @__x__@ is a @__s__@ structure.
mcoStruct :: MorCo m s o (i (j x)) y -> Struct s x
mcoStruct ToCo   = Struct
mcoStruct FromCo = Struct

--------------------------------------------------------------------------------
-- tauCo -

tauCo :: (TransformableG m s s, TransformableG o s s) => Struct s x -> Struct s (m (o x))
tauCo = tauO . tauO


instance Morphism (MorCo m s o) where
  type ObjectClass (MorCo m s o) = s
  homomorphous ToCo   = tauCo Struct :>: tauCo Struct
  homomorphous FromCo = tauCo Struct :>: tauCo Struct

--------------------------------------------------------------------------------
-- toCo -

toCo :: (TransformableG m s s, TransformableG o s s)
  => Struct s x -> MorCo m s o (o (m x)) (m (o x))
toCo Struct = ToCo

--------------------------------------------------------------------------------
-- fromCo -

fromCo :: (TransformableG m s s, TransformableG o s s)
  => Struct s x -> MorCo m s o (m (o x)) (o (m x))
fromCo Struct = FromCo

--------------------------------------------------------------------------------
-- PathCo -

newtype PathCo m s o x y = PathCo (Path (SMorphism s s o (MorCo m s o)) x y)

rdcCoToFromCo :: PathCo m s o x y -> Rdc (PathCo m s o x y)
rdcCoToFromCo (PathCo p) = case p of
  SCov ToCo :. SCov FromCo :. p' -> reducesTo (PathCo p')    >>= rdcCoToFromCo
  SCov FromCo :. SCov ToCo :. p' -> reducesTo (PathCo p')    >>= rdcCoToFromCo  
  p' :. p''                      -> rdcCoToFromCo (PathCo p'')
                                >>= \(PathCo p'') -> return (PathCo (p' :. p''))
  _                              -> return (PathCo p)

rdcCoToFromDual :: PathCo m s o x y -> Rdc (PathCo m s o x y)
rdcCoToFromDual (PathCo p) = rdcPathSMorphism p >>= return . PathCo

rdcPathCo :: PathCo m s o x y -> Rdc (PathCo m s o x y)
rdcPathCo = rdcCoToFromCo >>>= rdcCoToFromDual

instance Reducible (PathCo m s o x y) where reduce = reduceWith rdcPathCo

--------------------------------------------------------------------------------
-- HomCo -

newtype HomCo m s o x y = HomCo (PathCo m s o x y)

--------------------------------------------------------------------------------
-- Constructable -

instance Exposable (HomCo m s o x y) where
  type Form (HomCo m s o x y) = PathCo m s o x y
  form (HomCo p) = p

instance Constructable (HomCo m s o x y) where make = HomCo . reduce

--------------------------------------------------------------------------------
-- sHomCo -

-- | functorial projection to 'HomCo'.
sHomCo :: SHom s s o (MorCo m s o) x y -> HomCo m s o x y
sHomCo = make . PathCo . form

--------------------------------------------------------------------------------
-- Category -

instance Morphism (HomCo m s o) where
  type ObjectClass (HomCo m s o) = s
  homomorphous (HomCo (PathCo p)) = homomorphous p

instance Category (HomCo m s o) where
  cOne = make . PathCo . cOne

  HomCo (PathCo f) . HomCo (PathCo g) = make (PathCo (f . g))

instance Disjunctive (HomCo m s o x y) where variant (HomCo (PathCo p)) = variant p
instance Disjunctive2 (HomCo m s o)
instance CategoryDisjunctive (HomCo m s o)

--------------------------------------------------------------------------------
-- IsoCo -

-- | isomorphism for 'HomCo'.
type IsoCo m s o = Inv2 (HomCo m s o)

--------------------------------------------------------------------------------
-- isoCo -

isoCoStruct :: (TransformableG m s s, TransformableG o s s)
  => Struct s (m x) -> Struct s (o (m x)) -> Struct s (m (o x))
  -> Struct s x -> Variant2 Contravariant (IsoCo m s o) (m x) (m (o x))
isoCoStruct sm@Struct Struct smo@Struct Struct = Contravariant2 (Inv2 t f) where
  t = make (PathCo (SCov ToCo :. SToDual :. IdPath sm))
  f = make (PathCo (SFromDual :. SCov FromCo :. IdPath smo)) 

-- | contravariant isomorphism.
isoCo ::(TransformableG m s s, TransformableG o s s)
  => Struct s x -> Variant2 Contravariant (IsoCo m s o) (m x) (m (o x))
isoCo s = isoCoStruct (tauO s) (tauO $ tauO s) (tauO $ tauO s) s

--------------------------------------------------------------------------------
-- ApplicativeG -

instance
  ( ApplicativeG d (MorCo m s o) (->)
  , DualisableG s (->) o d
  )
  => ApplicativeG (SVal d) (HomCo m s o) (->) where
  amapG (HomCo (PathCo p)) = amapG p

--------------------------------------------------------------------------------
-- FunctorialCo -

-- | functorial predicat for 'HomCo'.
--
-- __Properties__ Let @'FunctorialCo' __d s m o c__@, then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'amapG' ('fromCo' s) '.'  'amapG' ('toCo' s) '.=.' 'cOneDOF' f s@.
--
-- (2) @'amapG' ('toCo' s) '.' 'amapG' ('fromCo' s)  '.=.' 'cOneDCo' f s@.
--
-- where @f@ is anay proxy in @__q d s m o c__@.
class
  ( Category c
  , ApplicativeG d (MorCo m s o) c
  , TransformableG m s s, TransformableG o s s
  , TransformableG d s (ObjectClass c)
  ) => FunctorialCo d s m o c

--------------------------------------------------------------------------------
-- FunctorCo -

-- | whiteness of being 'FunctorialCo'.
data FunctorCo d s m o c where
  FunctorCo :: FunctorialCo d s m o c => FunctorCo d s m o c
  
--------------------------------------------------------------------------------
-- prpFunctorialCo -

cOneDOM :: FunctorCo d s m o c -> Struct s x -> c (d (o (m x))) (d (o (m x)))
cOneDOM FunctorCo = cOne . tauG . tauO . tauO

cOneDMO :: FunctorCo d s m o c -> Struct s x -> c (d (m (o x))) (d (m (o x)))
cOneDMO FunctorCo = cOne . tauG . tauO. tauO

relFunctorialCo :: EqExt c => FunctorCo d s m o c -> Struct s x -> Statement
relFunctorialCo f@FunctorCo s
  = And [ Label "1" :<=>: (amapG (fromCo s) .  amapG (toCo s) .=. cOneDOM f s)
        , Label "2" :<=>: (amapG (toCo s) . amapG (fromCo s)  .=. cOneDMO f s)
        ]

-- | validity according to 'FunctorialCo'.
prpFunctorialCo :: EqExt c => FunctorCo d s m o c -> Struct s x -> Statement
prpFunctorialCo m s = Prp "FunctoiralCo" :<=>: relFunctorialCo m s

--------------------------------------------------------------------------------
-- FunctorialG -

instance (FunctorialCo d s m o (->) , DualisableG s (->) o d)
  => FunctorialG (SVal d) (HomCo m s o) (->)

