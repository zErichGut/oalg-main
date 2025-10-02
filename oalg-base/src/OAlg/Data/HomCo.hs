
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
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
    HomCo(), toCo, fromCo, sHomCo
  , PathCo(..), rdcCoToFromCo, rdcCoToFromDual, rdcPathCo
  , MorCo(..), mcoStruct

    -- * Functor
  , ApplicativeMorCo, FunctorialHomCo, FunctorHomCo(..)

    -- * Iso
  , isoCo, IsoCo

    -- * X
  , xscHomCo
  
    -- * Proposition
  , prpFunctorialHomCo
  )
  where

import Control.Monad

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.Dualisable
import OAlg.Category.Path
import OAlg.Category.Unify

import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Variant

--------------------------------------------------------------------------------
-- MorCo -

-- | morphism to and from the co-cobject.
data MorCo m s o x y where
  ToCo   :: (Structure s x, TransformableG m s s, TransformableG o s s)
         => MorCo m s o (o (m x)) (m (o x))
  FromCo :: (Structure s x, TransformableG m s s, TransformableG o s s)
         => MorCo m s o (m (o x)) (o (m x))

deriving instance Show (MorCo m s o x y)
instance Show2 (MorCo m s o)

--------------------------------------------------------------------------------
-- mcoStruct -

-- | whitness that @__x__@ is a @__s__@ structure.
mcoStruct :: MorCo m s o (i (j x)) y -> Struct s x
mcoStruct ToCo   = Struct
mcoStruct FromCo = Struct

--------------------------------------------------------------------------------
-- tauCo -

-- | propagating the @__s__@ structure on @__x__@ to its co-object.
tauCo :: (TransformableG m s s, TransformableG o s s) => Struct s x -> Struct s (m (o x))
tauCo = tauO . tauO

instance Morphism (MorCo m s o) where
  type ObjectClass (MorCo m s o) = s
  homomorphous ToCo   = tauCo Struct :>: tauCo Struct
  homomorphous FromCo = tauCo Struct :>: tauCo Struct

--------------------------------------------------------------------------------
-- toCo -

-- | to the co-object.
toCo :: (TransformableG m s s, TransformableG o s s)
  => Struct s x -> MorCo m s o (o (m x)) (m (o x))
toCo Struct = ToCo

--------------------------------------------------------------------------------
-- fromCo -

-- | from the co-cobject.
fromCo :: (TransformableG m s s, TransformableG o s s)
  => Struct s x -> MorCo m s o (m (o x)) (o (m x))
fromCo Struct = FromCo

--------------------------------------------------------------------------------
-- PathCo -

-- | path of 'SMorphism' over 'MorCo'.
newtype PathCo m s o x y = PathCo (Path (SMorphism s s o (MorCo m s o)) x y)
  deriving (Show)

instance Show2 (PathCo m s o)

-- | reducing a path according to the rules:
--
-- (1) @'SCov' 'ToCo' ':.' 'SCov' 'FromCo' ':.' p'@ reduces to @p'@.
--
-- (2) @'SCov' 'FromCo' ':.' 'SCov' 'ToCo' ':.' p'@ reduces to @p'@.
rdcCoToFromCo :: PathCo m s o x y -> Rdc (PathCo m s o x y)
rdcCoToFromCo (PathCo p) = case p of
  SCov ToCo :. SCov FromCo :. p' -> reducesTo (PathCo p')    >>= rdcCoToFromCo
  SCov FromCo :. SCov ToCo :. p' -> reducesTo (PathCo p')    >>= rdcCoToFromCo  
  p' :. p''                      -> rdcCoToFromCo (PathCo p'')
                                >>= \(PathCo p'') -> return (PathCo (p' :. p''))
  _                              -> return (PathCo p)

-- | reducing a 'PathCo' according to 'rdcPathSMorphism'.
rdcCoToFromDual :: PathCo m s o x y -> Rdc (PathCo m s o x y)
rdcCoToFromDual (PathCo p) = rdcPathSMorphism p >>= return . PathCo

-- | applying the rules of 'rdcCoToFromCo' and 'rdcCoToFromDual'.
rdcPathCo :: PathCo m s o x y -> Rdc (PathCo m s o x y)
rdcPathCo = rdcCoToFromCo >>>= rdcCoToFromDual

instance Reducible (PathCo m s o x y) where reduce = reduceWith rdcPathCo

--------------------------------------------------------------------------------
-- HomCo -

-- | homomorphism for applications of objects @__m__@ over @__x__@.
newtype HomCo m s o x y = HomCo (PathCo m s o x y)
  deriving (Show)

instance Show2 (HomCo m s o)

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
-- ApplicativeMorCo -

-- | helper class to avoid undecidable instances.
class ApplicativeG d (MorCo m s o) c => ApplicativeMorCo d m s o c

instance
  ( ApplicativeMorCo d m s o (->)
  , DualisableG s (->) o d
  )
  => ApplicativeG d (HomCo m s o) (->) where
  amapG (HomCo (PathCo p)) d = d' where SVal d' = amapG p (SVal d)  

--------------------------------------------------------------------------------
-- FunctorialHomCo -

-- | functorial predicat for 'HomCo'.
--
-- __Properties__ Let @'FunctorialHomCo' __d s m o c__@, then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'amapG' ('fromCo' s) '.'  'amapG' ('toCo' s) '.=.' 'cOneDOM' f s@.
--
-- (2) @'amapG' ('toCo' s) '.' 'amapG' ('fromCo' s)  '.=.' 'cOneDMO' f s@.
--
-- where @f@ is anay proxy in @__q d s m o c__@.
class
  ( Category c
  , ApplicativeMorCo d m s o c
  , TransformableG m s s, TransformableG o s s
  , TransformableG d s (ObjectClass c)
  ) => FunctorialHomCo d m s o c

--------------------------------------------------------------------------------
-- FunctorHomCo -

-- | whiteness of being 'FunctorialHomCo'.
data FunctorHomCo d m s o c where
  FunctorHomCo :: FunctorialHomCo d m s o c => FunctorHomCo d m s o c
  
--------------------------------------------------------------------------------
-- prpFunctorialHomCo -

cOneDOM :: FunctorHomCo d m s o c -> Struct s x -> c (d (o (m x))) (d (o (m x)))
cOneDOM FunctorHomCo = cOne . tauG . tauO . tauO

cOneDMO :: FunctorHomCo d m s o c -> Struct s x -> c (d (m (o x))) (d (m (o x)))
cOneDMO FunctorHomCo = cOne . tauG . tauO. tauO

relFunctorialHomCo :: EqExt c => FunctorHomCo d m s o c -> Struct s x -> Statement
relFunctorialHomCo f@FunctorHomCo s
  = And [ Label "1" :<=>: (amapG (fromCo s) .  amapG (toCo s) .=. cOneDOM f s)
        , Label "2" :<=>: (amapG (toCo s) . amapG (fromCo s)  .=. cOneDMO f s)
        ]

-- | validity according to 'FunctorialHomCo'.
prpFunctorialHomCo :: EqExt c => FunctorHomCo d m s o c -> Struct s x -> Statement
prpFunctorialHomCo m s = Prp "FunctoiralCo" :<=>: relFunctorialHomCo m s

--------------------------------------------------------------------------------
-- FunctorialG -

instance (FunctorialHomCo d m s o (->) , DualisableG s (->) o d)
  => FunctorialG d (HomCo m s o) (->)

--------------------------------------------------------------------------------
-- xHomCo -

-- | random variable for some composable 'HomCo's.
xscHomCo :: TransformableG o s s
  => N -> X (SomeObjectClass (HomCo m s o)) -> X (SomeMorphism (MorCo m s o))
  -> X (SomeCmpb2 (HomCo m s o))
xscHomCo n xsoHomCo xsmMorCo
  = amap1 soce $ xSctSomeCmpb2 n (amap1 socSHom xsoHomCo) xsmMorCo where
  
  socSHom :: SomeObjectClass (HomCo m s o) -> SomeObjectClass (SHom s s o (MorCo m s o))
  socSHom (SomeObjectClass o) = SomeObjectClass o

  soce :: SomeCmpb2 (SHom s s o (MorCo m s o)) -> SomeCmpb2 (HomCo m s o)
  soce (SomeCmpb2 f g) = SomeCmpb2 (sHomCo f) (sHomCo g)


