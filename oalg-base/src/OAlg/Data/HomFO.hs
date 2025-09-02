
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

-- |
-- Module      : OAlg.Data.HomFO
-- Description : parameterized contravariant homomorphisms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- parameterized contravariant homomorphisms.
module OAlg.Data.HomFO
  (
  )
  where

import Control.Monad

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.Dualisable
import OAlg.Category.Path

import OAlg.Data.Reducible
import OAlg.Data.Constructable

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
-- PathFO -

newtype PathFO s f o x y = PathFO (Path (SMorphism s s o (MorFO s f o)) x y)

rdcToFromFO :: PathFO s f o x y -> Rdc (PathFO s f o x y)
rdcToFromFO (PathFO p) = case p of
  SCov ToFO :. SCov FromFO :. p' -> reducesTo (PathFO p')    >>= rdcToFromFO
  SCov FromFO :. SCov ToFO :. p' -> reducesTo (PathFO p')    >>= rdcToFromFO  
  p' :. p''                      -> rdcToFromFO (PathFO p'')
                                >>= \(PathFO p'') -> return (PathFO (p' :. p''))
  _                              -> return (PathFO p)

rdcToFromDual :: PathFO s f o x y -> Rdc (PathFO s f o x y)
rdcToFromDual (PathFO p) = rdcPathSMorphism p >>= return . PathFO

rdcPathFO :: PathFO s f o x y -> Rdc (PathFO s f o x y)
rdcPathFO = rdcToFromFO >>>= rdcToFromDual

instance Reducible (PathFO s f o x y) where reduce = reduceWith rdcPathFO

--------------------------------------------------------------------------------
-- HomFO -

newtype HomFO s f o x y = HomFO (PathFO s f o x y)

--------------------------------------------------------------------------------
-- HomFO - Constructable -

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
-- ApplicativeG - HomFO -

instance
  ( ApplicativeG d (MorFO s f o) (->)
  , DualisableG s (->) o d
  )
  => ApplicativeG (SVal d) (HomFO s f o) (->) where
  amapG (HomFO (PathFO p)) = amapG p

--------------------------------------------------------------------------------
-- FunctorialHomFO -

-- |
--
-- __Properties__
--
-- @'fromFo' s '.'  'toFO' s '.=.' 'cOne' s@.
class
  ( Category c, ApplicativeG d (MorFO s f o) c
  , DualisableG s c o d
  ) => FunctorialHomFO d s f o c

-- instance FunctorialHomFO d s f o (->) => FunctorialG (SVal d) (HomFO s f o) (->)
