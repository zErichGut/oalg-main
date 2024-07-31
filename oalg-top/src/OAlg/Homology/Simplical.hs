
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Homology.Simplical
-- Description : simplical structures admitting a face operator.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'Simplical' structures, i.e. family of types indexed by natural numbers admitting a face operator.
module OAlg.Homology.Simplical
  (  
    -- * Simplical
--    Simplical(..), Face(..), fcSimplex

    -- * Simplex
--  , Simplex(..), simplex

  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Natural
import OAlg.Entity.FinList

{-
--------------------------------------------------------------------------------
-- Face -

data Face s n x where
  EmptyFace :: Face s N0 x
  Face      :: s n x -> Face s (n+1) x

instance Show (Face s N0 x) where show EmptyFace = "EmptyFace"
deriving instance Show (s n x) => Show (Face s (S n) x)

--------------------------------------------------------------------------------
-- fcSimplex -

fcSimplex :: Face s (n+1) x -> s n x
fcSimplex (Face s) = s

--------------------------------------------------------------------------------
-- Simplical -

class Typeable s => Simplical s x where
  sOrd :: Struct Ord' (s n x)
  sEnt :: Attestable n => Struct Ent (s n x)
  faces :: s n x -> FinList (n+1) (Face s n x)

--------------------------------------------------------------------------------
-- Simplex -

newtype Simplex n x = Simplex (FinList (n+1) x) deriving (Show,Eq,Ord,Validable,Entity)


(<:) :: x -> Face Simplex n x -> Face Simplex (n+1) x
x <: EmptyFace = Face (Simplex (x:|Nil))
x <: (Face (Simplex xs)) = Face (Simplex (x:|xs))


instance (Ord x, Entity x) => Simplical Simplex x where
  sOrd = Struct
  sEnt = Struct
  faces (Simplex (_:|Nil))       = EmptyFace:|Nil
  faces (Simplex (x:|xs@(_:|_))) = Face (Simplex xs) :| amap1 (x<:) (faces (Simplex xs))

--------------------------------------------------------------------------------
-- simplex -

simplex :: Enum v => Any n -> v -> Simplex n v
simplex n v = Simplex $ spl n v where
  spl :: Enum v => Any n -> v -> FinList (n+1) v
  spl W0 v = v :| Nil
  spl (SW n) v = v :| spl n (succ v) 

-}
