
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Homology.Simplex
-- Description : simplices and there faces..
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Simplices and there faces.
module OAlg.Homology.Simplex
  (  
    -- * Simplex
    Simplex(..), simplex

    -- * Face
  , Face(..), fcSimplex
  , faces, (<:)

  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Natural
import OAlg.Entity.FinList

--------------------------------------------------------------------------------
-- Simplex -

-- | @__n__@-dimensional simplex, given by @__n__ + 1@ points in @__x__@.
newtype Simplex n x = Simplex (FinList (n+1) x) deriving (Show,Eq,Ord,Validable,Entity)

--------------------------------------------------------------------------------
-- simplex -

-- | the @__n__@-diemensional 'Simplex', starting at the given enumerating value @v@.
--
--  __Example__
--
-- >>> simplex (attest :: Any N4) (0::N)
-- Simplex (0 :| (1 :| (2 :| (3 :| (4 :| Nil)))))
simplex :: Enum v => Any n -> v -> Simplex n v
simplex n v = Simplex $ spl n v where
  spl :: Enum v => Any n -> v -> FinList (n+1) v
  spl W0 v = v :| Nil
  spl (SW n) v = v :| spl n (succ v) 

--------------------------------------------------------------------------------
-- Face -

-- | a 'Face' of a @__n__@-dimensional 'Simplex', which is a @__n__ - 1@-dimensional 'Simplex'.
data Face n x where
  FaceEmpty :: Face N0 x
  Face      :: Simplex n x -> Face (n+1) x

deriving instance Show x => Show (Face n x)
deriving instance Eq x => Eq (Face n x)
deriving instance Ord x => Ord (Face n x)

instance Validable x => Validable (Face n x) where
  valid FaceEmpty = SValid
  valid (Face s)  = valid s

instance (Entity x, Typeable n) => Entity (Face n x)

--------------------------------------------------------------------------------
-- (<:) -

(<:) :: x -> Face n x -> Face (n+1) x
x <: FaceEmpty = Face (Simplex (x:|Nil))
x <: (Face (Simplex xs)) = Face (Simplex (x:|xs))

--------------------------------------------------------------------------------
-- fcSimplex -

fcSimplex :: Face (n+1) x -> Simplex n x
fcSimplex (Face s) = s

--------------------------------------------------------------------------------
-- faces -

-- | the 'Face's of a 'Simplex'.
faces :: Simplex n x -> FinList (n+1) (Face n x)
faces (Simplex (_:|Nil))       = FaceEmpty:|Nil
faces (Simplex (x:|xs@(_:|_))) = Face (Simplex xs) :| amap1 (x<:) (faces (Simplex xs))

{-
--------------------------------------------------------------------------------
-- Face -

data Face s n x where
  FaceEmpty :: Face s N0 x
  Face      :: s n x -> Face s (n+1) x

instance Show (Face s N0 x) where show FaceEmpty = "FaceEmpty"
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


instance (Ord x, Entity x) => Simplical Simplex x where
  sOrd = Struct
  sEnt = Struct
  faces (Simplex (_:|Nil))       = FaceEmpty:|Nil
  faces (Simplex (x:|xs@(_:|_))) = Face (Simplex xs) :| amap1 (x<:) (faces (Simplex xs))


-}
