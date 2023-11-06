
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Simplex
-- Description : definition of an abstract simplex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Simplex'.
module OAlg.Homology.Simplex
  (
    -- * Simplex
    Simplex(..), splHead
  , faces, faces', isFace

    -- ** Construction
  , vertex, (<:)

    -- * FAce
  , Face(..), fcSimplex
  
  ) where


import Data.Typeable
import Data.Foldable (toList)

import OAlg.Prelude

import OAlg.Entity.Natural
import OAlg.Entity.FinList as F hiding (zip) 

--------------------------------------------------------------------------------
-- Simplex - 

-- | @__n__@-dimensional simplex given by @n t'+' 1@ vertices in @__v__@.
newtype Simplex n v = Simplex (FinList (n+1) v) deriving (Show,Eq,Ord)
-- we relay on the fact that the ordering of simplices is derived!


instance Validable v => Validable (Simplex n v) where
  valid (Simplex vs) = valid vs

instance (Entity v, Typeable n) => Entity (Simplex n v)

--------------------------------------------------------------------------------
-- Face -

-- | face of a @__n__@-dimensional 'Simplex' with vertices in @__v__@.
data Face n v where
  EmptyFace :: Face N0 v
  Face      :: Simplex n v -> Face (n+1) v

deriving instance Show v => Show (Face n v)
deriving instance Eq x => Eq (Face n x)

--------------------------------------------------------------------------------
-- splHead -

splHead :: Simplex n v -> v
splHead (Simplex (v:|_)) = v
        
--------------------------------------------------------------------------------
-- fcSimplex -

fcSimplex :: Face (n+1) v -> Simplex n v
fcSimplex (Face s) = s

--------------------------------------------------------------------------------
-- vertex -

vertex :: v -> Simplex N0 v
vertex v = Simplex (v:|Nil)

--------------------------------------------------------------------------------
-- (<:) -

(<:) :: v -> Face n v -> Face (n + 1) v
v <: EmptyFace           = Face (Simplex (v:|Nil))
v <: (Face (Simplex vs)) = Face (Simplex (v:|vs))

--------------------------------------------------------------------------------
-- faces -

-- | the faces of a simplex.
faces :: Simplex n v -> FinList (n + 1) (Face n v)
faces (Simplex (_:|Nil))       = EmptyFace :| Nil
faces (Simplex (v:|vs@(_:|_))) = Face (Simplex vs) :| amap1 (v<:) (faces (Simplex vs))


faces' :: Simplex n v -> [Face n v]
faces' = toList . faces

--------------------------------------------------------------------------------
-- isFace -

isFace :: Face n v -> Simplex n v -> Bool
isFace = error "nyi"

