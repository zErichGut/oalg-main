
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Structure.FibredOriented
-- Description : definition of fibred oriented structures.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'FibredOriented' structures.
module OAlg.Structure.FibredOriented
  (
    -- * Fibred Oriented
    FibredOriented, FbrOrt, TransformableFbrOrt, tauFbrOrt

    -- * X
  , XFbrOrt, FbrOrtX

    -- * Proposition
  , prpFbrOrt
  )
  where

import Data.Kind

import Data.List (map)

import OAlg.Prelude

import OAlg.Structure.Oriented

import OAlg.Structure.Fibred.Definition

--------------------------------------------------------------------------------
-- FibredOriented -


-- | 'Fibred' and 'Oriented' structure with matching 'root' and 'orientation'.
--
--   __Property__ Let __@d@__ be a 'FibredOriented' structure, then holds:
--
--   (1) @'root' '.=.' 'orientation'@.
--
--   __Note__ 'FibredOriented' structures are required for
--  'OAlg.Structure.Distributive.Distributive' structures.
class (Fibred d, Oriented d, Root d ~ Orientation (Point d)) => FibredOriented d

--------------------------------------------------------------------------------
-- Fibred - Instance -

instance FibredOriented ()
instance FibredOriented Int
instance FibredOriented Integer
instance FibredOriented N
instance FibredOriented Z
instance FibredOriented Q
instance Entity p => FibredOriented (Orientation p)
instance FibredOriented x => FibredOriented (Id x)

instance FibredOriented x => Fibred (Op x)
instance FibredOriented x => FibredOriented (Op x)

instance FibredOriented f => Dualisable (Sheaf f) where
  toDual (Sheaf r fs)     = Sheaf (transpose r) (map Op fs)
  fromDual (Sheaf r' fs') = Sheaf (transpose r') (map fromOp fs')

--------------------------------------------------------------------------------
-- FbrOrt -
  
-- | type representing the class of 'FibredOriented' structures.
data FbrOrt

type instance Structure FbrOrt x = FibredOriented x

instance Transformable FbrOrt Typ where tau Struct = Struct
instance Transformable FbrOrt Ent where tau Struct = Struct
instance Transformable FbrOrt Fbr where tau Struct = Struct
instance Transformable FbrOrt Ort where tau Struct = Struct

instance TransformableOp FbrOrt

instance TransformableG Op FbrOrt FbrOrt where tauG Struct = Struct
instance TransformableGRefl Op FbrOrt

--------------------------------------------------------------------------------
-- TransformableFbrOrt -

-- | transformable to 'FibredOriented' structure.
class ( Transformable s Fbr, Transformable s Ort
      , Transformable s FbrOrt
      ) => TransformableFbrOrt s

instance TransformableTyp FbrOrt
instance TransformableOrt FbrOrt
instance TransformableFbr FbrOrt
instance TransformableFbrOrt FbrOrt

--------------------------------------------------------------------------------
-- tauFbrOrt -

-- | 'tau' for 'FbrOrt'.
tauFbrOrt :: Transformable s FbrOrt => Struct s x -> Struct FbrOrt x
tauFbrOrt = tau

--------------------------------------------------------------------------------
-- XFbrOrt -

-- | random variable type for validating 'FibredOriented' structures. 
type XFbrOrt = X

--------------------------------------------------------------------------------
-- xFbrOrtOrnt -

-- | random variable for the 'FibredOriented' structure of @'Orientation' p@.
xFbrOrtOrnt :: X p -> XFbrOrt (Orientation p)
xFbrOrtOrnt = xFbrOrnt

--------------------------------------------------------------------------------
-- xoFbrOrt -

-- | the associated random variable for validation 'FibredOriented' structures.
xoFbrOrt :: XOrtOrientation f -> XFbrOrt f
xoFbrOrt = xoOrt

--------------------------------------------------------------------------------
-- FbrOrtX -

-- | type representing the class 'FibredOriented' equipped with standard random variables.
data FbrOrtX

type instance Structure FbrOrtX x = (FibredOriented x, XStandard x, XStandardPoint x)

instance Transformable FbrOrtX Ort where tau Struct = Struct
instance TransformableOrt FbrOrtX

instance TransformableG Op FbrOrtX FbrOrtX where tauG Struct = Struct
instance TransformableOp FbrOrtX

instance Transformable FbrOrtX Fbr where tau Struct = Struct
instance TransformableFbr FbrOrtX
instance Transformable FbrOrtX FbrOrt where tau Struct = Struct
instance TransformableFbrOrt FbrOrtX

instance Transformable FbrOrtX Typ where tau Struct = Struct

instance Transformable FbrOrtX Type where tau _ = Struct
instance TransformableType FbrOrtX

--------------------------------------------------------------------------------
-- prpFbrOrt -

-- | validity for 'FibredOriented' structures.
prpFbrOrt :: FibredOriented f => XFbrOrt f -> Statement
prpFbrOrt xs = Prp "FbrOrt" :<=>:
  Label "1" :<=>: root .=. orientation where (.=.) = prpEqualExt xs

