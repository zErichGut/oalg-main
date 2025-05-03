

{-# LANGUAGE GADTs, TypeFamilies, StandaloneDeriving, TypeOperators #-}

-- |
-- Module      : OAlg.Prelude
-- Description : the prelude
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- To avoid ambiguity for the algebraic operators on should /exclude/  the standard "Prelude" and
-- use this one instead.
module OAlg.Prelude
  ( 
    -- * Category
    module App
  , module Cat
  , module Prp

    -- * Validating
  , module Stm
  , module X
  , module Vlb
  , module Vld

    -- * Data
  , module Lgc
  , module Bol
  , module Eql
  , module EqlExt
  , module Myb
  , module Shw
  , module Nmb

    -- * Entity
  , module Ent

    -- * Structure
  , module Str
  
    -- * Dual
  , module Dlb
  , module SDlb
  , module Op

    -- * Ord
  , module Ord

    -- * Additionals
    -- | Some additional definition from the standard "Prelude".

    -- ** Type Equality
  , type (~)

    -- ** Bounded
  , Bounded(..)

    -- ** IO
  , IO, putStrLn

    -- ** seq
  , seq

    -- ** Undefined
  , undefined, error
  
    -- * Exception
  , module Exc
  )

  where

import Prelude( Bounded(..)
              , seq
              , undefined, error
              )

import Data.Type.Equality (type (~))
import System.IO (IO,putStrLn)

import OAlg.Control.Exception as Exc
import OAlg.Category.Applicative as App
import OAlg.Category.Definition as Cat
import OAlg.Category.Proposition as Prp

import OAlg.Control.Validate as Vld

import OAlg.Data.Logical as Lgc
import OAlg.Data.Statement as Stm
import OAlg.Data.X as X
import OAlg.Data.Validable as Vlb
import OAlg.Data.Boolean as Bol
import OAlg.Data.Equal as Eql
import OAlg.Data.EqualExtensional as EqlExt
import OAlg.Data.Maybe as Myb
import OAlg.Data.Show as Shw
import OAlg.Data.Number as Nmb
import OAlg.Data.Dualisable as Dlb
import OAlg.Data.SDualisable as SDlb
import OAlg.Data.Opposite as Op
import OAlg.Data.Ord as Ord

import OAlg.Entity.Definition as Ent
import OAlg.Structure.Definition as Str

