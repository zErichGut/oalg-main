
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.LinearAlgebra.KernelsAndCokernels
-- Description : kernels and cokernels.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Kernels and cokernels for matrices over a field.
module OAlg.LinearAlgebra.KernelsAndCokernels
  (
  ) where

import Control.Monad (join)
import Data.List (head,tail,zip,foldl,foldr,span)

import OAlg.Prelude

import OAlg.Data.Constructable
import OAlg.Data.Canonical

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Ring
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Exponential
import OAlg.Structure.Operational

import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Permutation

import OAlg.Entity.Product

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Transformation
import OAlg.Entity.Matrix.GeneralLinearGroup


