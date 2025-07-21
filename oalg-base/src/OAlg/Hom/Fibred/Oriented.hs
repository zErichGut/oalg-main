
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Hom.Fibred.Oriented
-- Description : homomorphisms between fibred oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'FibredOOriented' structures
module OAlg.Hom.Fibred.Oriented
  (
    -- * Fibred Oriented
    HomFibredOriented
  , HomFibredOrientedDisjunctive
  , DualisableFibredOriented, toDualRt
  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.Path

import OAlg.Data.Variant

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented hiding (Path(..))

import OAlg.Hom.Fibred.Definition
import OAlg.Hom.Oriented



