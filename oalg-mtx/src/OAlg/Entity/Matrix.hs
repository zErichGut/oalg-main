
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Entity.Matrix
-- Description : matrices over distributive structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- matrices over 'OAlg.Structure.Distributive.Definition.Distributive' structures
module OAlg.Entity.Matrix
  ( module Def
  , module Dim
  , module Ets
  , module PS
  , module GL
  , module Trf
  , module Prp
  , module Vec
  ) where

import OAlg.Entity.Matrix.Dim as Dim
import OAlg.Entity.Matrix.Entries as Ets
import OAlg.Entity.Matrix.Definition as Def
import OAlg.Entity.Matrix.ProductsAndSums as PS
import OAlg.Entity.Matrix.GeneralLinearGroup as GL
import OAlg.Entity.Matrix.Transformation as Trf
import OAlg.Entity.Matrix.Proposition as Prp
import OAlg.Entity.Matrix.Vector as Vec
