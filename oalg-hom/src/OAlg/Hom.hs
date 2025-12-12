
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Hom
-- Description : homomorphisms between algebraic structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between algebraic structures.
module OAlg.Hom
  (
    module Def
  , module Ort
  , module Mlt
  , module Fbr
  , module Add
  , module Dst
  , module Vec
  , module Alg
  )
  where

import OAlg.Hom.Definition as Def
import OAlg.Hom.Oriented as Ort
import OAlg.Hom.Multiplicative as Mlt
import OAlg.Hom.Fibred as Fbr
import OAlg.Hom.Additive as Add
import OAlg.Hom.Distributive as Dst
import OAlg.Hom.Vectorial as Vec
import OAlg.Hom.Algebraic as Alg

