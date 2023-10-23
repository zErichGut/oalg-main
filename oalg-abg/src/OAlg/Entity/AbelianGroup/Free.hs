
-- |
-- Module      : OAlg.Entity.AbelianGroup.Free
-- Description : homomorphisms between free abelian groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between free abelian groups which are represented by t'OAlg.Data.Number.Z'-matrices.
module OAlg.Entity.AbelianGroup.Free
  ( module SNF
  , module Lim
  ) where

import OAlg.Entity.AbelianGroup.Free.SmithNormalForm as SNF
import OAlg.Entity.AbelianGroup.Free.Limes as Lim
