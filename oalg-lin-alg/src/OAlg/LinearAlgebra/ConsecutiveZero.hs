
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
-- Module      : OAlg.LinearAlgebra.ConsecutiveZero
-- Description : representation for consecutive zeros.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Representation for consecutive zeros.
module OAlg.LinearAlgebra.ConsecutiveZero
  (
  ) where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Distributive
import OAlg.Structure.Ring

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Transformation

import OAlg.LinearAlgebra.StepMatrix

--------------------------------------------------------------------------------
-- Diagonalizable -

-- | predicate for diagonalisable matrices over a @'Distributive' __k__@@.
--
-- __Property__ Let @dg@ be in @'Diagonalizable' __k__@ for a @'Distributive' __k__@, then holds:
--
-- (1) @m '==' 'dgfMatrix' d@ for all @m@ in @'Matrix' __k__@, where @d = 'diagonalForm' dg m@.
newtype Diagonalizable k = Diagonalizable (Matrix k -> DiagonalForm k)

--------------------------------------------------------------------------------
-- prpDiagonalizable -

relDiagonalizable :: Distributive k => Diagonalizable k -> Matrix k -> Statement
relDiagonalizable dg m = (m == dgfMatrix d) :?> Params ["m":=show m]
  where d = diagonalForm dg m

-- | validity according to t'DiagonalForm'.
prpDiagonalizable :: Distributive k => Diagonalizable k -> X (Matrix k) -> Statement
prpDiagonalizable dg xm = Prp "Diagonalizable" :<=>: Forall xm (relDiagonalizable dg)
  
instance (Distributive k, XStandardOrtOrientation k) => Validable (Diagonalizable k) where
  valid dg = prpDiagonalizable dg (xoOrt xStandardOrtOrientation) 
  
--------------------------------------------------------------------------------
-- diagonalForm -

-- | the associated diagonal form.
diagonalForm :: Diagonalizable k -> Matrix k -> DiagonalForm k
diagonalForm (Diagonalizable d) = d

--------------------------------------------------------------------------------
-- dgzField -

-- | diagonalizables for a @'Field' __k__@.
dgzField :: Field k => Diagonalizable k
dgzField = Diagonalizable mtxDiagonalForm

