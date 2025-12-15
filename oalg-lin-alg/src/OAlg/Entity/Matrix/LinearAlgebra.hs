
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
-- Module      : OAlg.Entity.Matrix.LinearAlgebra
-- Description : matrices over fields.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Matrices over fields.
module OAlg.Entity.Matrix.LinearAlgebra
  (
  ) where


import OAlg.Prelude

import OAlg.Structure.Ring

import OAlg.Entity.Product
import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.GeneralLinearGroup


--------------------------------------------------------------------------------
-- StepForm -

-- | predicate for a matrix over a 'Ring' beeing in step form.
--
--
-- __Properties__ Let @'StepForm' js m@ be in @t'StepForm' __k__@ for a @t'Ring' __k__@, then
-- for all @(i,j)@ in @[0..] `zip` js@ holds:
--
-- (1) @m(i,j) '==' 'rOne'@.
--
-- (2) @m(i',j) '==' 'rZero'@ for all @i' '<' i@,
--
-- (3) @m(i',j') '==' 'rZero'@ for all @i' '>=' i@ and @j' '<=' j@ and @(i',j') '/=' (i,j)@,
--
-- (4) @m(i',_) '==' 'rZero'@ for all @i' '>' r@.
--
-- @
--           j0      j1  ..  j ..   jr   
--  0  [      1 *..*    *..*   *..*    *..* ]
--  1  [              1 *..*   *..*    *..* ]
--     [                                    ]
--  i  [                     1 *..*    *..* ]
--     [                                    ]
--  r  [                             1 *..* ]
--     [                                    ]
--  
-- @
data StepForm k = StepForm [N] (Matrix k) 

{-
--------------------------------------------------------------------------------
-- stepF -

type TPRows k = ProductForm Z (Transformation k)
type TPCols k = ProductForm Z (Transformation k)
type StepF i j k  = (Col i (Row j k), TPRows k) 

{-
-- | transforming to sep form
stepF :: Field k => (i ~ N, j ~ N) => Dim k () -> Dim k () -> i -> StepF i j k -> StepF i j k
stepF n m i cr@(rws,_) = if colIsEmpty rws
  then cr
  else stepF1 n m i i cr

-- pre: colIsEmpty rws is False.
stepF1 :: Filed k => (i ~ N, j ~ N) => Dim k () -> Dim k () -> i -> i -> StepF i j k -> StepF i j k
stepF1 n m i i' (rws,tr) = error "nyi"
-}

--------------------------------------------------------------------------------
-- stepForm -

stepForm :: Field k => Matrix k -> StepF N N k
stepForm (Matrix r c xs) = error "nyi"
-}
