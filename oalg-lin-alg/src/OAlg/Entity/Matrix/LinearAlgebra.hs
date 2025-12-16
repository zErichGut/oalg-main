
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

import Data.List (zip)

import OAlg.Prelude

import OAlg.Structure.Ring
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Exponential

import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.Set

import OAlg.Entity.Product
import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Transformation
import OAlg.Entity.Matrix.GeneralLinearGroup


--------------------------------------------------------------------------------
-- StepForm -

-- | predicate for a matrix over a 'Ring' beeing in step form.
--
--
-- __Properties__ Let @'StepForm' ('Set' js) m@ be in @t'StepForm' __k__@ for a @t'Ring' __k__@, then
-- for all @(i,j)@ in @[0..] `zip` js@ holds:
--
-- (1) @m(i,j) '==' 'rOne'@.
--
-- (2) @m(i,j') '==' 'rZero'@ for all @j' '<' j@,
--
-- (3) @m(i',j) '==' 'rZero'@ for all @i' '<' i@.
--
-- (4) @m(i',j') '==' 'rZero'@ for all @i' > r@.
--
--
-- @
--           j0      j1  ..  j ..   jr   
--  0  [      1 *..*    *..*   *..*    *..* ]
--  1  [              1 *..*   *..*    *..* ]
--  .  [                                    ]
--  .  [                                    ]
--  i  [                     1 *..*    *..* ]
--  .  [                                    ]
--  .  [                                    ]
--  r  [                             1 *..* ]
--     [                                    ]
--  
-- @
data StepForm r = StepForm (Set N) (Matrix r) deriving (Show,Eq)

instance Ring r => Validable (StepForm r) where
  valid (StepForm sjs@(Set js) m@(Matrix rs cs xs)) = Label "StepFrom" :<=>:
    And [ valid sjs
        , valid m
        , vldSteps ([0..] `zip` js) (etscr xs)
        ]

    where
      vldSteps [] crs        = Label "4" :<=>: colIsEmpty crs :?> Params ["crs":=show crs]
      vldSteps (ij:ijs) crs  = case crs of
        Col (PSequence [])  -> Label "1" :<=>: Label "empty col" :<=>: False :?> Params prms where
                                 prms = ["(i,j)":= show ij,"crs":=show crs]
        _                   -> And [ vldStep ij (amap1 snd ijs) (colHead crs)
                                   , vldSteps ijs (colTail crs)
                                   ]

      vldStep (i,j) js (rw,i') = case rw of
        Row (PSequence [])    -> Label "1" :<=>: Label "empty row" :<=>: False :?> Params prms where
                                   prms = ["(i,j)":=show (i,j)]
        _                     -> case rowHead rw of
          (x,j')              -> And [ Label "2" :<=>: (j <= j') :?> Params ["j'":=show j']
                                     , Label "1" :<=>: ((i,j) == (i',j')) :?>
                                         Params ["(i,j)":=show (i,j), "(i',j')":=show (i',j')]
                                     , Label "1" :<=>: (x == rOne) :?> Params ["x":=show x]
                                     , Label "3" :<=>:
                                         let supp = Set $ amap1 snd $ rowxs rw
                                             nz   = supp && Set js
                                          in (nz == empty) :?> Params ["nz":=show nz] 
                                     ]

sf = StepForm (set [3,1]) (matrix (dim () ^ 3) (dim () ^ 4) [(1,0,1),(1,1,3)]) :: StepForm Z 


--------------------------------------------------------------------------------
-- stepForm -

-- | transforming a matrix to step form.
--
-- __Properties__ Let @m@ be in @'Matrix' __k__@ for a @'Field' __k__@ and
-- @('StepForm' _ m',t) = 'stepForm' m@, then holds:
--
-- (1) @t '*>' m '==' m'@.
stepForm :: Field k => Matrix k -> (StepForm k, RowTrafo k)
stepForm m = error "nyi"


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
