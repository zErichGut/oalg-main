
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
-- Module      : OAlg.LinearAlgebra.StepForm
-- Description : matrices over fields.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Matrices over fields.
module OAlg.LinearAlgebra.StepForm
  (
  ) where

import Data.List (head,tail,zip)

import OAlg.Prelude

import OAlg.Data.Constructable

import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Ring
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Exponential

import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Sequence.Set

import OAlg.Entity.Product

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Transformation
import OAlg.Entity.Matrix.GeneralLinearGroup


--------------------------------------------------------------------------------
-- rowHeadIndex -

-- | graph of the head indices, i.e. assignment of each row index @i@ the corresponding
-- head index @j@.
--
-- Let @'Col' rws@ be in @'Col' __i__ ('Row' __j x__)@
--
-- pre: for each row @rw@ in @rws@ holds: @rw@ is not empty.
crHeadIndex :: Col i (Row j x) -> Graph i j
crHeadIndex (Col (PSequence xi)) = Graph $ amap1 hij xi where
  hij :: (Row j x,i) -> (i,j)
  hij (Row (PSequence xij),i) = (i,snd $ head xij)

-- | graph of the head indices, i.e. assignment of each row index @i@ the corresponding
-- head index @j@.
--
-- __Note__ If the given matrix is zero, then the resulting graph is empty.
rowHeadIndex :: (i ~ N, j ~ N) => Matrix x -> Graph i j
rowHeadIndex (Matrix _ _ xij) = crHeadIndex $ etscr xij

--------------------------------------------------------------------------------
-- StepGraph -

-- | predicate for a 'Graph' beeing a /step function/.
--
-- __Property__ Let @'StapGraph' s@ be in @'StepGraph' 'N' 'N'@ and let
-- @s = '['(i0,_)..(i,j),(i',j')..']'@ then holds:
--
-- (1) The sequence of the domain indices starts at @0@ and is successive, i.e.
--  @i0 '==' 0@ and @i' '==' i '+' 1@,
--
-- (2) Teh sequence of the range indices are strict increasing, i.e. @j '<' j'@.
newtype StepGraph i j = StepGraph (Graph i j) deriving (Show,Eq)

instance Validable (StepGraph N N) where
  valid (StepGraph (Graph ijs)) = Label "StepGraph" :<=>: vldSGraph 0 ijs where
    vldSGraph _ []          = SValid
    vldSGraph n ((i,j):ijs) = And [ Label "1" :<=>: (n == i) :?> Params ["n":=show n, "i":=show i]
                                  , case ijs of
                                      []        -> SValid
                                      (i',j'):_ -> And [ Label "2" :<=>: (j < j')
                                                           :?> Params [ "i" :=show i
                                                                      , "j" :=show j
                                                                      , "j'":=show j'
                                                                      ]
                                                       , vldSGraph (succ n) ijs
                                                       ]
                                  ]
--------------------------------------------------------------------------------
-- StepMatrix -

-- | predicate for a 'Matrix' beeing in /step form/.
--
-- __Properties__ Let @m@ be in @'StepMatrix' __k__@ for a @'Ring' __k__@, then holds:
--
-- (1) the associated 'stepGraph' is 'valid@.
--
-- (2) For all @i@ in the domain of @s = 'stepGraph' m@ holds:
--
--    (1) @m i (s i) '==' 'rOne'@
--
--    (2) @m i' (s i) '==' 'rZero@ for all @i' '/=' i@,
newtype StepMatrix k = StepMatrix (Matrix k) deriving (Show,Eq)

instance Semiring k => Validable (StepMatrix k) where
  valid m@(StepMatrix m') = Label "StepMatrix" :<=>:
    And [ valid m'
        , Label "1" :<=>: valid $ stepGraph m
        , vldStpRws s' (etscr rws)
        ] where

    s@(StepGraph (Graph s')) = stepGraph m
    Matrix _ _ rws = m'

    vldStpRws [] _ = SValid -- as such, rws is empty, i.e all entries are zero
    vldStpRws ((i,j):ijs) (Col (PSequence rws))
      = And [ Label "2.1" :<=>: (xij == rOne) :?> Params ["(i,j)":=show (i,j),"xij":=show xij]
            , Label "2.2" :<=>: ((j's && js) == empty)
                :?> Params ["(i,j)":=show (i,j),"j's":= show (j's && js)]
                    
            , vldStpRws ijs (Col $ PSequence $ rws')
            ] where
        -- tail and head bellow are well defined, becaus (i,j):jis is not empty and
        -- are given by rowHeadIndex
        Row (PSequence rwi) = fst $ head rws
        xij                 = fst $ head rwi
        rws'                = tail rws
        j's                 = Set $ amap1 snd rwi
        js                  = Set $ amap1 snd ijs                 
        
--------------------------------------------------------------------------------
-- stepGraph -

-- | the associated step graph
stepGraph :: StepMatrix x -> StepGraph N N
stepGraph (StepMatrix m) = StepGraph $ rowHeadIndex m

sf = StepMatrix (matrix (dim () ^ 7) (dim () ^ 5) [(1,0,1),(3,0,2),(1,1,3),(2,1,4)]) :: StepMatrix N
