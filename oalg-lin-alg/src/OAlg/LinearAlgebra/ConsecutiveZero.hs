
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

import Control.Monad (join)
import qualified Data.List as L (zip)

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Ring

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Transformation
import OAlg.Entity.Matrix.GeneralLinearGroup

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

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

--------------------------------------------------------------------------------
-- isoChainDiagFst -

-- | isomorphism from the given chain diagram to a chain diagram with first matrix a diagonal matrix
-- with non zero entries.
isoChainDiagFst :: Distributive k
  => Diagonalizable k -> Diagram (Chain t) (n+1) n (Matrix k)
  -> Inv (DiagramTrafo (Chain t) (n+1) n (Matrix k))
isoChainDiagFst dgz a@(DiagramChainTo _ chs) = case chs of
  Nil     -> one a
  m:|chs' -> Inv t f where
    
    a' = DiagramChainTo (start m) chs'
    b  = DiagramChainTo (end d_) (d_ :| rpFst c' chs')
    os = tail $ amap1 one $ dgPoints a'
    t  = DiagramTrafo a b (r:|c':|os)
    f  = DiagramTrafo b a (r':|c:|os) 

    -- r * m = d_ * c'
    DiagonalForm d (RowTrafo rt) (ColTrafo ct) = diagonalForm dgz m  
    Inv r r' = amap GLTGL rt
    Inv c c' = amap GLTGL ct
    d_       = diagonal (end m) (start m) d
    
    -- replaces the firts entry with the multiplication from the left by the given one.
    rpFst :: Multiplicative x => x -> FinList n x -> FinList n x
    rpFst _ Nil     = Nil
    rpFst l (x:|xs) = (l*x):|xs

isoChainDiagFts dgz a@(DiagramChainFrom _ _) = error "nyi"

{-
    chs'' = case chs' of
      Nil   -> Nil
      _:|cs -> c':|cs 
-}

mt :: (Ring r, i ~ N, j ~ N) => N -> N -> [([(r,j)],i)] -> Matrix r
mt r c xijs = matrixTtl r c xijs' where
  xijs' = join $ amap1 (\(xjs,i) -> amap1 (\(x,j) -> (x,i,j)) xjs) xijs

m :: Matrix Q
m = mt 4 6 ([ [2,4,6,0,2  ] `L.zip` [1..]
            , [1,2,3,3,0.5] `L.zip` [1..]
            , [3,6,7,1,2  ] `L.zip` [1..]
            , [1,2,5,3,4/3] `L.zip` [1..]
            ] `L.zip` [0..]
           )

d = DiagramChainTo (end m) (m:|Nil)
