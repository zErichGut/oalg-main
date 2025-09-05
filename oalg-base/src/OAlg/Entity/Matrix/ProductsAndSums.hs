
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
-- |
-- Module      : OAlg.Entity.Matrix.ProductsAndSums
-- Description : products and sums for matrices
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- 'Products' and 'Sums' for matrices.
module OAlg.Entity.Matrix.ProductsAndSums
  ( -- mtxProducts, mtxSums
  ) where

import Control.Monad

import Data.Foldable
import Data.List (map)

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Variant
import OAlg.Data.Either
import OAlg.Data.HomCo

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented

import OAlg.Entity.FinList
import OAlg.Entity.Diagram
import OAlg.Entity.Sequence.PSequence

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.ProductsAndSums

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Entries

import OAlg.Hom.Definition
import OAlg.Hom.Distributive

--------------------------------------------------------------------------------
-- mtxProducts -

-- | products for matrices.
mtxProducts :: Distributive x => Products n (Matrix x)
mtxProducts = LimitsG prd where
  
  prd :: Distributive x => ProductDiagram n (Matrix x) -> Product n (Matrix x)
  prd d = LimesProjective l u where
    l = lim d
    u = univ

  lim :: Distributive x => ProductDiagram n (Matrix x) -> ProductCone n (Matrix x)
  lim d@(DiagramDiscrete ps)  = ConeProjective d l (prjs 0 l ps) where
    l = mtxJoinDim $ productDim $ toList ps

    prjs :: Distributive x
      => N -> Dim x (Point x) -> FinList n (Dim x (Point x)) -> FinList n (Matrix x)
    prjs _ _ Nil     = Nil
    prjs j l (r:|rs) = prj j l r :| prjs (j+rl) l rs where
      rl = lengthN r

    prj j l r = Matrix r l os where
      os = etsElimZeros $ Entries $ PSequence $ map (\(p,i) -> (one p,(i,i+j))) $ dimxs r

  univ :: Distributive x
    => ProductCone n (Matrix x) -> Matrix x
  univ (ConeProjective _ t cs)
    = mtxJoin $ Matrix rw cl $ etsElimZeros $ Entries $ PSequence $ u 0 cs where
      rw = productDim $ toList $ amap1 end cs
      cl = dim t
      
      u :: Distributive x => N -> FinList n (Matrix x) -> [(Matrix x,(N,N))]
      u _ Nil     = []
      u i (c:|cs) = (c,(i,0)) : u (succ i) cs 


--------------------------------------------------------------------------------
-- mtxSums -

-- | sums for matrices.
mtxSums :: Distributive x => Sums n (Matrix x)
mtxSums = sms where
  Contravariant2 i    = isoCoMatrixOp
  SDualBi (Left1 sms) = amapF (inv2 i) (SDualBi (Right1 mtxProducts))

