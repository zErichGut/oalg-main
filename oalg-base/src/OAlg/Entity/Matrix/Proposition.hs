{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Matrix.Proposition
-- Description : propositions on matrices
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on matrices.
module OAlg.Entity.Matrix.Proposition
  (
    -- * Proposition
    prpMatrix, prpMatrixZ
    
  ) where

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Distributive
import OAlg.Structure.Algebraic

import OAlg.Limes.ProductsAndSums

import OAlg.Entity.Natural

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.ProductsAndSums

--------------------------------------------------------------------------------
-- prpMatrix -

-- | validity of the algebraic structure of matrices.
prpMatrix :: Distributive x
  => XOrtOrientation (Matrix x)
  -> XOrtSite From (Matrix x)
  -> XOrtSite To (Matrix x)
  -> Statement
prpMatrix xo xf xt = Prp "Matrix" :<=>:
  And [ prpOrt (xoOrt xo)
      , prpMlt (xoMlt (xNB 0 10) xo)
      , prpFbr (xoFbr xo)
      , prpFbrOrt (xoFbrOrt xo)
      , prpAdd (xoAdd (xNB 0 5) xo)
      , prpDst (xoDst xo xf xt)
      ]


dstMatrix :: Int -> X (Matrix x) -> IO ()
dstMatrix = putDstr (\m -> [rws m,cls m]) where
  rws (Matrix r _ _) = show $ lengthN r
  cls (Matrix _ c _) = show $ lengthN c


--------------------------------------------------------------------------------
-- prpMatrixZ -

-- | validity of the algebraic structure of block matrices of 'Z'.
prpMatrixZ :: Statement
prpMatrixZ = Prp "MatrixZ"
  :<=>: And [ prpMatrix xo xf xt
            , prpAbl (xoAbl (xZB (-10) 10) xo)            
            , prpVec (xoVec xZ xo)
            , prpAlg (xoAlg xZ xf)
            , Label "Sums N3 (Matrix Z)" 
                 :<=>: valid (mtxSums :: Sums N3 (Matrix Z))
            ]
  where xo = xodZZ
        xf = xoFrom xo
        xt = xoTo xo

