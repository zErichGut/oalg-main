
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Proposition
-- Description : propositions on limits
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions on 'OAlg.Limes.Limits.Limits'.
module OAlg.Limes.Proposition
  (
    prpLimitsOrntSymbol
  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Symbol

import OAlg.Structure.Oriented

import OAlg.Entity.Natural

import OAlg.Limes.TerminalAndInitialPoint
import OAlg.Limes.MinimaAndMaxima
import OAlg.Limes.ProductsAndSums
import OAlg.Limes.EqualizersAndCoequalizers
import OAlg.Limes.PullbacksAndPushouts
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.Deviation

--------------------------------------------------------------------------------
-- prpLimitsOrntSymbol -

-- | validity of 'OAlg.Limes.Limits.Limits' for @'Orientation' 'Symbol'@.
prpLimitsOrntSymbol :: Statement
prpLimitsOrntSymbol = Prp "LimesOrntSymbol" :<=>:
  And [ Label "TerminalAndInitialPoint" :<=>:
          valid (initialPointOrnt :: Symbol -> InitialPoint OS)
      , Label "MinimaAndMaxima" :<=>:
          Exist xN (\(SomeNatural n) -> Label (show n) :<=>:
                     And [ valid (maximaTo' n (Proxy :: Proxy OS))
                         , valid (maximaFrom' n (Proxy :: Proxy OS))
                         ]
                     
                   )

      , Label "ProductsAndSums" :<=>:
          Exist xN (\(SomeNatural n) -> Label (show n) :<=>:
                      valid (sums' n (sumsOrnt I) (sumsOrnt I))
                   )
      , Label "EqualizersAndCoEqualizers" :<=>:
          Exist xN (\(SomeNatural n) -> Label (show n) :<=>:
                      valid (coequalizers' n (sumsOrnt I) (coequalizersOrnt I))
                   )

      , Label "PullbacksAndPushouts" :<=>:
          Exist xN (\(SomeNatural n) -> Label (show n) :<=>:
                      valid (pushouts' n (pushoutsOrnt I))
                   )
      , Label "plbPrdEql2" :<=>: valid (plbPrdEql2 (productsOrnt P) (equalizersOrnt E))    

      , Label "KernelsAndCokernels" :<=>:
          Exist xN (\(SomeNatural n) -> Label (show n) :<=>:
                      valid (cokernels' n (cokernelsOrnt I))
                   )
      , Label "Deviation" :<=>: prpDeviationOrntSymbol
      ]
  where xN = xOneOf $ takeN 20 naturals


