
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

-- | Propositions about the algerbaic structure of types.
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

{-
--------------------------------------------------------------------------------
-- prpLimitsToProjectiveSomeDiagram -

prpLimitsToProjectiveSomeDiagram :: Multiplicative a
  => XStandardOrtSite To a
  => Products N0 a -> Products N2 a
  -> SomeDiagram a -> Statement
prpLimitsToProjectiveSomeDiagram prd0 prd2 (SomeDiagram d)
  = Prp "LimitsToProjectiveSomeDiagram" :<=>: case d of
    DiagramDiscrete _     -> prpLimitsProduct
                               xStandardEligibleFactor
                               (products prd0 prd2) d
    DiagramChainTo _ _    -> prpLimitsMinimum xStandardEligibleFactor minimaTo d
--    DiagramChainFrom _ _  -> prpLimitsMinimum xStandardEligibleFactor minimaFrom d
    _                     -> PTrue
-}

--------------------------------------------------------------------------------
-- prpLimitsOrntSymbol -

-- | validity of limits for @'Orientation' 'Symbole'@.
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
      ]
  where xN = xOneOf $ takeN 20 naturals


