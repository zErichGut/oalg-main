
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
prpLimitsOrntSymbol :: N -> Statement
prpLimitsOrntSymbol n' = Prp "LimesOrntSymbol" :<=>: Label (show n') :<=>:
  case someNatural n' of
    SomeNatural n
      -> And [ Label "TerminalAndInitialPoint" :<=>:
               valid (initialPointOrnt :: Symbol -> InitialPoint OS)
                  
             , Label "MinimaAndMaxima" :<=>:
                 And [ valid (maximaTo' n (Proxy :: Proxy OS))
                     , valid (maximaFrom' n (Proxy :: Proxy OS))
                     ]

             , Label "ProductsAndSums" :<=>:
                 valid (sums' n (sumsOrnt I) (sumsOrnt I))
                      
             , Label "EqualizersAndCoEqualizers" :<=>:
                 valid (coequalizers' n (sumsOrnt I) (coequalizersOrnt I))


             , Label "PullbacksAndPushouts" :<=>:
                 valid (pushouts' n (pushoutsOrnt I))

             , Label "plbPrdEql2" :<=>:
                 valid (plbPrdEql2 (productsOrnt P) (equalizersOrnt E))    


             , Label "KernelsAndCokernels" :<=>:
                 valid (cokernels' n (cokernelsOrnt I))

             , Label "Deviation" :<=>: prpDeviationOrntSymbol
             ]



