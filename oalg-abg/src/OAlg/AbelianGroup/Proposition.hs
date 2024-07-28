
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.AbelianGroup.Proposition
-- Description : validity of abelian groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- validity of abelian groups.
module OAlg.AbelianGroup.Proposition
  ( prpAbelianGroups, prpAbhCokernelLftFree
  ) where

import Prelude (ceiling)

import Data.Foldable
import Data.List

import Control.Monad
import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Singleton

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Slice
import OAlg.Entity.Slice.Free
import OAlg.Entity.Matrix.Definition

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative

import OAlg.Limes.Definition
import OAlg.Limes.Cone.Definition
import OAlg.Limes.KernelsAndCokernels

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels
import OAlg.AbelianGroup.ZMod

--------------------------------------------------------------------------------
-- xHomMltAbhSliceFreeAdjunction -

xHomMltAbhSliceToCokernel :: Attestable k
  => Free k AbHom -> XOrtSite To AbHom -> XHomMlt (AbhSliceFreeAdjunction k)
xHomMltAbhSliceToCokernel k xTo = xHomMlt xAppl where
  xAppl = XSomeApplMlt AbhFreeToCokernel (xosXOrtSiteToSliceFactorTo xTo k)

xHomMltAbhCokernelSliceTo :: Attestable k
  => Free k AbHom -> XOrtSite To AbHom -> XHomMlt (AbhSliceFreeAdjunction k)
xHomMltAbhCokernelSliceTo k xTo = xHomMlt xAppl where
  xAppl = XSomeApplMlt AbhFreeFromKernel (xosAbhCokerneFreeToFactor k xSliceTo)
  xSliceTo = xosAdjTerminal (1%100) $ xosXOrtSiteToSliceFactorTo xTo k


{-
qq :: N -> Statement
qq k = case someNatural k of
  SomeNatural k' -> valid $ xosXOrtSiteFromAbhCokernelFreeToFactor (Free k') xStandardOrtSite 
-}

pp :: N -> Statement
pp k = case someNatural k of
  SomeNatural k' -> And [ prpHomMlt (xHomMltAbhSliceToCokernel (Free k') xStandardOrtSite)
                        , prpHomMlt (xHomMltAbhCokernelSliceTo (Free k') xStandardOrtSite)
                        ]

rr :: N -> Statement
rr k = case someNatural k of
  SomeNatural k' -> valid $ xosAbhCokerneFreeToFactor (Free k') xStandardOrtSite 

dst1 :: N -> Int -> XOrtSite To AbHom -> IO ()
dst1 k n xTo = case someNatural k of
  SomeNatural k' -> putDstr shw n xShw where
    xShw = xosPoint $ xosXOrtSiteToSliceFactorTo xTo (Free k')
    -- shw = return . show . length . filter isFree . toList . (\(AbGroup g) -> g) . start . slice
    shw = return . show . abhDensity 5 . slice
    isFree (ZMod n) = True -- n == 0

dst2 :: N -> Int -> XOrtSite To AbHom -> IO ()
dst2 k n xTo = case someNatural k of
  SomeNatural k' -> putDstr shw n xShw where
    xShw = xosOrt $ xosXOrtSiteToSliceFactorTo xTo (Free k')
    shw = return . show . abhDensity 5 . slfDrop

{-
dst3 :: N -> Int -> XOrtSite To AbHom -> IO ()
dst3 k n xTo = case someNatural k of
  SomeNatural k' -> putDstr shw n xShw where
    xShw = xosPoint $ xosXOrtSiteFromAbhCokernelFreeToFactor (Free k') xTo 
    shw = return . show . end . slice . abgCftSliceFrom
    isFree (ZMod n) = True -- n == 0

dst4 :: N -> Int -> XOrtSite To AbHom -> IO ()
dst4 k n xTo = case someNatural k of
  SomeNatural k' -> putDstr shw n xShw where
    xShw = xosOrt $ xosXOrtSiteFromAbhCokernelFreeToFactor (Free k') xTo 
    shw = return . show . abhDensity 17 . slfDrop . abgCftSliceFromFactor
-}
--------------------------------------------------------------------------------
-- prpAbhCokernelLftFree -

-- | validity of 'abhCokernelLftFree' for a given cokernel diagram @h@.
prpAbhCokernelLftFree :: CokernelDiagram N1 AbHom -> Statement
prpAbhCokernelLftFree h = Prp "AbhCokernelLftFree" :<=>:
  And [ valid c
      , Label "1" :<=>: (h == (diagram $ clfCokernel c)) :?> Params ["h":=show h]
      , Label "2" :<=>: (isSmithNormal $ tip $ universalCone $ clfCokernel c)
          :?> Params ["h":=show h]
      
      ]
  where c = abhCokernelLftFree h

-- | validity for abelian groups.
prpAbelianGroups :: Statement
prpAbelianGroups = Prp "AbelianGroups"
  :<=>: And [ prpAbHom
            , Label "isoSmithNormal" :<=>: Forall xStandard (valid . isoSmithNormal)
            , Label "kernels" :<=>: valid abhKernels
            , Label "cokernels liftable" :<=>: Forall xStandard prpAbhCokernelLftFree
            , Label "abhFreeAdjunction" :<=>: valid abhFreeAdjunction
            ]
