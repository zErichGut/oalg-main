
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

import Control.Monad
import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Slice
import OAlg.Entity.Slice.Free

import OAlg.Structure.Oriented

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative

import OAlg.Limes.Definition
import OAlg.Limes.Cone.Definition
import OAlg.Limes.KernelsAndCokernels

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

--------------------------------------------------------------------------------
-- xHomMltAbhSliceFreeAdjunction -

xHomMltAbhSliceToCokernel :: Attestable k
  => Free k AbHom -> XOrtSite To AbHom -> XHomMlt (AbhSliceFreeAdjunction k)
xHomMltAbhSliceToCokernel k xTo = xHomMlt xAppl where
  xAppl = XSomeApplMlt AbhFreeToCokernel (xosXOrtSiteToSliceFactorTo xTo k)

xHomMltAbhCokernelSliceTo :: Attestable k
  => Free k AbHom -> XOrtSite To AbHom -> XHomMlt (AbhSliceFreeAdjunction k)
xHomMltAbhCokernelSliceTo k xTo = xHomMlt xAppl where
  xAppl = XSomeApplMlt AbhFreeFromKernel (xosXOrtSiteFromAbhCokernelFreeToFactor k xTo)
  
xosXOrtSiteFromAbhCokernelFreeToFactor :: Attestable k
  => Free k AbHom -> XOrtSite To AbHom -> XOrtSite To (AbhCokernelFreeToFactor k)
xosXOrtSiteFromAbhCokernelFreeToFactor k xTo = XEnd xToSlice xToFactor where
  XEnd xToP xToM = xosXOrtSiteToSliceFactorTo xTo k
  xToSlice = fmap (pmap AbhFreeToCokernel) xToP
  xToFactor e = do
    f <- xToM $ abhCokernelFreeToSliceTo e
    s <- return $ pmap AbhFreeToCokernel $ start f
    sCoker <- return $ clfCokernel $ abgCftLiftableFree s 
    eDgm <- return $ diagram sCoker
    eCone <- return $ ConeCokernel eDgm (slice $ abgCftSliceFrom e)
    return (AbhCokernelFreeToFactor s e (universalFactor sCoker eCone)) -- valid



qq :: N -> Statement
qq k = case someNatural k of
  SomeNatural k' -> valid $ xosXOrtSiteFromAbhCokernelFreeToFactor (Free k') xStandardOrtSite 

pp :: N -> Statement
pp k = case someNatural k of
  SomeNatural k' -> And [ prpHomMlt (xHomMltAbhSliceToCokernel (Free k') xStandardOrtSite)
                        , prpHomMlt (xHomMltAbhCokernelSliceTo (Free k') xStandardOrtSite)
                        ]

{-
xHomMltAbhSliceFreeAdjunction :: Attestable k
  => XOrtSite To AbHom -> XOrtSite From AbHom -> XHomMlt (AbhSliceFreeAdjunction k)
xHomMltAbhSliceFreeAdjunction xAbhTo xAbhFrom
  = XHomMlt (xPnt k xAbhTo xAbhFrom) (xMlt k xAbhTo xAbhFrom) where
    k = unit1
    xPnt :: Attestable k => Free k AbHom -> XOrtSite To AbHom -> XOrtSite From AbHom
         -> X (SomeApplPnt (AbhSliceFreeAdjunction k))
    xPnt k xAbhTo xAbhFrom = xPntTo k xAbhTo  
  
    xPntTo :: Attestable k => Free k AbHom -> XOrtSite To AbHom
      -> X (SomeApplPnt (AbhSliceFreeAdjunction k))
    xPntTo k xAbhTo = do
      s <- xp
      return (SomeApplPnt AbhFreeToCokernel s)
  
      where XEnd xp _ = xosXOrtSiteToSliceFactorTo xAbhTo k
  
    xMlt :: Attestable k => Free k AbHom -> XOrtSite To AbHom -> XOrtSite From AbHom
         -> X (SomeApplMltp2 (AbhSliceFreeAdjunction k))
    xMlt k xAbhTo xAbhFrom = xMltTo k xAbhTo

    xMltTo :: Attestable k => Free k AbHom -> XOrtSite To AbHom
         -> X (SomeApplMltp2 (AbhSliceFreeAdjunction k))
    xMltTo k xAbhTo = error "nyi"
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
