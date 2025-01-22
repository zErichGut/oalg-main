
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.Zeros
-- Description : chain diagrams with consecutive zero-able arrows. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Chain diagrams with consecutive zero-able arrows. 
module OAlg.Limes.Exact.Zeros
  ( -- * Zeros
    Zeros(..), zrsDiagram, zrsPoints, zrsArrows

    -- ** Duality
  , coZeros

    -- * Transformation
  , ZerosTrafo(..)

    -- ** Duality
  , coZerosTrafo
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList

--------------------------------------------------------------------------------
-- Zeros -

-- | chain diagrams with consecutive zero-able arrows.
--
-- __Properties__ Let @'Zero' c@ be in @'Zero' __t__ __n__ __d__@ for a 'Distributive' structure
-- @__d__@, then holds:
--
-- (1) If @c@ matches @'DiagramChainTo' _ ds@ then holds:
-- @d '*' d'@ is 'zero' for all @..d':|'d'..@ in @ds@.
--
-- (2) If @c@ matches @'DiagramChainFrom' _ ds@ then holds:
-- @d' '*' d@ is 'zero' for all @..d':|'d'..@ in @ds@.
newtype Zeros t n d = Zeros (Diagram (Chain t) (n+3) (n+2) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Zeros - Duality -

type instance Dual (Zeros t n d) = Zeros (Dual t) n (Op d)

reflDualChain :: Zeros t n d -> Dual (Chain t) :~: Chain (Dual t)
reflDualChain (Zeros d) = case d of
  DiagramChainTo _ _   -> Refl
  DiagramChainFrom _ _ -> Refl

-- | the dual 'Zeros'
coZeros :: Zeros t n d -> Dual (Zeros t n d)
coZeros c@(Zeros d) = case reflDualChain c of
  Refl -> Zeros (coDiagram d)

--------------------------------------------------------------------------------
-- Zeros - Entity -

vldZerosTo :: Distributive d => Zeros To n d -> Statement
vldZerosTo (Zeros (DiagramChainTo e (d:|ds)))
  = And [ valid d
        , Label "e == end d" :<=>: (e == end d) :?> Params ["e":=show e, "d":=show d]
        , vldZrs 0 d ds
        ] where
  
  vldZrs :: Distributive d => N -> d -> FinList n d -> Statement
  vldZrs _ _ Nil      = SValid
  vldZrs i d (d':|ds) = And [ valid d'
                            , Label "start d == end d'"
                                :<=>: (start d == end d') :?> Params ["i":=show i]
                            , Label "1" :<=>: isZero (d*d') :?> Params ["i":=show i]
                            , vldZrs (succ i) d' ds
                            ]

instance Distributive d => Validable (Zeros t n d) where
  valid c@(Zeros d) = Label "Zeros" :<=>:
    case d of
      DiagramChainTo _ _   -> vldZerosTo c
      DiagramChainFrom _ _ -> vldZerosTo $ coZeros c

instance (Distributive d, Typeable t, Typeable n) => Entity (Zeros t n d)

--------------------------------------------------------------------------------
-- zrsDiagram -

-- | the underlying 'Diagram'.
zrsDiagram :: Zeros t n d -> Diagram (Chain t) (n+3) (n+2) d
zrsDiagram (Zeros d) = d

--------------------------------------------------------------------------------
-- zrsPoints -

-- | the points of the underlying 'Diagram'.
zrsPoints :: Oriented d => Zeros t n d -> FinList (n+3) (Point d)
zrsPoints = dgPoints . zrsDiagram

--------------------------------------------------------------------------------
-- zrsArrows -

-- | the arrows of the underlying 'Diagram'.
zrsArrows :: Zeros t n d -> FinList (n+2) d
zrsArrows = dgArrows . zrsDiagram

--------------------------------------------------------------------------------
-- zrsHead -

-- zrsHead :: Oriented d => Zeros t n d -> Zeros t N0 d
-- zrsHead (Zeros (DiagramChainTo _ (a:|a':|_))) = Zeros (DiagramChainTo (end a) (a:|a':|Nil))

--------------------------------------------------------------------------------
-- ZerosTrafo -

-- | transformation between two 'Zeros'.
--
-- __Properties__ Let @t = 'ZeroTrafo' a b fs@ be in @'ZerosTrafo' __t__ __n__ __d__@ for a
-- 'Distributive' structure, then holds:
--
-- (1) If @a@ matches @'Zeros' ('DiagramChainTo' _ as)@, then holds:
-- @f '*' a '==' b '*' f'@ for all @f@, @a@ and @b@ in
--
-- @
--                a       
--  as: ...    <------ <------   ...
--            |       |       |
--  fs: ... f |     f'|       |  ...
--            v       v       v
--  bs: ...    <------ <------   ... 
--                b       
-- @
--
-- (2) If @a@ matches @'Zeros' ('DiagramChainFrom' _ as)@, then holds:
-- @f' '*' a '==' b '*' f@ for all @f@, @a@ and @b@ in
--
-- @
--                a       
--  as: ...    ------> ------>   ...
--            |       |       |
--  fs: ... f |     f'|       |  ...
--            v       v       v
--  bs: ...    ------> ------>   ... 
--                b       
-- @
data ZerosTrafo t n d = ZerosTrafo (Zeros t n d) (Zeros t n d) (FinList (n+3) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- zrtTransformation -

-- | the underlying 'Transformation'.
zrtTransformation :: ZerosTrafo t n d -> Transformation (Chain t) (n+3) (n+2) d
zrtTransformation (ZerosTrafo a b fs) = Transformation (zrsDiagram a) (zrsDiagram b) fs

--------------------------------------------------------------------------------
-- coZerosTrafo - Duality -

type instance Dual (ZerosTrafo t n d) = ZerosTrafo (Dual t) n (Op d)

-- | the dual 'ZerosTrafo'.
coZerosTrafo :: ZerosTrafo t n d -> Dual (ZerosTrafo t n d)
coZerosTrafo (ZerosTrafo a b fs) = ZerosTrafo (coZeros b) (coZeros a) (amap1 Op fs)

--------------------------------------------------------------------------------
-- vldZerosTrafoTo - Entity -

vldZerosTrafoTo :: Distributive d => ZerosTrafo To n d -> Statement
vldZerosTrafoTo (ZerosTrafo a@(Zeros (DiagramChainTo _ as)) b@(Zeros (DiagramChainTo _ bs)) (f:|fs))
  = And [ valid a
        , valid b
        , valid f
        , vldTrfs 0 f fs as bs 
        ] where

  vldTrfs :: Distributive d => N -> d -> FinList n d -> FinList n d -> FinList n d -> Statement
  vldTrfs _ _ Nil Nil Nil = SValid
  vldTrfs i f (f':|fs) (a:|as) (b:|bs)
    = And [ valid f'
          , Label "f * a" :<=>: (end a == start f) :?> Params ["i":=show i]
          , Label "b * f'" :<=>: (end f' == start b) :?> Params ["i":=show i]
          , Label "1" :<=>: (f * a == b * f') :?> Params ["i":=show i]
          , vldTrfs (succ i) f' fs as bs
          ]

instance Distributive d => Validable (ZerosTrafo t n d) where
  valid t@(ZerosTrafo a _ _) = Label "ZerosTrafo" :<=>: case a of
    Zeros (DiagramChainTo _ _)   -> vldZerosTrafoTo t
    Zeros (DiagramChainFrom _ _) -> vldZerosTrafoTo $ coZerosTrafo t

instance (Distributive d, Typeable t, Typeable n) => Entity (ZerosTrafo t n d)

--------------------------------------------------------------------------------
-- ZerosTrafo - Oriented -

instance (Distributive d, Typeable t, Typeable n) => Oriented (ZerosTrafo t n d) where
  type Point (ZerosTrafo t n d) = Zeros t n d
  orientation (ZerosTrafo a b _) = a :> b
