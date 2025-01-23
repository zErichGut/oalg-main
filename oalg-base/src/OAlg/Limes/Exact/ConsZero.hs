
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.ConsZero
-- Description : chain diagrams with consecutive zero-able arrows. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Chain diagrams with consecutive zero-able arrows. 
module OAlg.Limes.Exact.ConsZero
  ( -- * Consecutive Zero
    ConsZero(..), zrsDiagram, zrsPoints, zrsArrows

    -- ** Duality
  , coConsZero

    -- * Transformation
  , ConsZeroTrafo(..)

    -- ** Duality
  , coConsZeroTrafo
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
-- ConsZero -

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
newtype ConsZero t n d = ConsZero (Diagram (Chain t) (n+3) (n+2) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ConsZero - Duality -

type instance Dual (ConsZero t n d) = ConsZero (Dual t) n (Op d)

reflDualChain :: ConsZero t n d -> Dual (Chain t) :~: Chain (Dual t)
reflDualChain (ConsZero d) = case d of
  DiagramChainTo _ _   -> Refl
  DiagramChainFrom _ _ -> Refl

-- | the dual 'ConsZero'
coConsZero :: ConsZero t n d -> Dual (ConsZero t n d)
coConsZero c@(ConsZero d) = case reflDualChain c of
  Refl -> ConsZero (coDiagram d)

--------------------------------------------------------------------------------
-- ConsZero - Entity -

vldConsZeroTo :: Distributive d => ConsZero To n d -> Statement
vldConsZeroTo (ConsZero (DiagramChainTo e (d:|ds)))
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

instance Distributive d => Validable (ConsZero t n d) where
  valid c@(ConsZero d) = Label "ConsZero" :<=>:
    case d of
      DiagramChainTo _ _   -> vldConsZeroTo c
      DiagramChainFrom _ _ -> vldConsZeroTo $ coConsZero c

instance (Distributive d, Typeable t, Typeable n) => Entity (ConsZero t n d)

--------------------------------------------------------------------------------
-- zrsDiagram -

-- | the underlying 'Diagram'.
zrsDiagram :: ConsZero t n d -> Diagram (Chain t) (n+3) (n+2) d
zrsDiagram (ConsZero d) = d

--------------------------------------------------------------------------------
-- zrsPoints -

-- | the points of the underlying 'Diagram'.
zrsPoints :: Oriented d => ConsZero t n d -> FinList (n+3) (Point d)
zrsPoints = dgPoints . zrsDiagram

--------------------------------------------------------------------------------
-- zrsArrows -

-- | the arrows of the underlying 'Diagram'.
zrsArrows :: ConsZero t n d -> FinList (n+2) d
zrsArrows = dgArrows . zrsDiagram

--------------------------------------------------------------------------------
-- zrsHead -

-- zrsHead :: Oriented d => ConsZero t n d -> ConsZero t N0 d
-- zrsHead (ConsZero (DiagramChainTo _ (a:|a':|_))) = ConsZero (DiagramChainTo (end a) (a:|a':|Nil))

--------------------------------------------------------------------------------
-- ConsZeroTrafo -

-- | transformation between two 'ConsZero'.
--
-- __Properties__ Let @t = 'ZeroTrafo' a b fs@ be in @'ConsZeroTrafo' __t__ __n__ __d__@ for a
-- 'Distributive' structure, then holds:
--
-- (1) If @a@ matches @'ConsZero' ('DiagramChainTo' _ as)@, then holds:
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
-- (2) If @a@ matches @'ConsZero' ('DiagramChainFrom' _ as)@, then holds:
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
data ConsZeroTrafo t n d = ConsZeroTrafo (ConsZero t n d) (ConsZero t n d) (FinList (n+3) d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- zrtTransformation -

-- | the underlying 'Transformation'.
zrtTransformation :: ConsZeroTrafo t n d -> Transformation (Chain t) (n+3) (n+2) d
zrtTransformation (ConsZeroTrafo a b fs) = Transformation (zrsDiagram a) (zrsDiagram b) fs

--------------------------------------------------------------------------------
-- coConsZeroTrafo - Duality -

type instance Dual (ConsZeroTrafo t n d) = ConsZeroTrafo (Dual t) n (Op d)

-- | the dual 'ConsZeroTrafo'.
coConsZeroTrafo :: ConsZeroTrafo t n d -> Dual (ConsZeroTrafo t n d)
coConsZeroTrafo (ConsZeroTrafo a b fs) = ConsZeroTrafo (coConsZero b) (coConsZero a) (amap1 Op fs)

--------------------------------------------------------------------------------
-- vldConsZeroTrafoTo - Entity -

vldConsZeroTrafoTo :: Distributive d => ConsZeroTrafo To n d -> Statement
vldConsZeroTrafoTo (ConsZeroTrafo a@(ConsZero (DiagramChainTo _ as)) b@(ConsZero (DiagramChainTo _ bs)) (f:|fs))
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

instance Distributive d => Validable (ConsZeroTrafo t n d) where
  valid t@(ConsZeroTrafo a _ _) = Label "ConsZeroTrafo" :<=>: case a of
    ConsZero (DiagramChainTo _ _)   -> vldConsZeroTrafoTo t
    ConsZero (DiagramChainFrom _ _) -> vldConsZeroTrafoTo $ coConsZeroTrafo t

instance (Distributive d, Typeable t, Typeable n) => Entity (ConsZeroTrafo t n d)

--------------------------------------------------------------------------------
-- ConsZeroTrafo - Oriented -

instance (Distributive d, Typeable t, Typeable n) => Oriented (ConsZeroTrafo t n d) where
  type Point (ConsZeroTrafo t n d) = ConsZero t n d
  orientation (ConsZeroTrafo a b _) = a :> b
