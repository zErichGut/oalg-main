
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.Data.Generator
-- Description : generators or embeddings for finitely presentable points.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Finitely presentable 'Point's within 'Distributive' structures.
module OAlg.Data.FinitelyPresentable
  (
    -- * Finitely Presentable
    FinitelyPresentable(..), finitePresentation

    -- * Splitable
  , Splitable(..), split
    
    -- * Finite Presentation
  , FinitePresentation(..)
  , finitePoint, generator, embedding
  , SomeSliceN(..)

    -- * X
  , XSomeFreeSliceFromLiftable(..), xsfsfl
  , XStandardSomeFreeSliceFromLiftable(..)

  )
  where

import Data.Typeable
import Data.Kind

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Distributive
import OAlg.Structure.Operational

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram
import OAlg.Entity.Slice

import OAlg.Limes.KernelsAndCokernels

--------------------------------------------------------------------------------
-- Splitable -

-- | predicate for splitable slices.
--
--  __Propterties__ Let @__d__@ be 'Oriented' and @'Sliced' (__ i__ __k__) __d__@ for all
--  @__k__@, then holds:
--
--  (1) Let @'Splitable' splt@ be in @'Splitable' 'From' __i__ __d__@ then holds:
--  For all @__k__@ and @s@ in @'Slice' 'From' (__i__ __k__) __d__@ holds:
--  @'end' s' '==' 'end' s@ for all @s'@ in @splt s@.
newtype Splitable s i d
  = Splitable
      (forall k. (Attestable k, Sliced (i k) d)
         => Slice s (i k) d -> FinList k (Slice s (i N1) d)
      )

--------------------------------------------------------------------------------
-- split -

-- | splitting of a slice of dimension @__i__ __k__@.
split :: (Attestable k, Sliced (i k) d)
  => Splitable s i d -> Slice s (i k) d -> FinList k (Slice s (i N1) d)
split (Splitable s) = s


--------------------------------------------------------------------------------
-- FinitePresentation -

-- | finitely presentable 'Point's within a 'Distributive' structure.
--
-- __Property 1__ Let @'GeneratorTo' d k' k'' coker ker lft@ be in
-- @'FinitePresentation' 'From' __i__ __a__@ and let
-- @'DiagramChainTo' p (g':|'g'':|''Nil') = d@
--
-- @
--          g           g'
--   p <<------- p' <------< p''
--
-- @
--
-- then holds:
--
-- (1) @coker@ is the cokernel of @g'@ with @g@ as the shell factor of its universal cone.
--
-- (2) @ker@ is the kernel of @g@ with @g'@ as the shell factor of its universal cone.
--
-- (3) @'KenrelSliceFromSomeFreeTip' k'' k' ker@ is 'valid'.
--
-- (4) For all @h@ in @'Slice' 'From' (__i__ __k__) a@ with
-- @'end' h '==' p@ holds:
--
--     (1) @lft h@ is 'valid'.
--
--     (2) @'orientation' (lft h) '==' 'start' h ':>' 'start' g@.
--
--     (3) @g '*>' lft h '==' h@.
--
-- @
--              p'
--            ^ |
--           /  |
--   lft h  /   | g
--         /    |
--        /     v
--       * ---> p
--          h
-- @
--
-- __Property 2__ Let @'EmbeddingTo' d k' k'' ker coker lft@ be in
-- -- @'FinitePresentation' 'To' __i__ __a__@ then holds the dual of the property 1 above.
data FinitePresentation s i a where
  GeneratorTo
    :: ( Attestable k' , Sliced (i k') a
       , Attestable k'', Sliced (i k'') a
       )
    => Diagram (Chain To) N3 N2 a
    -> i k' a
    -> i k'' a
    -> Cokernel N1 a
    -> Kernel N1 a
    -> (forall (k :: N') . Slice From (i k) a -> Slice From (i k) a)
    -> FinitePresentation To i a
  EmbeddingFrom
    :: ( Attestable k', Sliced (i k') a
       , Attestable k'', Sliced (i k'') a
       )
    => Diagram (Chain From) N3 N2 a
    -> i k' a
    -> i k'' a
    -> Kernel N1 a
    -> Cokernel N1 a
    -> (forall (k :: N') . Slice To (i k) a -> Slice To (i k) a)
    -> FinitePresentation From i a

--------------------------------------------------------------------------------
-- FinitelyPresentable -

-- | predicate for finitely presentable 'Distributive' structures @__a__@, where for each
--   point @p@ in @'Point' __a__@ there is an associated @'FinitePresentation' __s__ __i__ __a__@
--   such that its 'finitePoint' is equal to @p@.
newtype FinitelyPresentable s i a = FinitelyPresentable (Point a -> FinitePresentation s i a)

--------------------------------------------------------------------------------
-- finitePoint -

-- | the underlying finite point given by the finite presentation.
finitePoint :: FinitePresentation s i a -> Point a
finitePoint (GeneratorTo (DiagramChainTo e _) _ _ _ _ _)     = e
finitePoint (EmbeddingFrom (DiagramChainFrom s _) _ _ _ _ _) = s

--------------------------------------------------------------------------------
-- SomeSliceN -

-- | some slice.
data SomeSliceN t (i :: N' -> Type -> Type) d where
  SomeSliceN :: (Attestable n, Sliced (i n) d) => Slice t (i n) d -> SomeSliceN t i d

deriving instance Show d => Show (SomeSliceN t i d)

--------------------------------------------------------------------------------
-- generator -

-- | the generator 
generator :: FinitePresentation To i a -> SomeSliceN From i a
generator (GeneratorTo (DiagramChainTo _ (p:|_)) k' _ _ _ _)
  = SomeSliceN (SliceFrom k' p)

--------------------------------------------------------------------------------
-- embedding -

-- | the embedding of the finite point.
embedding :: FinitePresentation From i a -> SomeSliceN To i a
embedding (EmbeddingFrom (DiagramChainFrom _ (i:|_)) k' _ _ _ _)
  = SomeSliceN (SliceTo k' i)

--------------------------------------------------------------------------------
-- finitePresentation -

finitePresentation :: FinitelyPresentable s i a -> Point a -> FinitePresentation s i a
finitePresentation (FinitelyPresentable f) = f

--------------------------------------------------------------------------------
-- XSomeFreeSliceFromLiftable -

-- | random variable of factors in @__a__@ having a free 'start' and as 'end'-point the
--   given one.
newtype XSomeFreeSliceFromLiftable a
  = XSomeFreeSliceFromLiftable (Point a -> X (SomeFreeSlice From a))

instance (Oriented a, XStandardPoint a) => Validable (XSomeFreeSliceFromLiftable a) where
  valid (XSomeFreeSliceFromLiftable lft) = Prp "XSomeFreeSliceFromLiftable" :<=>:
    Forall xStandard
      (\p -> Forall (lft p) (\(SomeFreeSlice h@(SliceFrom _ h'))
             -> And [ valid h
                    , (end h' == p) :?> Params []
                    ]
                            )
      )

--------------------------------------------------------------------------------
-- xsfsfl -

-- | the underlying random variable for some free slice.
xsfsfl :: XSomeFreeSliceFromLiftable a -> Point a -> X (SomeFreeSlice From a)
xsfsfl (XSomeFreeSliceFromLiftable xfl) = xfl

--------------------------------------------------------------------------------
-- XStandardSomeFreeSliceFromLifable -

-- | random variable of lift-able free slice froms.
--
--  __Property__ Let @__a__@ be in instance of 'XStandardSomeFreeSliceFromLiftable' then holds:
-- For all @p@ in @'Point' __a__@ and @'SomeFreeSlice' ('SliceFrom' _ h)@ in the range of
-- @'xStandardSomeFreeSliceFromLiftable' p@ holds: @'end' h '==' p@.
class XStandardSomeFreeSliceFromLiftable a where
  xStandardSomeFreeSliceFromLiftable :: XSomeFreeSliceFromLiftable a

--------------------------------------------------------------------------------
-- Validable - FinitePresentation To Free a

instance
  ( Distributive a
  , XStandardEligibleConeCokernel N1 a
  , XStandardEligibleConeFactorCokernel N1 a
  , XStandardEligibleConeKernel N1 a
  , XStandardEligibleConeFactorKernel N1 a
  , XStandardSomeFreeSliceFromLiftable a
  )
  => Validable (FinitePresentation To Free a) where
  valid gen@(GeneratorTo d k' k'' coker ker lft) = Label (show $ typeOf gen) :<=>:
    And [ valid (d,k',k'',coker,ker)
        , Label "1" :<=>: prpIsCokernel coker (g':|Nil) g
        , Label "2" :<=>: prpIsKernel ker (g:|Nil) g'
        , Label "3" :<=>: valid (KernelSliceFromSomeFreeTip k'' k' ker)
        , Label "4" :<=>: Forall (xsfsfl xStandardSomeFreeSliceFromLiftable p)
          (\(SomeFreeSlice h)
            -> let lh = lft h in
              And [ Label "1" :<=>: valid lh
                  , Label "2" :<=>: (orientation lh == start h :> start g) :?> Params ["lh":=show lh]
                  , Label "3" :<=>: (g *> lh == h) :?> Params ["h":=show h]
                  ]
          )

        ]

       where DiagramChainTo p (g:|g':|Nil) = d




