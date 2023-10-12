
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- | Singelton types having exactly one element.
module OAlg.Data.Generator
  ( -- * Generator
    Generator(..)

    -- * X
  , XSomeFreeSliceFromLiftable(..), xsfsfl
  , XStandardSomeFreeSliceFromLiftable(..)
  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram
import OAlg.Entity.Slice


import OAlg.Limes.KernelsAndCokernels

--------------------------------------------------------------------------------
-- Generator -

-- | the generator for a finitely generated abelian group.
--
--  __Property__ Let @'Generator' d k' k'' coker ker lft@ be in 'Generator' and let
--  @'DiagramChainTo' g (p':|'p'':|''Nil') = d@
--
-- @
--          p           p'
--   g <<------- g' <------< g''
--
-- @
--
-- then holds:
--
--  (1) @coker@ is the cokernel of @p'@ with @p@ as the shell of its universal cone.
--
--  (2) @ker@ is the kernel of @p@ with @p'@ as the shell of its universal cone.
--
--  (3) @'KenrelSliceFromSomeFreeTip k'' k' ker@ is 'valid'.
--
--  (4) For all @h = 'SliceFrom' _ h'@ in @'Slice' 'From' ('Free' __k__) a@ with
--      @'end' h' '==' g@ holds:
--
--      (1) @lft h@ is 'valid'.
--
--      (2) @'orientation' (lft h) '==' 'start' h ':>' 'start' p@.
--
--      (3) @p 'M.*' lft h '==' h'@.
--
-- @
--             g'
--            ^ |
--           /  |
--   lft h  /   | p
--         /    |
--        /     v
--       * ---> g
--          h'
-- @
data Generator s a where
  GeneratorTo
    :: ( Attestable k', Sliced (Free k') a
       , Attestable k'', Sliced (Free k'') a
       )
    => Diagram (Chain To) N3 N2 a
    -> Free k' a
    -> Free k'' a
    -> Cokernel N1 a
    -> Kernel N1 a
    -> (forall (k :: N') . Slice From (Free k) a -> a)
    -> Generator To a

instance ( Distributive a, XStandardOrtSiteFrom a, XStandardOrtSiteTo a
         , XStandardSomeFreeSliceFromLiftable a
         )
  => Validable (Generator To a) where
  valid gen@(GeneratorTo d k' k'' coker ker lft) = Label (show $ typeOf gen) :<=>:
    And [ valid (d,k',k'',coker,ker)
        , Label "1" :<=>: prpIsCokernel coker (p':|Nil) p
        , Label "2" :<=>: prpIsKernel ker (p:|Nil) p'
        , Label "3" :<=>: valid (KernelSliceFromSomeFreeTip k'' k' ker)
        , Label "4" :<=>: Forall (xsfsfl xStandardSomeFreeSliceFromLiftable g)
          (\(SomeFreeSlice h@(SliceFrom _ h'))
            -> let lh = lft h in
              And [ Label "1" :<=>: valid lh
                  , Label "2" :<=>: (orientation lh == start h' :> start p) :?> Params []
                  , Label "3" :<=>: (p * lh == h') :?> Params ["h'":=show h']
                  ]
          )

        ]

    where DiagramChainTo g (p:|p':|Nil) = d

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

xsfsfl :: XSomeFreeSliceFromLiftable a -> Point a -> X (SomeFreeSlice From a)
xsfsfl (XSomeFreeSliceFromLiftable xfl) = xfl

--------------------------------------------------------------------------------
-- XStandardSomeFreeSliceFromLifable -

-- | random variable of liftable free slice froms.
--
--  __Property__ Let @__a__@ be in instance of 'XStandardSomeFreeSliceLiftable' then holds:
-- For all @p@ in @'Point' a@ and @'SomeSliceFrom' ('SliceFrom' _ h)@ in the range of
-- @'xStandardSomeFreeSliceFromLiftable' p@ holds: @'end' h '==' p@.
class XStandardSomeFreeSliceFromLiftable a where
  xStandardSomeFreeSliceFromLiftable :: XSomeFreeSliceFromLiftable a

