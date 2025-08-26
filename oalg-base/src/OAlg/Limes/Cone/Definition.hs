
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.Definition
-- Description : definition of cones over diagrammatic objects.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of 'Cone's over 'Diagrammatic' objects.
module OAlg.Limes.Cone.Definition
  (
    -- * Cone
    Cone(..), diagrammaticObject, coneDiagram
  , Perspective(..), cnMltOrDst, coneStruct
  , cnDiagramTypeRefl
  , tip, shell, cnArrows, cnPoints

    -- * Duality
  , module Dl

    -- * Constructions
  , cnDstAdjZero
  , cnPrjOrnt, cnInjOrnt
  , cnPrjDstOrnt, cnInjDstOrnt
  
    -- * X
  , xCnPrjOrnt, xCnPrjDstOrnt
  , xCnInjOrnt, xCnInjDstOrnt

  ) where

import Control.Monad

import Data.Typeable
import Data.Array hiding (range)

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Perspective

import OAlg.Limes.Cone.Core
import OAlg.Limes.Cone.Duality as Dl

--------------------------------------------------------------------------------
-- relConePrjMlt -

prm :: N -> Message
prm i = Params["i":=show i]

lE, lS, lO, lC, lB :: Label
lE = Label "end"
lS = Label "start"
lO = Label "orientation"
lC = Label "commutative"
lB = Label "bound"

tp2 :: FinList N2 a -> (a,a)
tp2 (a:|b:|Nil) = (a,b)

ht :: FinList (n+1) a -> (a,FinList n a)
ht (x:|xs) = (x,xs)

relConePrjMlt :: Multiplicative a
  => Diagram t n m a -> Point a -> FinList n a -> Statement
relConePrjMlt DiagramEmpty t Nil = valid t

relConePrjMlt (DiagramDiscrete ps) t cs = valid t && vld 0 t ps cs where
  vld :: Multiplicative a => N -> Point a -> FinList n (Point a) -> FinList n a
         -> Statement
  vld _ _ Nil Nil = SValid
  vld i t (p:|ps) (c:|cs)
    = And [ valid c
          , lO :<=>: (orientation c == t :> p) :?> prm i
          , vld (succ i) t ps cs
          ]

relConePrjMlt (DiagramChainTo l as) t cs = valid cl && vld 0 l as t cl cs' where
  (cl,cs') = ht cs
  vld :: Multiplicative a
    => N -> Point a -> FinList m a -> Point a -> a -> FinList m a -> Statement
  vld i l Nil t cl Nil
    = lO :<=>: (orientation cl == t:>l):?>prm i
  vld i l (a:|as) t cl (c:|cs)
    = And [ valid a
          , valid c
          , lO :<=>: (end a == l):?>prm i
          , lO :<=>: (orientation c == t:>start a):?>prm i
          , lC :<=>: (a*c == cl):?>prm i
          , vld (succ i) (start a) as t c cs 
          ]

relConePrjMlt (DiagramChainFrom l as) t cs = vld 0 l as t cl cs' where
  (cl,cs') = ht cs
  vld :: Multiplicative a
    => N -> Point a -> FinList m a -> Point a -> a -> FinList m a -> Statement
  vld i l Nil t cl Nil
    = And [ valid cl
          , lO :<=>: (orientation cl == t :> l):?>prm i
          ]
  vld i l (a:|as) t cl (c:|cs)
    = And [ valid cl
          , lO :<=>: (start a == l):?>prm i
          , lO :<=>: (orientation cl == t:>start a):?>prm i
          , lC :<=>: (a*cl == c):?>prm i
          , vld (succ i) (end a) as t c cs
          ]

relConePrjMlt (DiagramParallelLR p q as) t cs
  = And [ valid cp
        , valid cq
        , lO :<=>: (orientation cp == t:>p):?>prm 0
        , lO :<=>: (orientation cq == t:>q):?>prm 1
        , vld 0 (p:>q) as cp cq
        ] where
  (cp,cq) = tp2 cs
  vld :: Multiplicative a => N -> Orientation (Point a)
    -> FinList m a -> a -> a -> Statement
  vld _ _ Nil _ _ = SValid
  vld i o (a:|as) cp cq
    = And [ lO :<=>: (orientation a == o):?>prm i
          , lC :<=>: (a*cp == cq):?>prm i
          , vld (succ i) o as cp cq
          ]
      
relConePrjMlt (DiagramParallelRL p q as) t cs
  = And [ valid cp
        , valid cq
        , lO :<=>: (orientation cp == t:>p):?>prm 0
        , lO :<=>: (orientation cq == t:>q):?>prm 1
        , vld 0 (q:>p) as cp cq
        ] where
  (cp,cq) = tp2 cs
  vld :: Multiplicative a => N -> Orientation (Point a)
    -> FinList n a -> a -> a -> Statement
  vld _ _ Nil _ _ = SValid
  vld i o (a:|as) cp cq
    = And [ lO :<=>: (orientation a == o):?>prm i
          , lC :<=>: (a*cq == cp):?>prm i
          , vld (succ i) o as cp cq
          ]

relConePrjMlt (DiagramSource s as) t cs
  = And [ valid c0
        , lO :<=>: (orientation c0 == t:>s):?>prm 0
        , vld 0 t s as c0 cs'
        ] where
  (c0,cs')  = ht cs 
  vld :: Multiplicative a => N -> Point a -> Point a
         -> FinList m a -> a -> FinList m a -> Statement
  vld _ _ _ Nil _ Nil = SValid
  vld i t s (a:|as) c0 (c:|cs)
    = And [ lS :<=>: (start a == s):?>prm i
          , lO :<=>: (orientation c == t:>end a):?>prm i
          , lC :<=>: (a*c0 == c):?>prm i
          , vld (succ i) t s as c0 cs
          ]

relConePrjMlt (DiagramSink e as) t cs
  = And [ valid c0
        , lO :<=>: (orientation c0 == t:>e):?>prm 0
        , vld 0 t e as c0 cs'
        ] where
  (c0,cs') = ht cs
  vld :: Multiplicative a => N -> Point a -> Point a
         -> FinList m a -> a -> FinList m a -> Statement
  vld _ _ _ Nil _ Nil = SValid
  vld i t e (a:|as) c0 (c:|cs)
    = And [ lE :<=>: (end a == e):?>prm i
          , lO :<=>: (orientation c == t:>start a):?>prm i
          , lC :<=>: (a*c == c0):?>prm i
          , vld (succ i) t e as c0 cs
          ]
      
relConePrjMlt (DiagramGeneral ps aijs) t cs
  = And [ vldO 0 t ps cs
        , vldC 0 (toArray cs) aijs
        ] where
  vldO :: Oriented a => N -> Point a
    -> FinList n (Point a) -> FinList n a -> Statement
  vldO _ _ Nil Nil = SValid
  vldO i t (p:|ps) (c:|cs)
    = And [ valid c
          , lO :<=>: (orientation c == t:>p):?>prm i
          , vldO (succ i) t ps cs
          ]

  vldC :: Multiplicative a => N -> Array N a
    -> FinList m (a,Orientation N) -> Statement
  vldC _ _ Nil = SValid
  vldC l cs ((a,i:>j):|aijs)
    = And [ lB :<=>: (inRange (bounds cs) i) :?> Params["l":=show l,"i":=show i]
          , lB :<=>: (inRange (bounds cs) j) :?> Params["l":=show l,"j":=show j]
          , lO :<=>: (orientation a == end ci :> end cj)
                     :?>Params["l":=show l,"(i,j)":=show (i,j)]
          , lC :<=>: (a*ci == cj):?>Params["l":=show l,"(i,j)":=show (i,j)]
          , vldC (succ l) cs aijs
          ] where ci = cs ! i
                  cj = cs ! j

--------------------------------------------------------------------------------
-- cnDstAdjZero -

-- | adjoins a 'zero' arrow to the diagram and the cone.
cnDstAdjZero :: Cone Dst p Diagram t n m a -> Cone Mlt p Diagram t n (m+1) a
cnDstAdjZero (ConeKernel d@(DiagramParallelLR _ r _) k)
  = ConeProjective (dgPrlAdjZero d) t (k:|zero (t:>r):|Nil) where t = start k
cnDstAdjZero c@(ConeCokernel _ _) = cMlt where
  Contravariant2 (Inv2 t f) = toDualOpDst
  
  SDualBi (Left1 c')    = amapF t (SDualBi (Right1 c))
  cMlt'                 = cnDstAdjZero c'
  SDualBi (Right1 cMlt) = amapF f (SDualBi (Left1 cMlt'))

--------------------------------------------------------------------------------
-- relConeDiagram -

-- | validity of a 'Diagram'-'Cone'.
relConeDiagram :: Cone s p Diagram t n m a -> Statement
relConeDiagram (ConeProjective d t cs) = relConePrjMlt d t cs
relConeDiagram c@(ConeInjective _ _ _) = case cnDiagramTypeRefl c of
  Refl -> relConeDiagram c' where
    Contravariant2 (Inv2 t _) = toDualOpMlt
    SDualBi (Left1 c') = cnMapS t (SDualBi (Right1 c))
relConeDiagram c@(ConeKernel _ _)      = relConeDiagram (cnDstAdjZero c)
relConeDiagram c@(ConeCokernel _ _)    = relConeDiagram c' where
  Contravariant2 (Inv2 t _) = toDualOpDst
  SDualBi (Left1 c') = cnMapS t (SDualBi (Right1 c))

--------------------------------------------------------------------------------
-- relCone -

-- | validity of a 'Cone'.
relCone :: Diagrammatic d => Cone s p d t n m a -> Statement
relCone = relConeDiagram . coneDiagram

--------------------------------------------------------------------------------
-- Cone - Validable -

instance (Diagrammatic d, Validable (d t n m a)) => Validable (Cone s p d t n m a) where
  valid c = Label "Cone" :<=>:
    And [ valid (diagrammaticObject c)
        , relCone c
        ]

--------------------------------------------------------------------------------
-- Cone - Parallel - Oriented -

type instance Point (Cone s p d (Parallel t) N2 m a) = Point a
instance ShowPoint a => ShowPoint (Cone s p d (Parallel t) N2 m a)
instance EqPoint a => EqPoint (Cone s p d (Parallel t) N2 m a)
instance ValidablePoint a => ValidablePoint (Cone s p d (Parallel t) N2 m a)
instance TypeablePoint a => TypeablePoint (Cone s p d (Parallel t) N2 m a)

instance ( Oriented a, Diagrammatic d, Entity (d (Parallel t) N2 m a)
         , Typeable d, Typeable s, Typeable p, Typeable t, Typeable m
         )
  => Oriented (Cone s p d (Parallel t) N2 m a) where
  orientation = orientation . diagram . diagrammaticObject

--------------------------------------------------------------------------------
-- cnPrjOrnt -

-- | the projective cone on 'Orientation' with the underlying given diagram and tip with the given
-- point. 
cnPrjOrnt :: (Diagrammatic d, Entity p)
  => p -> d t n m (Orientation p) -> Cone Mlt Projective d t n m (Orientation p)
cnPrjOrnt p d = ConeProjective d p (amap1 (p:>) $ dgPoints $ diagram d)

cnPrjDstOrnt :: (Diagrammatic d, Entity p, t ~ Parallel LeftToRight, n ~ N2)
  => p -> d t n m (Orientation p) -> Cone Dst Projective d t n m (Orientation p)
cnPrjDstOrnt t d = ConeKernel d (t:>p) where DiagramParallelLR p _ _ = diagram d

--------------------------------------------------------------------------------
-- cnInjOrnt -

-- | the injective cone on 'Orientation' with the underlying given diagram and tip with the given
-- point. 
cnInjOrnt :: (Diagrammatic d, Entity p)
  => p -> d t n m (Orientation p) -> Cone Mlt Injective d t n m (Orientation p)
cnInjOrnt p d = ConeInjective d p (amap1 (:>p) $ dgPoints $ diagram d)

cnInjDstOrnt :: (Diagrammatic d, Entity p, t ~ Parallel RightToLeft, n ~ N2)
  => p -> d t n m (Orientation p) -> Cone Dst Injective d t n m (Orientation p)
cnInjDstOrnt t d = ConeCokernel d (q:>t) where DiagramParallelRL _ q _ = diagram d

--------------------------------------------------------------------------------
-- xCnPrjOrnt -

-- | randorm variable for projecive multiplicative cones over 'Orientation'.
xCnPrjOrnt :: (Diagrammatic d, Entity p)
  => X p -> X (d t n m (Orientation p)) -> X (Cone Mlt Projective d t n m (Orientation p))
xCnPrjOrnt xp xd = do
  d <- xd
  p <- xp
  return (cnPrjOrnt p d)
  
instance
  ( Entity p
  , Diagrammatic d
  , XStandard p, XStandard (d t n m (Orientation p))
  )
  => XStandard (Cone Mlt Projective d t n m (Orientation p)) where
  xStandard = xCnPrjOrnt xStandard xStandard

--------------------------------------------------------------------------------
-- xCnPrjDstOrnt -

-- | randorm variable for projecive distributive cones over 'Orientation',
xCnPrjDstOrnt ::
  ( Diagrammatic d
  , Entity p
  , t ~ Parallel LeftToRight, n ~ N2
  )
  => X p -> X (d t n m (Orientation p)) -> X (Cone Dst Projective d t n m (Orientation p))
xCnPrjDstOrnt xp xd = do
  d <- xd
  t <- xp
  return (cnPrjDstOrnt t d)

instance ( Entity p, t ~ Parallel LeftToRight, n ~ N2
         , Diagrammatic d
         , XStandard p, XStandard (d t n m (Orientation p))
         ) => XStandard (Cone Dst Projective d t n m (Orientation p)) where
  xStandard = xCnPrjDstOrnt xStandard xStandard

--------------------------------------------------------------------------------
-- xCnInjOrnt -

-- | randorm variable for injective multiplicative cones over 'Orientation',
xCnInjOrnt :: (Entity p, Diagrammatic d)
  => X p -> X (d t n m (Orientation p)) -> X (Cone Mlt Injective d t n m (Orientation p))
xCnInjOrnt xp xd = do
  d <- xd
  p <- xp
  return (cnInjOrnt p d)

instance
  ( Entity p
  , Diagrammatic d
  , XStandard p, XStandard (d t n m (Orientation p))
  )
  => XStandard (Cone Mlt Injective d t n m (Orientation p)) where
  xStandard = xCnInjOrnt xStandard xStandard

--------------------------------------------------------------------------------
-- xCnInjDstOrnt -

-- | randorm variable for injective distributive cones over 'Orientation',
xCnInjDstOrnt ::(Entity p, t ~ Parallel RightToLeft, n ~ N2, Diagrammatic d)
  => X p -> X (d t n m (Orientation p)) -> X (Cone Dst Injective d t n m (Orientation p))
xCnInjDstOrnt xp xd = do
  d <- xd
  t <- xp
  return (cnInjDstOrnt t d)
  
instance ( Entity p, t ~ Parallel RightToLeft, n ~ N2
         , Diagrammatic d
         , XStandard p, XStandard (d t n m (Orientation p))
         ) => XStandard (Cone Dst Injective d t n m (Orientation p)) where
  xStandard = xCnInjDstOrnt xStandard xStandard

