
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.ConsecutiveZero
-- Description : chain diagrams with consecutive zero arrows. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- chain diagrams with consecutive zero arrows. 
module OAlg.Limes.Exact.ConsecutiveZero
  (
    -- * Consecutive Zero
    ConsecutiveZero(..), cnzSite
  , cnzDiagram, cnzPoints, cnzArrows
  , cnzHead, cnzTail
  , cnzMapS, cnzMapCov, cnzMapCnt

    -- * Transformation
  , ConsecutiveZeroTrafo(..), cnztSite
  , cnztHead, cnztTail
  , cnztMapS, cnztMapCov, cnztMapCnt 

    -- * X
  , xSomeConsecutiveZeroTrafoOrnt, SomeConsecutiveZeroTrafo(..)

  ) where

import Control.Monad
import Control.Applicative ((<|>))

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Variant
import OAlg.Data.Either

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Vectorial
import OAlg.Structure.Algebraic

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Hom.Oriented
import OAlg.Hom.Distributive

--------------------------------------------------------------------------------
-- ConsecutiveZero -

-- | chain diagrams with consecutive zero arrows.
--
-- __Properties__ Let @'ConsecutiveZero' c@ be in @'ConsecutiveZero' __t n x__@
-- for a  'Distributive' structure @__x__@, then holds:
--
-- (1) If @c@ matches @'DiagramChainTo' _ ds@ then holds:
-- @d '*' d'@ is 'zero' for all @..d':|'d'..@ in @ds@.
--
-- (2) If @c@ matches @'DiagramChainFrom' _ ds@ then holds:
-- @d' '*' d@ is 'zero' for all @..d':|'d'..@ in @ds@.
newtype ConsecutiveZero t n x = ConsecutiveZero (Diagram (Chain t) (n+3) (n+2) x)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- cnzSite -

-- | proof that the site is either 'From' or 'To'.
cnzSite :: ConsecutiveZero t n x -> Either (t :~: From) (t :~: To)
cnzSite (ConsecutiveZero d) = case d of
  DiagramChainFrom _ _ -> Left Refl
  DiagramChainTo _ _   -> Right Refl
  
--------------------------------------------------------------------------------
-- cnzDiagram -

-- | the underlying chain diagram.
cnzDiagram :: ConsecutiveZero t n x -> Diagram (Chain t) (n+3) (n+2) x
cnzDiagram (ConsecutiveZero c) = c

--------------------------------------------------------------------------------
-- cnzArrows -

-- | the arrows according to its underlying diagram.
cnzArrows :: ConsecutiveZero t n x -> FinList (n+2) x
cnzArrows = dgArrows . cnzDiagram

--------------------------------------------------------------------------------
-- cnzPoints -

-- | the points according to its underlying diagram.
cnzPoints :: Oriented x => ConsecutiveZero t n x -> FinList (n+3) (Point x)
cnzPoints = dgPoints . cnzDiagram

--------------------------------------------------------------------------------
-- cnzMapCov -

cnzMapCov :: HomDistributiveDisjunctive h
  => Variant2 Covariant h x y -> ConsecutiveZero t n x -> ConsecutiveZero t n y
cnzMapCov h (ConsecutiveZero c) = ConsecutiveZero (dgMapCov h c)

--------------------------------------------------------------------------------
-- cnzMapCnt -

cnzMapCnt :: HomDistributiveDisjunctive h
  => Variant2 Contravariant h x y -> ConsecutiveZero t n x -> ConsecutiveZero (Dual t) n y
cnzMapCnt h (ConsecutiveZero c) = ConsecutiveZero (dgMapCnt h c)

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (ConsecutiveZero t n) = ConsecutiveZero (Dual t) n

--------------------------------------------------------------------------------
-- cnzMapS -

cnzMapS :: (HomDistributiveDisjunctive h, t ~ Dual (Dual t))
  => h x y -> SDualBi (ConsecutiveZero t n) x -> SDualBi (ConsecutiveZero t n) y
cnzMapS = vmapBi cnzMapCov cnzMapCov cnzMapCnt cnzMapCnt

--------------------------------------------------------------------------------
-- Functorial -

instance (HomDistributiveDisjunctive h, t ~ Dual (Dual t))
  => ApplicativeG (SDualBi (ConsecutiveZero t n)) h (->) where
  amapG = cnzMapS

instance
  ( HomDistributiveDisjunctive h, t ~ Dual (Dual t)
  , FunctorialOriented h
  )
  => FunctorialG (SDualBi (ConsecutiveZero t n)) h (->)

--------------------------------------------------------------------------------
-- prpConsecutiveZero -
-- | validity according to 'ConsecutiveZero' for @'Chain' 'To'@.
relConsecutiveZeroTo :: Distributive x => ConsecutiveZero To n x -> Statement
relConsecutiveZeroTo (ConsecutiveZero c@(DiagramChainTo _ ds)) = And [valid c, vldCnz 0 ds] where
  
  vldCnz :: Distributive x => N -> FinList m x -> Statement
  vldCnz _ Nil         = SValid
  vldCnz _ (_:|Nil)    = SValid
  vldCnz i (d:|d':|ds) = And [ isZero (d * d') :?> Params ["i":=show i, "d":=show d, "d'":=show d']
                             , vldCnz (succ i) (d':|ds)
                             ]

-- | validity according to 'ConsecutiveZero'.
relConsecutiveZero :: Distributive x => ConsecutiveZero t n x -> Statement
relConsecutiveZero c@(ConsecutiveZero (DiagramChainTo _ _))   = relConsecutiveZeroTo c
relConsecutiveZero c@(ConsecutiveZero (DiagramChainFrom _ _)) = relConsecutiveZeroTo c' where
  Contravariant2 i = toDualOpDst
  SDualBi (Left1 c') = amapG i (SDualBi (Right1 c))

-- | validity according to 'ConsecutiveZero'.
prpConsecutiveZero :: Distributive x => ConsecutiveZero t n x -> Statement
prpConsecutiveZero c = Prp "ConsecutiveZero" :<=>: relConsecutiveZero c

instance Distributive x => Validable (ConsecutiveZero t n x) where
  valid = prpConsecutiveZero

--------------------------------------------------------------------------------
-- cnzHead -

-- | the two first arrows as a 'ConsecutiveZero'.
cnzHead :: Distributive x => ConsecutiveZero t n x -> ConsecutiveZero t N0 x
cnzHead (ConsecutiveZero (DiagramChainTo e (d:|d':|_)))
  = ConsecutiveZero (DiagramChainTo e (d:|d':|Nil))
cnzHead c@(ConsecutiveZero (DiagramChainFrom _ _)) = c'' where
  Contravariant2 i     = toDualOpDst
  SDualBi (Left1 c')   = amapG i (SDualBi (Right1 c))
  SDualBi (Right1 c'') = amapG (inv2 i) (SDualBi (Left1 $ cnzHead c'))
  
--------------------------------------------------------------------------------
-- cnzTail -

-- | dropping the first arrow.
cnzTail :: Distributive d => ConsecutiveZero t (n+1) d -> ConsecutiveZero t n d
cnzTail (ConsecutiveZero (DiagramChainTo _ (a:|as))) = ConsecutiveZero (DiagramChainTo (start a) as)
                                                                                       -- a is dropped
cnzTail c@(ConsecutiveZero (DiagramChainFrom _ _))   = c'' where
  Contravariant2 i    = toDualOpDst
  SDualBi (Left1 c')   = amapG i (SDualBi (Right1 c))
  SDualBi (Right1 c'') = amapG (inv2 i) (SDualBi (Left1 $ cnzTail c'))
  

--------------------------------------------------------------------------------
-- ConsecutiveZeroTrafo -

-- | diagram transformation between two consecutive zero chains.
--
-- __Property__ Let @'ConsecutiveZeroTrafo' t@ be in @'ConsecutiveZeroTraf' __t n x__@ within a
-- 'Distributive' structure @__x__@, then holds
--
-- (1) @'start' t@ and @'end' t@ are consecutive zero chains.
--
newtype ConsecutiveZeroTrafo t n x
  = ConsecutiveZeroTrafo (DiagramTrafo (Chain t) (n+3) (n+2) x)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- cnztSite -

-- | proof that the site is either 'From' or 'To'.
cnztSite :: ConsecutiveZeroTrafo t n x -> Either (t :~: From) (t :~: To)
cnztSite (ConsecutiveZeroTrafo (DiagramTrafo d _ _)) = case d of
  DiagramChainFrom _ _ -> Left Refl
  DiagramChainTo _ _   -> Right Refl
  
{-
--------------------------------------------------------------------------------
-- cnztTrafos -

-- | the transformations.
cnztTrafos :: ConsecutiveZeroTrafo t n d -> FinList (n+3) d
cnztTrafos (ConsecutiveZeroTrafo _ _ fs) = fs

--------------------------------------------------------------------------------
-- cnztDiagramTrafo -

-- | the underlying 'DiagramTrafo'.
cnztDiagramTrafo :: ConsecutiveZeroTrafo t n d -> DiagramTrafo (Chain t) (n+3) (n+2) d
cnztDiagramTrafo (ConsecutiveZeroTrafo a b fs) = DiagramTrafo (cnzDiagram a) (cnzDiagram b) fs
-}

--------------------------------------------------------------------------------
-- cnztMapCov -

cnztMapCov :: HomDistributiveDisjunctive h
  => Variant2 Covariant h x y -> ConsecutiveZeroTrafo t n x -> ConsecutiveZeroTrafo t n y
cnztMapCov h (ConsecutiveZeroTrafo t) = ConsecutiveZeroTrafo (dgtMapCov h t)

--------------------------------------------------------------------------------
-- cnztMapCnt -

cnztMapCnt :: HomDistributiveDisjunctive h
  => Variant2 Contravariant h x y -> ConsecutiveZeroTrafo t n x -> ConsecutiveZeroTrafo (Dual t) n y
cnztMapCnt h (ConsecutiveZeroTrafo t) = ConsecutiveZeroTrafo (dgtMapCnt h t)

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (ConsecutiveZeroTrafo t n) = ConsecutiveZeroTrafo (Dual t) n

--------------------------------------------------------------------------------
-- cnztMapS -

cnztMapS :: (HomDistributiveDisjunctive h, t ~ Dual (Dual t))
  => h x y -> SDualBi (ConsecutiveZeroTrafo t n) x -> SDualBi (ConsecutiveZeroTrafo t n) y
cnztMapS = vmapBi cnztMapCov cnztMapCov cnztMapCnt cnztMapCnt

--------------------------------------------------------------------------------
-- Functorial -

instance (HomDistributiveDisjunctive h, t ~ Dual (Dual t))
  => ApplicativeG (SDualBi (ConsecutiveZeroTrafo t n)) h (->) where
  amapG = cnztMapS
  
instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConsecutiveZeroTrafo t n)) h (->)

--------------------------------------------------------------------------------
-- Validable -

instance (Distributive x, Typeable t, Typeable n) => Validable (ConsecutiveZeroTrafo t n x) where
  valid (ConsecutiveZeroTrafo t) = Label "ConsecutiveZeroTrafo" :<=>:
    And [ valid t
        , Label "start" :<=>: valid (ConsecutiveZero $ start t)
        , Label "end" :<=>: valid (ConsecutiveZero $ end t)
        ]
    
--------------------------------------------------------------------------------
-- ConsecutiveZeroTrafo - Algebraic -

type instance Point (ConsecutiveZeroTrafo t n x) = ConsecutiveZero t n x

instance (Show x, ShowPoint x) => ShowPoint (ConsecutiveZeroTrafo t n x)
instance (Eq x, EqPoint x) => EqPoint (ConsecutiveZeroTrafo t n x)
instance Distributive x => ValidablePoint (ConsecutiveZeroTrafo t n x)
instance (Typeable x, Typeable t, Typeable n) => TypeablePoint (ConsecutiveZeroTrafo t n x)

instance (Distributive x, Typeable t, Typeable n) => Oriented (ConsecutiveZeroTrafo t n x) where
  orientation (ConsecutiveZeroTrafo t) = ConsecutiveZero a :> ConsecutiveZero b where
    a :> b = orientation t

instance (Distributive x, Typeable t, Typeable n) => Multiplicative (ConsecutiveZeroTrafo t n x) where
  one (ConsecutiveZero c) = ConsecutiveZeroTrafo $ one c
  ConsecutiveZeroTrafo f * ConsecutiveZeroTrafo g = ConsecutiveZeroTrafo (f*g)
  npower (ConsecutiveZeroTrafo f) n = ConsecutiveZeroTrafo (npower f n)
  
type instance Root (ConsecutiveZeroTrafo t n x) = Orientation (ConsecutiveZero t n x)

instance (Show x, ShowPoint x) => ShowRoot (ConsecutiveZeroTrafo t n x)
instance (Eq x, EqPoint x) => EqRoot (ConsecutiveZeroTrafo t n x)
instance Distributive x => ValidableRoot (ConsecutiveZeroTrafo t n x)
instance (Typeable x, Typeable t, Typeable n) => TypeableRoot (ConsecutiveZeroTrafo t n x)

instance (Distributive x, Typeable t, Typeable n) => Fibred (ConsecutiveZeroTrafo t n x)
  
instance (Distributive x, Typeable t, Typeable n) => FibredOriented (ConsecutiveZeroTrafo t n x)

instance (Distributive x, Typeable t, Typeable n) => Additive (ConsecutiveZeroTrafo t n x) where
  zero (ConsecutiveZero a :> ConsecutiveZero b) = ConsecutiveZeroTrafo $ zero (a :> b)
  ConsecutiveZeroTrafo f + ConsecutiveZeroTrafo g = ConsecutiveZeroTrafo (f+g)
  ntimes n (ConsecutiveZeroTrafo t) = ConsecutiveZeroTrafo (ntimes n t)
  
instance (Distributive x, Abelian x, Typeable t, Typeable n)
  => Abelian (ConsecutiveZeroTrafo t n x) where
  negate (ConsecutiveZeroTrafo t) = ConsecutiveZeroTrafo $ negate t
  ConsecutiveZeroTrafo f - ConsecutiveZeroTrafo g = ConsecutiveZeroTrafo (f-g)
  ztimes n (ConsecutiveZeroTrafo t) = ConsecutiveZeroTrafo (ztimes n t)
  
instance (Distributive x, Typeable t, Typeable n) => Distributive (ConsecutiveZeroTrafo t n x)

instance (Algebraic x, Typeable t, Typeable n) => Vectorial (ConsecutiveZeroTrafo t n x) where
  type Scalar (ConsecutiveZeroTrafo t n x) = Scalar x
  x ! ConsecutiveZeroTrafo t = ConsecutiveZeroTrafo (x!t)

instance (Algebraic x, Typeable t, Typeable n) => Algebraic (ConsecutiveZeroTrafo t n x)

--------------------------------------------------------------------------------
-- cnztHead -

-- | the first two arrows of the given 'ConsecutiveZeroTrafo'.
cnztHead :: Distributive x => ConsecutiveZeroTrafo t n x -> ConsecutiveZeroTrafo t N0 x
cnztHead (ConsecutiveZeroTrafo (DiagramTrafo a b (f0:|f1:|f2:|_)))
  = ConsecutiveZeroTrafo (DiagramTrafo a' b' (f0:|f1:|f2:|Nil)) where
  ConsecutiveZero a' = cnzHead $ ConsecutiveZero a
  ConsecutiveZero b' = cnzHead $ ConsecutiveZero b
  
--------------------------------------------------------------------------------
-- cnztTail -

-- | dropping the first arrow.
cnztTail :: Distributive x => ConsecutiveZeroTrafo t (n+1) x -> ConsecutiveZeroTrafo t n x
cnztTail (ConsecutiveZeroTrafo (DiagramTrafo a b fs))
  = ConsecutiveZeroTrafo (DiagramTrafo a' b' (tail fs)) where
  ConsecutiveZero a' = cnzTail $ ConsecutiveZero a
  ConsecutiveZero b' = cnzTail $ ConsecutiveZero b
  
--------------------------------------------------------------------------------
-- SomeConsecutiveZeroTrafo -

-- | some 'ConsecutiveZeroTrafo'.
data SomeConsecutiveZeroTrafo x where
  SomeConsecutiveZeroTrafo :: (Typeable t, Typeable n)
    => ConsecutiveZeroTrafo t n x -> SomeConsecutiveZeroTrafo x

instance Distributive x => Validable (SomeConsecutiveZeroTrafo x) where
  valid (SomeConsecutiveZeroTrafo t) = Label "SomeConsecutiveZeroTrafo" :<=>: valid t
  
--------------------------------------------------------------------------------
-- xSomeConsecutiveZeroTrafoOrnt -

-- | random variable for @'ConsecutiveZeroTrafo' __t n__ 'OS'@ with a maximal @__n__@ of the given one.
xSomeConsecutiveZeroTrafoOrnt :: N -> X (SomeConsecutiveZeroTrafo OS)
xSomeConsecutiveZeroTrafoOrnt n = xscnztTo n <|> xscnztFrom n where

  xTo :: Any n -> X (Diagram (Chain To) (n+3) (n+2) OS)
  xTo n = xDiagram Refl $ XDiagramChainTo (SW $ SW n) xStandardOrtSite
  
  xFrom :: Any n -> X (Diagram (Chain From) (n+3) (n+2) OS)
  xFrom n = xDiagram Refl $ XDiagramChainFrom (SW $ SW n) xStandardOrtSite
  
  xcnztTo :: Any n -> X (ConsecutiveZeroTrafo To n OS)
  xcnztTo n = do
    a <- xTo n
    b <- xTo n
    return $ ConsecutiveZeroTrafo
           $ DiagramTrafo a b
           $ amap1 (uncurry (:>))
           $ (dgPoints a `zip` dgPoints b) 

  xcnztFrom :: Any n -> X (ConsecutiveZeroTrafo From n OS)
  xcnztFrom n = do
    a <- xFrom n
    b <- xFrom n
    return $ ConsecutiveZeroTrafo
           $ DiagramTrafo a b
           $ amap1 (uncurry (:>))
           $ (dgPoints a `zip` dgPoints b) 
  
  xscnztTo :: N -> X (SomeConsecutiveZeroTrafo OS)
  xscnztTo n = do
    SomeNatural n' <- amap1 someNatural $ xNB 0 n
    t              <- xcnztTo n'
    return $ SomeConsecutiveZeroTrafo t

  xscnztFrom :: N -> X (SomeConsecutiveZeroTrafo OS)
  xscnztFrom n = do
    SomeNatural n' <- amap1 someNatural $ xNB 0 n
    t              <- xcnztFrom n'
    return $ SomeConsecutiveZeroTrafo t
  

