
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

    -- ** Duality
  , cnzMapS, cnzMapCov, cnzMapCnt

    -- * Consecutive Zero Hom
  , ConsecutiveZeroHom(..), cnzHomSite, cnzHomArrows
  , cnzHomHead, cnzHomTail

    -- ** Duality
  , cnzHomMapS, cnzHomMapCov, cnzHomMapCnt 

    -- * X
  , xSomeConsecutiveZeroHomOrnt, SomeConsecutiveZeroHom(..)

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
  SDualBi (Left1 c') = amapF i (SDualBi (Right1 c))

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
  SDualBi (Left1 c')   = amapF i (SDualBi (Right1 c))
  SDualBi (Right1 c'') = amapF (inv2 i) (SDualBi (Left1 $ cnzHead c'))
  
--------------------------------------------------------------------------------
-- cnzTail -

-- | dropping the first arrow.
cnzTail :: Distributive d => ConsecutiveZero t (n+1) d -> ConsecutiveZero t n d
cnzTail (ConsecutiveZero (DiagramChainTo _ (a:|as))) = ConsecutiveZero (DiagramChainTo (start a) as)
                                                                                       -- a is dropped
cnzTail c@(ConsecutiveZero (DiagramChainFrom _ _))   = c'' where
  Contravariant2 i    = toDualOpDst
  SDualBi (Left1 c')   = amapF i (SDualBi (Right1 c))
  SDualBi (Right1 c'') = amapF (inv2 i) (SDualBi (Left1 $ cnzTail c'))
  

--------------------------------------------------------------------------------
-- ConsecutiveZeroHom -

-- | homomorphism between two consecutive zero chains.
--
-- __Property__ Let @'ConsecutiveZeroHom' t@ be in @'ConsecutiveZeroTraf' __t n x__@ within a
-- 'Distributive' structure @__x__@, then holds
--
-- (1) @'start' t@ and @'end' t@ are consecutive zero chains.
--
newtype ConsecutiveZeroHom t n x
  = ConsecutiveZeroHom (DiagramTrafo (Chain t) (n+3) (n+2) x)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- cnzHomSite -

-- | proof that the site is either 'From' or 'To'.
cnzHomSite :: ConsecutiveZeroHom t n x -> Either (t :~: From) (t :~: To)
cnzHomSite (ConsecutiveZeroHom (DiagramTrafo d _ _)) = case d of
  DiagramChainFrom _ _ -> Left Refl
  DiagramChainTo _ _   -> Right Refl
  
--------------------------------------------------------------------------------
-- cnzHomMapCov -

cnzHomMapCov :: HomDistributiveDisjunctive h
  => Variant2 Covariant h x y -> ConsecutiveZeroHom t n x -> ConsecutiveZeroHom t n y
cnzHomMapCov h (ConsecutiveZeroHom t) = ConsecutiveZeroHom (dgtMapCov h t)

--------------------------------------------------------------------------------
-- cnzHomMapCnt -

cnzHomMapCnt :: HomDistributiveDisjunctive h
  => Variant2 Contravariant h x y -> ConsecutiveZeroHom t n x -> ConsecutiveZeroHom (Dual t) n y
cnzHomMapCnt h (ConsecutiveZeroHom t) = ConsecutiveZeroHom (dgtMapCnt h t)

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (ConsecutiveZeroHom t n) = ConsecutiveZeroHom (Dual t) n

--------------------------------------------------------------------------------
-- cnzHomMapS -

cnzHomMapS :: (HomDistributiveDisjunctive h, t ~ Dual (Dual t))
  => h x y -> SDualBi (ConsecutiveZeroHom t n) x -> SDualBi (ConsecutiveZeroHom t n) y
cnzHomMapS = vmapBi cnzHomMapCov cnzHomMapCov cnzHomMapCnt cnzHomMapCnt

--------------------------------------------------------------------------------
-- Functorial -

instance (HomDistributiveDisjunctive h, t ~ Dual (Dual t))
  => ApplicativeG (SDualBi (ConsecutiveZeroHom t n)) h (->) where
  amapG = cnzHomMapS
  
instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (ConsecutiveZeroHom t n)) h (->)

--------------------------------------------------------------------------------
-- Validable -

instance (Distributive x, Typeable t, Typeable n) => Validable (ConsecutiveZeroHom t n x) where
  valid (ConsecutiveZeroHom t) = Label "ConsecutiveZeroHom" :<=>:
    And [ valid t
        , Label "start" :<=>: valid (ConsecutiveZero $ start t)
        , Label "end" :<=>: valid (ConsecutiveZero $ end t)
        ]
    
--------------------------------------------------------------------------------
-- ConsecutiveZeroHom - Algebraic -

type instance Point (ConsecutiveZeroHom t n x) = ConsecutiveZero t n x

instance (Show x, ShowPoint x) => ShowPoint (ConsecutiveZeroHom t n x)
instance (Eq x, EqPoint x) => EqPoint (ConsecutiveZeroHom t n x)
instance Distributive x => ValidablePoint (ConsecutiveZeroHom t n x)
instance (Typeable x, Typeable t, Typeable n) => TypeablePoint (ConsecutiveZeroHom t n x)

instance (Distributive x, Typeable t, Typeable n) => Oriented (ConsecutiveZeroHom t n x) where
  orientation (ConsecutiveZeroHom t) = ConsecutiveZero a :> ConsecutiveZero b where
    a :> b = orientation t

instance (Distributive x, Typeable t, Typeable n) => Multiplicative (ConsecutiveZeroHom t n x) where
  one (ConsecutiveZero c) = ConsecutiveZeroHom $ one c
  ConsecutiveZeroHom f * ConsecutiveZeroHom g = ConsecutiveZeroHom (f*g)
  npower (ConsecutiveZeroHom f) n = ConsecutiveZeroHom (npower f n)
  
type instance Root (ConsecutiveZeroHom t n x) = Orientation (ConsecutiveZero t n x)

instance (Show x, ShowPoint x) => ShowRoot (ConsecutiveZeroHom t n x)
instance (Eq x, EqPoint x) => EqRoot (ConsecutiveZeroHom t n x)
instance Distributive x => ValidableRoot (ConsecutiveZeroHom t n x)
instance (Typeable x, Typeable t, Typeable n) => TypeableRoot (ConsecutiveZeroHom t n x)

instance (Distributive x, Typeable t, Typeable n) => Fibred (ConsecutiveZeroHom t n x)
  
instance (Distributive x, Typeable t, Typeable n) => FibredOriented (ConsecutiveZeroHom t n x)

instance (Distributive x, Typeable t, Typeable n) => Additive (ConsecutiveZeroHom t n x) where
  zero (ConsecutiveZero a :> ConsecutiveZero b) = ConsecutiveZeroHom $ zero (a :> b)
  ConsecutiveZeroHom f + ConsecutiveZeroHom g = ConsecutiveZeroHom (f+g)
  ntimes n (ConsecutiveZeroHom t) = ConsecutiveZeroHom (ntimes n t)
  
instance (Distributive x, Abelian x, Typeable t, Typeable n)
  => Abelian (ConsecutiveZeroHom t n x) where
  negate (ConsecutiveZeroHom t) = ConsecutiveZeroHom $ negate t
  ConsecutiveZeroHom f - ConsecutiveZeroHom g = ConsecutiveZeroHom (f-g)
  ztimes n (ConsecutiveZeroHom t) = ConsecutiveZeroHom (ztimes n t)
  
instance (Distributive x, Typeable t, Typeable n) => Distributive (ConsecutiveZeroHom t n x)

instance (Algebraic x, Typeable t, Typeable n) => Vectorial (ConsecutiveZeroHom t n x) where
  type Scalar (ConsecutiveZeroHom t n x) = Scalar x
  x ! ConsecutiveZeroHom t = ConsecutiveZeroHom (x!t)

instance (Algebraic x, Typeable t, Typeable n) => Algebraic (ConsecutiveZeroHom t n x)

--------------------------------------------------------------------------------
-- cnzHomHead -

-- | the first two arrows of the given 'ConsecutiveZeroHom'.
cnzHomHead :: Distributive x => ConsecutiveZeroHom t n x -> ConsecutiveZeroHom t N0 x
cnzHomHead (ConsecutiveZeroHom (DiagramTrafo a b (f0:|f1:|f2:|_)))
  = ConsecutiveZeroHom (DiagramTrafo a' b' (f0:|f1:|f2:|Nil)) where
  ConsecutiveZero a' = cnzHead $ ConsecutiveZero a
  ConsecutiveZero b' = cnzHead $ ConsecutiveZero b
  
--------------------------------------------------------------------------------
-- cnzHomTail -

-- | dropping the first arrow.
cnzHomTail :: Distributive x => ConsecutiveZeroHom t (n+1) x -> ConsecutiveZeroHom t n x
cnzHomTail (ConsecutiveZeroHom (DiagramTrafo a b fs))
  = ConsecutiveZeroHom (DiagramTrafo a' b' (tail fs)) where
  ConsecutiveZero a' = cnzTail $ ConsecutiveZero a
  ConsecutiveZero b' = cnzTail $ ConsecutiveZero b

--------------------------------------------------------------------------------
-- cnzHomArrows -

-- | the underlying arrows.
cnzHomArrows :: ConsecutiveZeroHom t n x -> FinList (n+3) x
cnzHomArrows (ConsecutiveZeroHom (DiagramTrafo _ _ fs)) = fs

--------------------------------------------------------------------------------
-- SomeConsecutiveZeroHom -

-- | some 'ConsecutiveZeroHom'.
data SomeConsecutiveZeroHom x where
  SomeConsecutiveZeroHom :: (Typeable t, Attestable n)
    => ConsecutiveZeroHom t n x -> SomeConsecutiveZeroHom x

instance Distributive x => Validable (SomeConsecutiveZeroHom x) where
  valid (SomeConsecutiveZeroHom t) = Label "SomeConsecutiveZeroHom" :<=>: valid t
  
--------------------------------------------------------------------------------
-- xSomeConsecutiveZeroHomOrnt -

-- | random variable for @'ConsecutiveZeroHom' __t n__ 'OS'@ with a maximal @__n__@ of the given one.
xSomeConsecutiveZeroHomOrnt :: N -> X (SomeConsecutiveZeroHom OS)
xSomeConsecutiveZeroHomOrnt n = xscnzHomTo n <|> xscnzHomFrom n where

  xTo :: Any n -> X (Diagram (Chain To) (n+3) (n+2) OS)
  xTo n = xDiagram Refl $ XDiagramChainTo (SW $ SW n) xStandardOrtSite
  
  xFrom :: Any n -> X (Diagram (Chain From) (n+3) (n+2) OS)
  xFrom n = xDiagram Refl $ XDiagramChainFrom (SW $ SW n) xStandardOrtSite
  
  xcnzHomTo :: Any n -> X (ConsecutiveZeroHom To n OS)
  xcnzHomTo n = do
    a <- xTo n
    b <- xTo n
    return $ ConsecutiveZeroHom
           $ DiagramTrafo a b
           $ amap1 (uncurry (:>))
           $ (dgPoints a `zip` dgPoints b) 

  xcnzHomFrom :: Any n -> X (ConsecutiveZeroHom From n OS)
  xcnzHomFrom n = do
    a <- xFrom n
    b <- xFrom n
    return $ ConsecutiveZeroHom
           $ DiagramTrafo a b
           $ amap1 (uncurry (:>))
           $ (dgPoints a `zip` dgPoints b) 
  
  xscnzHomTo :: N -> X (SomeConsecutiveZeroHom OS)
  xscnzHomTo n = do
    SomeNatural n' <- amap1 someNatural $ xNB 0 n
    t              <- xcnzHomTo n'
    return $ SomeConsecutiveZeroHom t

  xscnzHomFrom :: N -> X (SomeConsecutiveZeroHom OS)
  xscnzHomFrom n = do
    SomeNatural n' <- amap1 someNatural $ xNB 0 n
    t              <- xcnzHomFrom n'
    return $ SomeConsecutiveZeroHom t
  

