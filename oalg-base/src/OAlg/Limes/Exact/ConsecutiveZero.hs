
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.ConsecutiveZero
-- Description : chain diagrams with consecutive zero-able arrows. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- chain diagrams with consecutive zero-able arrows. 
module OAlg.Limes.Exact.ConsecutiveZero
  (

    -- * Consecutive Zero
    ConsecutiveZero(..), cnzDiagram, cnzPoints, cnzArrows
  , cnzHead, cnzTail
  , cnzMapS, cnzMapCov, cnzMapCnt

    -- * Transformation
  , ConsecutiveZeroTrafo(..), cnztTrafos, cnztDiagramTrafo
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

import OAlg.Structure.Exception
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

-- | chain diagrams with consecutive zero-able arrows.
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

-- | transformation between two 'ConsecutiveZero's.
--
-- __Properties__ Let @'ConsecutiveZeroTrafo' a b fs@ be in @'ConsecutiveZeroTrafo' __t n x__@ for a
-- 'Distributive' structure @__x__@, then holds:
--
-- (1) If @a@ matches @'ConsecutiveZero' ('DiagramChainTo' _ as)@, then holds:
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
-- (2) If @a@ matches @'ConsecutiveZero' ('DiagramChainFrom' _ as)@, then holds:
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
data ConsecutiveZeroTrafo t n x
  = ConsecutiveZeroTrafo (ConsecutiveZero t n x) (ConsecutiveZero t n x) (FinList (n+3) x)
  deriving (Show,Eq)

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

--------------------------------------------------------------------------------
-- cnztMapCov -

cnztMapCov :: HomDistributiveDisjunctive h
  => Variant2 Covariant h x y -> ConsecutiveZeroTrafo t n x -> ConsecutiveZeroTrafo t n y
cnztMapCov h (ConsecutiveZeroTrafo a b fs) = ConsecutiveZeroTrafo a' b' fs' where
  a'  = cnzMapCov h a
  b'  = cnzMapCov h b
  fs' = amap1 (amap h) fs

--------------------------------------------------------------------------------
-- cnztMapCnt -

cnztMapCnt :: HomDistributiveDisjunctive h
  => Variant2 Contravariant h x y -> ConsecutiveZeroTrafo t n x -> ConsecutiveZeroTrafo (Dual t) n y
cnztMapCnt h (ConsecutiveZeroTrafo a b fs) = ConsecutiveZeroTrafo b' a' fs' where
  a'  = cnzMapCnt h a
  b'  = cnzMapCnt h b
  fs' = amap1 (amap h) fs

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (ConsecutiveZeroTrafo t n) = ConsecutiveZeroTrafo (Dual t) n

--------------------------------------------------------------------------------
-- cnztMapS -

cnztMapS :: (HomDistributiveDisjunctive h, t ~ Dual (Dual t))
  => h x y -> SDualBi (ConsecutiveZeroTrafo t n) x  -> SDualBi (ConsecutiveZeroTrafo t n) y
cnztMapS = vmapBi cnztMapCov cnztMapCov cnztMapCnt cnztMapCnt
  
--------------------------------------------------------------------------------
-- FunctorialG -

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
-- prpConsecutiveZeroTrafo -

prpConsecutiveZeroTrafo :: Distributive x => ConsecutiveZeroTrafo t n x -> Statement
prpConsecutiveZeroTrafo t@(ConsecutiveZeroTrafo a b _) = Prp "ConsecutiveZeroTrafo" :<=>:
  And [ valid a
      , valid b
      , valid $ cnztDiagramTrafo t
      ]

instance Distributive x => Validable (ConsecutiveZeroTrafo t n x) where
  valid = prpConsecutiveZeroTrafo


--------------------------------------------------------------------------------
-- ConsecutiveZeroTrafo - Algebraic -

type instance Point (ConsecutiveZeroTrafo t n x) = ConsecutiveZero t n x

instance (Show x, ShowPoint x) => ShowPoint (ConsecutiveZeroTrafo t n x)
instance (Eq x, EqPoint x) => EqPoint (ConsecutiveZeroTrafo t n x)
instance Distributive x => ValidablePoint (ConsecutiveZeroTrafo t n x)
instance (Typeable x, Typeable t, Typeable n) => TypeablePoint (ConsecutiveZeroTrafo t n x)

instance (Distributive x, Typeable t, Typeable n) => Oriented (ConsecutiveZeroTrafo t n x) where
  orientation (ConsecutiveZeroTrafo a b _) = a :> b

instance (Distributive x, Typeable t, Typeable n) => Multiplicative (ConsecutiveZeroTrafo t n x) where
  one c = ConsecutiveZeroTrafo c c $ amap1 one $ cnzPoints c

  ConsecutiveZeroTrafo y' z f * ConsecutiveZeroTrafo x y g
    | y == y'   = ConsecutiveZeroTrafo x z $ amap1 (uncurry (*)) (f `zip` g)
    | otherwise = throw NotMultiplicable 

type instance Root (ConsecutiveZeroTrafo t n x) = Orientation (ConsecutiveZero t n x)

instance (Show x, ShowPoint x) => ShowRoot (ConsecutiveZeroTrafo t n x)
instance (Eq x, EqPoint x) => EqRoot (ConsecutiveZeroTrafo t n x)
instance Distributive x => ValidableRoot (ConsecutiveZeroTrafo t n x)
instance (Typeable x, Typeable t, Typeable n) => TypeableRoot (ConsecutiveZeroTrafo t n x)

instance (Distributive x, Typeable t, Typeable n) => Fibred (ConsecutiveZeroTrafo t n x)
  
instance (Distributive x, Typeable t, Typeable n) => FibredOriented (ConsecutiveZeroTrafo t n x)

instance (Distributive x, Typeable t, Typeable n) => Additive (ConsecutiveZeroTrafo t n x) where
  zero (a :> b)
    = ConsecutiveZeroTrafo a b $ amap1 (zero . uncurry (:>)) (cnzPoints a `zip` cnzPoints b)

  ConsecutiveZeroTrafo a b f + ConsecutiveZeroTrafo a' b' g
    | a == a' && b == b' = ConsecutiveZeroTrafo a b $ amap1 (uncurry (+)) (f `zip` g)
    | otherwise          = throw NotAddable

instance (Distributive x, Abelian x, Typeable t, Typeable n)
  => Abelian (ConsecutiveZeroTrafo t n x) where
  negate (ConsecutiveZeroTrafo a b f) = ConsecutiveZeroTrafo a b $ amap1 negate f

  ConsecutiveZeroTrafo a b f - ConsecutiveZeroTrafo a' b' g
    | a == a' && b == b' = ConsecutiveZeroTrafo a b $ amap1 (uncurry (-)) (f `zip` g)
    | otherwise          = throw NotAddable
  
instance (Distributive x, Typeable t, Typeable n) => Distributive (ConsecutiveZeroTrafo t n x)

instance (Algebraic x, Typeable t, Typeable n) => Vectorial (ConsecutiveZeroTrafo t n x) where
  type Scalar (ConsecutiveZeroTrafo t n x) = Scalar x
  x ! ConsecutiveZeroTrafo a b f = ConsecutiveZeroTrafo a b $ amap1 (x!) f

instance (Algebraic x, Typeable t, Typeable n) => Algebraic (ConsecutiveZeroTrafo t n x)

--------------------------------------------------------------------------------
-- cnztHead -

-- | the first two arrows of the given 'ConsecutiveZeroTrafo'.
cnztHead :: Distributive x => ConsecutiveZeroTrafo t n x -> ConsecutiveZeroTrafo t N0 x
cnztHead (ConsecutiveZeroTrafo a b (f0:|f1:|f2:|_)) = ConsecutiveZeroTrafo (cnzHead a) (cnzHead b) (f0:|f1:|f2:|Nil)

--------------------------------------------------------------------------------
-- cnztTail -

-- | dropping the first arrow.
cnztTail :: Distributive x => ConsecutiveZeroTrafo t (n+1) x -> ConsecutiveZeroTrafo t n x
cnztTail (ConsecutiveZeroTrafo a b fs) = ConsecutiveZeroTrafo (cnzTail a) (cnzTail b) (tail fs)

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
    a <- amap1 ConsecutiveZero $ xTo n
    b <- amap1 ConsecutiveZero $ xTo n
    return $ ConsecutiveZeroTrafo a b $ amap1 (uncurry (:>)) $ (cnzPoints a `zip` cnzPoints b) 
  
  xcnztFrom :: Any n -> X (ConsecutiveZeroTrafo From n OS)
  xcnztFrom n = do
    a <- amap1 ConsecutiveZero $ xFrom n
    b <- amap1 ConsecutiveZero $ xFrom n
    return $ ConsecutiveZeroTrafo a b $ amap1 (uncurry (:>)) $ (cnzPoints a `zip` cnzPoints b) 
  
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
  

