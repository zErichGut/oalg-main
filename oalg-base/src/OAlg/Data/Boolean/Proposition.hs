
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : OAlg.Data.Boolean.Proposition
-- Description : propositions on boolean structures.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions on boolean structures which must always be true, i.e. tautologies. They
-- serve also to describe the semantic of the boolean operators.
module OAlg.Data.Boolean.Proposition
  ( prpBool, prpBoolTautologies
  
    -- * Tautologies
  , prpTautologies
    
    -- ** Not
  , prpNotNot

    -- ** And
  , prpAndAssoc, prpAndOr, prpAndTrue, prpAnd0, prpAnds

    -- ** Or
  , prpOrAssoc, prpOrAnd, prpOr0, prpOrs

    -- * Impl
  , prpImplRefl, prpImplFalseEverything, prpImplCurry, prpImplTransitive

    -- * Eqvl
  , prpEqvlAnd

    -- * Lazy
  , prpLazy, prpLazyAnd, prpLazyOr, prpLazyImpl
  )
  where

import Prelude(IO,undefined)

import Control.Monad

import Data.List(take,repeat)

import OAlg.Category.Definition

import OAlg.Data.Logical
import OAlg.Data.Canonical
import OAlg.Data.Number
import OAlg.Data.Boolean.Definition
import OAlg.Data.Statement.Definition
import OAlg.Data.X

--------------------------------------------------------------------------------
-- not -
-- | for all @p@ holds: @'not' ('not' p) '<~>' p@.
prpNotNot :: Boolean b => b -> b
prpNotNot p = not (not p) <~> p

--------------------------------------------------------------------------------
-- and -

-- | for all @a@, @b@ and @c@ holds: @(a '&&' b) '&&' c '<~>' a '&&' (b '&&' c)@.
prpAndAssoc :: Boolean b => b -> b -> b -> b
prpAndAssoc a b c = (a && b) && c <~> a && (b && c)

-- | for all @a@, @b@ and @c@ holds: @(a '&&' b) '||' c '<~>' (a '||' c) '&&' (b '||' c)@.
prpAndOr :: Boolean b => b -> b -> b -> b
prpAndOr a b c = (a && b) || c <~> (a || c) && (b || c)

-- | for all @p@ holds: @'true' '&&' p '<~>' p@.
prpAndTrue :: Boolean b => b -> b
prpAndTrue p = true && p <~> p

-- | @'and' [] '<~>' 'true'@.
prpAnd0 :: Boolean b => b
prpAnd0 = and [] <~> true

-- | for all @a@ and @as@ holds: @'and' (a':'as) '<~>' a '&&' 'and' as@.
prpAnds :: Boolean b => b -> [b] -> b
prpAnds a as = and (a:as) <~> a && and as

-- | substituting equivalent boolenas in '&&' yiels equivalent booleans, i.e.
--   @for all @(a,a')@ and @(b,b')@ holds:
--   (a '<~>' a') '&&' (b '<~>' b') '~>' ((a '&&' b) '<~>' (a' '&&' b'))@.
prpAndSubs :: Boolean b => (b,b) -> (b,b) -> b
prpAndSubs (a,a') (b,b') = (a <~> a') && (b <~> b') ~> ((a && b) <~> (a' && b'))

--------------------------------------------------------------------------------
-- Or -

-- | for all @a@, @b@ and @c@ holds: @(a '||' b) '||' c '<~>' a '||' (b '||' c)@.
prpOrAssoc :: Boolean  b => b -> b -> b -> b
prpOrAssoc a b c = (a || b) || c <~> a || (b || c)

-- | for all @a@, @b@ and @c@ holds: @(a '||' b) '&&' c '<~>' (a '&&' c) '||' (b '&&' c)@.
prpOrAnd ::  Boolean b => b -> b -> b -> b
prpOrAnd a b c = (a || b) && c <~> (a && c) || (b && c)

-- | for all @p@ holds:  @'false' '||' p '<~>' p@.
prpOrFalse :: Boolean b => b -> b
prpOrFalse p = false || p <~> p

-- | @'or' [] '<~>' 'false'@.
prpOr0 :: Boolean b => b
prpOr0 = or [] <~> false

-- | @for all @a@ and @as@ holds: 'or' (a':'as) '<~>' a '||' 'or' as@.
prpOrs :: Boolean b => b -> [b] -> b
prpOrs a as = or (a:as) <~> a || or as

--------------------------------------------------------------------------------
-- Impl -

-- | @for all @p@ holds: p '~>' p@.
prpImplRefl :: Boolean b => b -> b
prpImplRefl p = p ~> p

-- | for all @p@ holds: @'false' '~>' (p '<~>' 'true')@.
--
--   i.e. a false premisis implies everithing.
prpImplFalseEverything :: Boolean b => b -> b
prpImplFalseEverything p = false ~> (p <~> true)

-- | for all @a@, @b@ and @c@ holds: @((a '&&' b) '~>' c) '<~>' (a '~>' b '~>' c)@.
prpImplCurry :: Boolean b => b -> b -> b -> b
prpImplCurry a b c = ((a && b) ~> c) <~> (a ~> b ~> c)

-- | for all @a@, @b@ and @c@ holds: @(a '~>' b) '&&' (b '~>' c) '~>' (a '~>' c)@. 
prpImplTransitive :: Boolean b => b -> b -> b -> b
prpImplTransitive a b c = (a ~> b) && (b ~> c) ~> (a ~> c)

--------------------------------------------------------------------------------
-- Eqvl -

-- | for all @a@ and @b@ holds: @(a '<~>' b) '<~>' ((a '~>' b) && (b '~>' a))@.
prpEqvlAnd :: Boolean b => b -> b -> b
prpEqvlAnd a b = (a <~> b) <~> ((a ~> b) && (b ~> a))

--------------------------------------------------------------------------------
-- lazy -

-- | lazy evaluation of '&&', i.e. @'false' '&&' 'undefined' '<~>' 'false'@.
--
--  __Note__ @('undefined' '&&' 'false')@ evaluates to an exception!
prpLazyAnd :: Boolean b => b
prpLazyAnd = false && undefined <~> false

-- | lazy evaluationof '||', i.e. @'true' '||' 'undefined'@.
prpLazyOr :: Boolean b => b
prpLazyOr = true || undefined

-- | lazy evaluation of '~>', i.e. @'false' ':=>' 'undefined'@.
prpLazyImpl :: Boolean b => b
prpLazyImpl = false ~> undefined

--------------------------------------------------------------------------------
-- prpTautologies -

-- | tautologies on boolean structures.
prpTautologies :: Boolean b => (b -> Statement) -> X b -> X [b] -> Statement
prpTautologies prp xb xbs = Prp "Tautologies"
  :<=>: And [ -- Not
              Prp "NotNot" :<=>: Forall xb (prp . prpNotNot)

              -- And
            , Prp "AndAssoc" :<=>: Forall xabc (prp . (uncurry3 prpAndAssoc))
            , Prp "AndOr" :<=>: Forall xabc (prp . (uncurry3 prpAndOr))
            , Prp "AndTrue" :<=>: Forall xb (prp . prpAndTrue)
            , Prp "And0" :<=>: prp prpAnd0
            , Prp "Ands" :<=>: Forall xbbs (prp . (uncurry prpAnds))

              -- Or
            , Prp "OrAssoc" :<=>: Forall xabc (prp . (uncurry3 prpOrAssoc))
            , Prp "OrAnd" :<=>: Forall xabc (prp . (uncurry3 prpOrAnd))
            , Prp "OrFalse" :<=>: Forall xb (prp . prpOrFalse)
            , Prp "Or0" :<=>: prp prpOr0
            , Prp "Ors" :<=>: Forall xbbs (prp . (uncurry prpOrs))

              -- Impl
            , Prp "ImplRefl" :<=>: Forall xb (prp . prpImplRefl)
            , Prp "ImplFalseEverything" :<=>: Forall xb (prp . prpImplFalseEverything)
            , Prp "ImplCurry" :<=>: Forall xabc (prp . (uncurry3 prpImplCurry))
            , Prp "ImplTransitive" :<=>: Forall xabc (prp . (uncurry3 prpImplTransitive))

              -- Eqvl
            , Prp "EqvlAnd" :<=>: Forall xab (prp . (uncurry prpEqvlAnd))
            ]
  where xab  = xTupple2 xb xb
        xabc = xTupple3 xb xb xb
        xbbs = xTupple2 xb xbs

--------------------------------------------------------------------------------
-- prpBoolTautologies -

-- | tautologies for 'Bool'.
prpBoolTautologies :: Statement
prpBoolTautologies = Prp "BoolTautologies"
  :<=>: prpTautologies inj xBool (xTakeB 0 10 xBool)
  
--------------------------------------------------------------------------------
-- prpLazy -

-- | laziness of 'and', 'or' and @('~>')@.
prpLazy :: Boolean b => (b -> Statement) -> Statement
prpLazy prp = Prp "Lazy"
  :<=>: And [ Prp "LazyAnd" :<=>: prp prpLazyAnd
            , Prp "LazyOr" :<=>: prp prpLazyOr
            , Prp "LazyImpl" :<=>: prp prpLazyImpl
            ]
  
xbDst :: Int -> X Bool -> IO ()
xbDst n xb = getOmega >>= putDistribution n xb

xabDst :: Int -> X Bool -> IO ()
xabDst n xb = getOmega >>= putDistribution n xab where
  xab = xTupple2 xb xb

xabcDst :: Int -> X Bool -> IO ()
xabcDst n xb = getOmega >>= putDistribution n xabc where
  xabc = xTupple3 xb xb xb

xbbsDst :: Int -> Int -> X Bool -> IO ()
xbbsDst n m xb = getOmega >>= putDistribution n xbbs where
  xbs  = xIntB 0 m >>= \n' -> xList $ take n' $ repeat xb
  xbbs = xTupple2 xb xbs

--------------------------------------------------------------------------------
-- prpBool -

-- | validity of the 'Boolean' structure of 'Bool'.
prpBool :: Statement
prpBool = Prp "Bool"
  :<=>: And [ prpBoolTautologies
            , prpLazy (inj :: Bool -> Statement)
            ]

