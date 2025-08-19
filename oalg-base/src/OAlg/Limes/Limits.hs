
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- {-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : OAlg.Limes.Limits
-- Description : limits of diagrams
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- 'Limits' of 'Diagram's, i.e. assigning to each diagram a 'Limes' over the given diagram.
module OAlg.Limes.Limits
  (

    -- * Limits
    Limits(..)
  , lmsMapS, lmsMapCov, lmsMapCnt

{-
    -- * Duality
  , lmsToOp, lmsFromOp
  , coLimits, coLimitsInv, lmsFromOpOp

    -- * Construction
  , lmsToPrjOrnt, lmsFromInjOrnt
  
    -- * Proposition
  , prpLimits, prpLimitsDiagram
-}
  ) where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either

-- import OAlg.Structure.Oriented
-- import OAlg.Structure.Multiplicative
-- import OAlg.Structure.Distributive

import OAlg.Hom.Oriented

import OAlg.Entity.Diagram
-- import OAlg.Entity.Natural

import OAlg.Limes.Cone
import OAlg.Limes.Definition

--------------------------------------------------------------------------------
-- Limits -

-- | limes of a diagrammatic object, i.e. assigning to each diagrammatic object @d@ a limes over the
-- @d@.
--
-- __Property__ Let @l@ be in @'Limits' __c s p d t n m x__@ for a @'Conic' __c__@ and a
-- @'Diagrammatic' __d__@, then holds:
--
-- (1) @'diagram' '.' 'cone' '.' 'universalCone' '.' 'limes' l '.=.' 'diagram'@.
newtype Limits c s p d t n m x = Limits (d t n m x -> Limes c s p d t n m x)

--------------------------------------------------------------------------------
-- limes -

-- | the limes over the given diagram.
limes :: Limits c s p d t n m x -> d t n m x -> Limes c s p d t n m x
limes (Limits l) = l

--------------------------------------------------------------------------------
-- Limits - Dual -

type instance Dual1 (Limits c s p d t n m) = Limits c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- lmsMapCov -

lmsMapCov :: NaturalConic h c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> Limits c s p d t n m x -> Limits c s p d t n m y
lmsMapCov i@(Covariant2 (Inv2 _ f)) (Limits u) = Limits u' where
  u' d' = lmMapCov i (u d) where
    SDualBi (Right1 (DiagramG d)) = amap1 f (SDualBi (Right1 (DiagramG d'))) 

--------------------------------------------------------------------------------
-- lmsMapCnt -

lmsMapCnt :: NaturalConic h c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> Limits c s p d t n m x -> Dual1 (Limits c s p d t n m) y
lmsMapCnt i@(Contravariant2 (Inv2 _ f)) (Limits u) = Limits u' where
  u' d' = lmMapCnt i (u d) where
    SDualBi (Right1 (DiagramG d)) = amap1 f (SDualBi (Left1 (DiagramG d'))) 

--------------------------------------------------------------------------------
-- lmsMapS -

lmsMapS ::
  ( CategoryDisjunctive h
  , NaturalConicBi h c s p d t n m
  )
  => Inv2 h x y -> SDualBi (Limits c s p d t n m) x -> SDualBi (Limits c s p d t n m) y
lmsMapS = vmapBi lmsMapCov lmsMapCov lmsMapCnt lmsMapCnt

--------------------------------------------------------------------------------
-- Limits - FunctorialG -

instance
  ( CategoryDisjunctive h
  , NaturalConicBi h c s p d t n m
  )
  => ApplicativeG (SDualBi (Limits c s p d t n m)) (Inv2 h) (->) where
  amapG = lmsMapS

instance
  ( CategoryDisjunctive h
  , NaturalConicBi h c s p d t n m
  )
  => FunctorialG (SDualBi (Limits c s p d t n m)) (Inv2 h) (->)  






{-
--------------------------------------------------------------------------------
-- lmsMap -

lmsMap :: NaturalConic h c s p d t n m
  => Inv2 h x y -> Limits c s p d t n m x -> Limits c s p d t n m y
lmsMap i@(Inv2 _ f) (Limits l) = Limits (amapG i . l . dmap f )
-}








{-
--------------------------------------------------------------------------------
-- lmsMap -

-- | mapping of limits.
lmsMap :: UniversalApplicative h l s
  => h a b -> Limits l s p t n m a -> Limits l s p t n m b
lmsMap h (Limits ls) = Limits (ls' h ls) where
  ls' h ls d' = umap h $ ls $ dgMap h' d' where h' = invert2 h 

--------------------------------------------------------------------------------
-- Limits - Applicative1 -

instance UniversalApplicative h l s => Applicative1 h (Limits l s p t n m) where
  amap1 = lmsMap


--------------------------------------------------------------------------------
-- Limits - Daul -

type instance Dual (Limits l s p t n m a) = Limits l s (Dual p) (Dual t) n m (Op a)

--------------------------------------------------------------------------------
-- coLimits -

-- | the co limits wit its inverse 'coLimitsInv'.
coLimits :: OpDualisable c l s
  => c s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Limits l s p t n m a -> Dual (Limits l s p t n m a)
coLimits cs rp rt (Limits lm) = Limits lm' where
  lm' d' = case opdStructMlt cs of Struct -> opdToOp cs (OpDuality rp rt) $ lm $ coDiagramInv rt d'

--------------------------------------------------------------------------------
-- lmsFromOpOp -

-- | from the bidual.
lmsFromOpOp :: (OpReflexive c s, UniversalApplicative (IsoOp s) l s)
  => c s a -> Limits l s p t n m (Op (Op a)) -> Limits l s p t n m a
lmsFromOpOp cs = amap1 (invert2 $ opdRefl cs)

--------------------------------------------------------------------------------
-- coLimitsInv -

-- | from the co limits, with its inverse of 'coLimits'.
coLimitsInv :: ( OpDualisable c l s
               , UniversalApplicative (IsoOp s) l s
               )
  => c s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (Limits l s p t n m a) -> Limits l s p t n m a
coLimitsInv cs Refl Refl lms'
  = lmsFromOpOp cs $ coLimits (opdStructOp cs) Refl Refl lms'

--------------------------------------------------------------------------------
-- lmsToOp -

-- | to @__f'__ ('Op' __a__)@.
lmsToOp :: OpDualisable c l s => c s a -> OpDuality (Limits l) s x y -> x a -> y (Op a)
lmsToOp cs (OpDuality rp rt) = coLimits cs rp rt

--------------------------------------------------------------------------------
-- lmsFromOp -

-- | from @__f'__ ('Op' __a__)@.
lmsFromOp :: ( OpDualisable c l s
             , UniversalApplicative (IsoOp s) l s
             )
  => c s a -> OpDuality (Limits l) s x y -> y (Op a) -> x a
lmsFromOp cs (OpDuality rp rt) = coLimitsInv cs rp rt

--------------------------------------------------------------------------------
-- Limits - OpDualisable -

-- needs UndecidableInstances to compile!  -- needs UndecidableInstances to compile!
instance ( OpDualisable c l s
         , UniversalApplicative (IsoOp s) l s
         )
  => OpDualisable c (Limits l) s where
  opdToOp   = lmsToOp
  opdFromOp = lmsFromOp

--------------------------------------------------------------------------------
-- prpLimitsDiagram -

-- | validity according to 'Limits'.
prpLimitsDiagram :: (OpReflexive c s, Universal l, Show (l s p t n m a))
  => c s a -> XOrtPerspective p a
  -> Limits l s p t n m a -> Diagram t n m a 
  -> Statement
prpLimitsDiagram cs xop lms d = Prp "LimesDiagram"
  :<=>: And [ case opdStructMlt cs of
                Struct -> (diagram (universalCone lm) == d) :?> Params["d":=show d,"lm":=show lm]
            , relUniversal (opdConeStruct cs) xop lm
            ]
  where lm = limes lms d

--------------------------------------------------------------------------------
-- prpLimits -

-- | validity according to 'Limits', relative to the given random variable for 'Diagram's. 
prpLimits :: (OpReflexive c s, Universal l, Show (l s p t n m a))
  => c s a -> Limits l s p t n m a
  -> X (Diagram t n m a) -> XOrtPerspective p a -> Statement
prpLimits cs lms xd xop = Prp "Limits"
  :<=>: Forall xd (prpLimitsDiagram cs xop lms)


instance ( Multiplicative a
         , Universal l, Show (l Mlt p t n m a)
         , XStandard (Diagram t n m a), XStandardOrtPerspective p a
         )
  => Validable (Limits l Mlt p t n m a) where
  valid lm = prpLimits ConeStructMlt lm xStandard xStandardOrtPerspective

instance ( Distributive a
         , Universal l, Show (l Dst p t n m a)
         , XStandard (Diagram t n m a), XStandardOrtPerspective p a
         )
  => Validable (Limits l Dst p t n m a) where
  valid lm = prpLimits ConeStructDst lm xStandard xStandardOrtPerspective

--------------------------------------------------------------------------------
-- lmsToPrjOrnt -

-- | projective limits for @'Orientation' __p__@.
lmsToPrjOrnt :: Entity p => p -> Limits Limes Mlt Projective t n m (Orientation p)
lmsToPrjOrnt = Limits . lmToPrjOrnt

--------------------------------------------------------------------------------
-- lmsFromInjOrnt -

-- | injective limits for @'Orientation' __p__@.
lmsFromInjOrnt :: Entity p => p -> Limits Limes Mlt Injective t n m (Orientation p)
lmsFromInjOrnt = Limits . lmFromInjOrnt  

-}
