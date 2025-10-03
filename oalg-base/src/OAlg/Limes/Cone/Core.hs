
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.Core
-- Description : basic definitions for cones
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- basic definition of 'Cone's over 'Diagrammatic' objects.
module OAlg.Limes.Cone.Core
  (
    -- * Cone
    Cone(..), diagrammaticObject, coneDiagram
  , Perspective(..), cnMltOrDst, coneStruct
  , cnDiagramTypeRefl
  , tip, shell, cnArrows, cnPoints
  
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.NaturalTransformable

import OAlg.Data.Either

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Limes.Perspective

import OAlg.Limes.Cone.Structure

--------------------------------------------------------------------------------
-- Cone -

-- | cone over a diagram.
--
-- __Properties__ Let @c@ be in @'Cone' __s__ __p__ __d__ __t__ __n__ __m__ __a__@ for a
-- 'Diagrammatic' @__d__@, then holds:
--
-- (1) If @c@ matches @'ConeProjective' d t cs@ for a 'Multiplicative' structure __@a@__
-- then holds:
--
--     (1) For all @ci@ in @cs@ holds: @'start' ci '==' t@ and
--     @'end' ci '==' pi@ where @pi@ in @'dgPoints' ('diagram' d)@.
--
--     (2) For all @aij@ in @'dgArrows' ('diagram' d)@ holds: @aij 'Mlt.*' ci '==' cj@
--     where @ci@, @cj@ in @cs@.
--
-- (2) If @c@ matches @'ConeInjective' d t cs@ for a 'Multiplicative' structure __@a@__
-- then holds: 
--
--     (1) For all @ci@ in @cs@ holds: @'end' ci '==' t@ and
--     @'start' ci '==' pi@ where @pi@ in @'dgPoints' ('diagram' d)@.
--
--     (2) For all @aij@ in @'dgArrows' ('diagram' d)@ holds: @cj 'Mlt.*' aij '==' ci@
--     where @ci@, @cj@ in @cs@.
--
-- (3) If @c@ matches @'ConeKernel' p k@ for a 'Distributive' structure __@a@__ then holds:
--
--     (1) @'end' k '==' p0@ where @p0@ in @'dgPoints' ('diagram' p)@
--
--     (2) For all @a@ in @'dgArrows' ('diagram' p)@ holds: @a 'Mlt.*' k '==' 'zero' (t ':>' p1)@
--     where @t = 'start' k@ and @p0@, @p1@ in @'dgPoints' ('diagram' p)@.
--
-- (4) If @c@ matches @'ConeCokernel' p k@ for a 'Distributive' structure __@a@__ then
-- holds:
--
--     (1) @'start' k '==' p0@ where @p0@ in @'dgPoints' ('diagram' p)@
--
--     (2) For all @a@ in @'dgArrows' ('diagram' p)@ holds: @k 'Mlt.*' a '==' 'zero' (p1 ':>' t)@
--     where @t = 'end' k@ and @p0@, @p1@ in @'dgPoints' ('diagram' p)@.
--
-- __Note__
--
-- (1) Let @'OAlg.Hom.Multiplicative.HomMultiplicativeDisjunctive' __h__@ and
-- @'NaturalDiagrammatic' __h d t n m__@,then holds:
-- @'NaturalTransformable' __h__ (->) ('DiagramG' __d t n m__) ('Diagram' __t n m__)@
-- (as required by the definition of @'NaturalDiagrammatic' __h d t n m__@)
-- and
-- @'NaturalTransformable' __h__ (->) ('Cone' 'Mlt' __p d t n m__) ('DiagramG' __d t n m__)@
-- (see comment in source code of its instance declaration and the property of 'dmap')
-- and therefore this establish a natural
-- transformation according to @__h__@ from @'Cone' 'Mlt' __p d t n m__@ to @'Diagram' __t n m__@.
--
-- (2) The same holds for @'OAlg.Hom.Multiplicative.HomMultiplicativeDisjunctive' __h__@ and
-- @'Cone' 'Dst' __p d t n m__@.
data Cone s (p :: Perspective) d (t :: DiagramType) (n :: N') (m :: N') a where
  ConeProjective :: Multiplicative a
    => d t n m a -> Point a -> FinList n a -> Cone Mlt Projective d t n m a
  ConeInjective  :: Multiplicative a
    => d t n m a -> Point a -> FinList n a -> Cone Mlt Injective d t n m a
  ConeKernel     :: Distributive a
    => d (Parallel LeftToRight) N2 m a -> a
    -> Cone Dst Projective d (Parallel LeftToRight)  N2 m a
  ConeCokernel   :: Distributive a
    => d (Parallel RightToLeft) N2 m a -> a
    -> Cone Dst Injective d (Parallel RightToLeft) N2 m a

deriving instance Show (d t n m a) => Show (Cone s p d t n m a)
deriving instance Eq (d t n m a) => Eq (Cone s p d t n m a)

--------------------------------------------------------------------------------
-- coneStruct -

-- | the associated 'ConeStruct'.
coneStruct :: Cone s p d t n m a -> ConeStruct s a
coneStruct (ConeProjective _ _ _) = ConeStructMlt
coneStruct (ConeInjective _ _ _)  = ConeStructMlt
coneStruct (ConeKernel _ _)       = ConeStructDst
coneStruct (ConeCokernel _ _)     = ConeStructDst

--------------------------------------------------------------------------------
-- cnMltOrDst -

-- | proof of @__s__@ being either 'Mlt' or 'Dst'.
cnMltOrDst :: Cone s p d t n m a -> Either (s :~: Mlt) (s :~: Dst)
cnMltOrDst = cnStructMltOrDst . coneStruct

--------------------------------------------------------------------------------
-- diagrammaticObject -

-- | the underlying 'Diagrammatic' object.
diagrammaticObject :: Cone s p d t n m a -> d t n m a
diagrammaticObject (ConeProjective d _ _) = d
diagrammaticObject (ConeInjective d _ _)  = d
diagrammaticObject (ConeKernel d _)       = d
diagrammaticObject (ConeCokernel d _)     = d

--------------------------------------------------------------------------------
-- cdroh -

-- | the diagrammatic object as generalized diagram.
cdroh :: Cone s p d t n m x -> DiagramG d t n m x
cdroh = DiagramG . diagrammaticObject

instance Natural r (->) (Cone s p d t n m) (DiagramG d t n m) where
  roh _ = cdroh

--------------------------------------------------------------------------------
-- cnDiagramTypeRefl -

-- | reflexivity of the underlying diagram type.
cnDiagramTypeRefl :: Diagrammatic d => Cone s p d t n m a -> Dual (Dual t) :~: t
cnDiagramTypeRefl = dgTypeRefl . diagram . diagrammaticObject

--------------------------------------------------------------------------------
-- cnTypeRefl -

cnTypeRefl :: Cone s p d t n m a -> Dual (Dual p) :~: p
cnTypeRefl (ConeProjective _ _ _) = Refl
cnTypeRefl (ConeInjective _ _ _)  = Refl
cnTypeRefl (ConeKernel _ _)       = Refl
cnTypeRefl (ConeCokernel _ _)     = Refl

--------------------------------------------------------------------------------
-- coneDiagram -

-- | mapping a 'Diagrammatic'-'Cone' to a 'Diagram'-'Cone'.
coneDiagram :: Diagrammatic d => Cone s p d t n m a -> Cone s p Diagram t n m a
coneDiagram (ConeProjective d t s) = ConeProjective (diagram d) t s
coneDiagram (ConeInjective d t s)  = ConeInjective (diagram d) t s
coneDiagram (ConeKernel d k)       = ConeKernel (diagram d) k
coneDiagram (ConeCokernel d k)     = ConeCokernel (diagram d) k

--------------------------------------------------------------------------------
-- tip -

-- | the tip of a cone.
--
-- __Property__ Let @c@ be in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ for a
-- 'Oriented' structure then holds:
--
-- (1) If __@p@__ is equal to __'Projective'__ then holds:
-- @'start' ci '==' 'tip' c@ for all @ci@ in @'shell' c@.
--
-- (2) If __@p@__ is equal to __'Injective'__ then holds:
-- @'end' ci '==' 'tip' c@ for all @ci@ in @'shell' c@.
tip :: Cone s p d t n m a -> Point a
tip c = case c of
  ConeProjective _ t _ -> t
  ConeInjective _ t _  -> t
  ConeKernel _ k       -> start k
  ConeCokernel _ k     -> end k

--------------------------------------------------------------------------------
-- shell -

-- | the shell of a cone.
--
-- __Property__ Let @c@ be in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ for a
-- 'Oriented' structure then holds:
--
-- (1) If __@p@__ is equal to __'Projective'__ then holds:
-- @'amap' 'end' ('shell' c) '==' 'cnPoints' c@.
--
-- (2) If __@p@__ is equal to __'Injective'__ then holds:
-- @'amap' 'start' ('shell' c) '==' 'cnPoints' c@.
shell :: Diagrammatic d => Cone s p d t n m a -> FinList n a
shell (ConeProjective _ _ as) = as
shell (ConeInjective _ _ as)  = as
shell (ConeKernel d k)        = k:|zero (start k :> q):|Nil where DiagramParallelLR _ q _ = diagram d
shell (ConeCokernel d k)      = k:|zero (q :> end k):|Nil where DiagramParallelRL _ q _ = diagram d

--------------------------------------------------------------------------------
-- cnPoints -

-- | the points of the underlying diagram.
cnPoints :: (Diagrammatic d, Oriented a) => Cone s p d t n m a -> FinList n (Point a)
cnPoints = dgPoints . diagrammaticObject . coneDiagram

--------------------------------------------------------------------------------
-- cnArrows -

-- | the arrows of the underlying diagram.
cnArrows :: Diagrammatic d => Cone s p d t n m a -> FinList m a
cnArrows = dgArrows . diagrammaticObject . coneDiagram
