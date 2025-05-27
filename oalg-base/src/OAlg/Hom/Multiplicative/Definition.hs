

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}


-- |
-- Module      : OAlg.Hom.Multiplicative.Definition
-- Description : definition of homomorphisms between multiplicative structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of homomorphisms between 'Multiplicative' structures.
module OAlg.Hom.Multiplicative.Definition
  (
{-
    -- * Multiplicative
    HomMultiplicative, IsoMultiplicative

    -- * Duality
  , SDualityMultiplicative

    -- * OpHom
  -- , toOpHomMlt
  , isoToOpOpMlt, isoFromOpOpMlt
  -- , isoOppositeMlt
-}
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

-- this modules are imported to make the description easier
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- HomMultiplicative -

-- | covariant homomorphisms between 'Multiplicative' structures.
--
-- __Propoerty__ Let @'HomMultiplicative' __h__@, then
-- for all __@a@__, __@b@__ and @h@ in __@h@__ __@a@__ __@b@__ holds:
--
-- (1) For all @p@ in @'Point' __a__@ holds:
--     @'amap' h ('one' p) '==' 'one' ('pmap' h p)@.
--
-- (2) For all @x@, @y@ in __@a@__ with @'start' x '==' 'end' y@ holds:
--     @'amap'h (x '*' y) '==' 'amap' h x '*' 'amap' h y@.
class (HomOriented h, Transformable (ObjectClass h) Mlt) => HomMultiplicative h

instance HomMultiplicative h => HomMultiplicative (Path h)

--------------------------------------------------------------------------------
-- HomDisjunctiveMultiplicative -

-- | disjunctive homomorphisms between 'Multiplicative' structures.
--
-- __Propoerty__ Let @'HomDisjunctiveMultiplicative' __h__@, then
-- for all __@a@__, __@b@__ and @h@ in __@h@__ __@a@__ __@b@__ holds:
--
-- (1) If @'variant2' h '==' 'Covariant'@ then holds:
--
--     (1) For all @p@ in @'Point' __a__@ holds:
--     @'amap' h ('one' p) '==' 'one' ('pmap' h p)@.
--
--     (2) For all @x@, @y@ in __@a@__ with @'start' x '==' 'end' y@ holds:
--     @'amap' h (x '*' y) '==' 'amap' h x '*' 'amap' h y@.
--
-- (2) If @'variant2' h '==' 'Contravariant'@ then holds:
--
--     (1) For all @p@ in @'Point' __a__@ holds:
--     @'amap' h ('one' p) '==' 'one' ('pmap' h p)@.
--
--     (2) For all @x@, @y@ in __@a@__ with @'start' x '==' 'end' y@ holds:
--     @'amap' h (x '*' y) '==' 'amap' h y '*' 'amap' h x@.
class (HomDisjunctiveOriented h, Transformable (ObjectClass h) Mlt) => HomDisjunctiveMultiplicative h

--------------------------------------------------------------------------------
-- SDualisableMultiplicative -

-- | duality according to @__o__@ on @__s__@-structured 'Multiplicative' types,
--
-- __Properties__ Let @'SDualisableMultiplicative' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) For all @p@ in @'Point' __x__@ holds:
-- @'toDualArw' q s ('one' p) '==' 'one' ('toDualPnt' q s p)@. 
--
-- (2) For all @x@, @y@ in @__x__@ with @'start' x '==' 'end' y@ holds:
-- @'toDualArw' q s (x '*' y) '==' 'toDualArw' q s y '*' 'toDualArw' q s x@.
--
-- where @q@ is any proxy for @__o__@.
class (SDualisableOriented s o, Transformable s Mlt) => SDualisableMultiplicative s o

--------------------------------------------------------------------------------
-- prpSDualisableMultiplicativeOne -

relSDualisableMultiplicativeOne :: SDualisableMultiplicative s o
  => q o -> Struct s x -> Struct Mlt x -> Struct Mlt (o x) -> X (Point x) -> Statement
relSDualisableMultiplicativeOne q s Struct Struct xp = Forall xp
  (\p -> (tArw (one p) == one (tPnt p)) :?> Params ["p":=show p])
  where tArw = toDualArw q s
        tPnt = toDualPnt q s

-- | validity according to 'SDualisableMultiplicative', property 1.
prpSDualisableMultiplicativeOne :: SDualisableMultiplicative s o
  => q o -> Struct s x -> X (Point x) -> Statement
prpSDualisableMultiplicativeOne q s xp = Prp "SDualisableMultiplicativeOne" :<=>: 
  relSDualisableMultiplicativeOne q s (tau s) (tau (tauO s)) xp

  
