
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Adjunction.Definition
-- Description : definition of adjunctions between multiplicative structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of adjunctions between 'Multiplicative' structures. We relay on the terms and notation as
-- used in [nLab](http://ncatlab.org/nlab/show/adjoint+functor)
module OAlg.Adjunction.Definition
  (
{-    
    -- * Adjunction
    Adjunction(..), unitr, unitl, adjl, adjr, adjHomMlt

    -- * Dual
  , coAdjunction

    -- * Proposition
  , prpAdjunction, prpAdjunctionRight, prpAdjunctionLeft
-}
  ) where

import OAlg.Prelude

import OAlg.Data.Proxy

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom

--------------------------------------------------------------------------------
-- Adjunction -

-- | adjunction between two multiplicative structures @__d__@ and @__c__@ according
--   two given multiplicative homomorphisms @l :: __h c d__@ and
--   @r :: __h d c__@.  
--
-- @
--              l
--          <------- 
--        d          c
--          -------->
--              r
-- @
--
--  __Property__ Let @'Adjunction' l r u v@ be in @'Adjunction' __h d c__@ where
--  @__h__@ is a 'Mlt'-homomorphism,
--  then holds:
--
--  (1) Naturality of the right unit @u@:
--
--      (1) For all @x@ in @'Point' __c__@ holds:
--      @'orientation' (u x) '==' x ':>' 'pmap' r ('pmap' l x)@.
--
--      (2) For all @f@ in @__c__@ holds:
--      @u ('end' f) '*' f '==' 'amap' r ('amap' l) f '*' u ('start' f)@.
--
--  (2) Naturality of the left unit @v@:
--
--      (1) For all @y@ in @'Point' __d__@ holds:
--      @'orientation' (v y) '==' 'pmap' l ('pmap' r y) ':>' y@.
--
--      (2) For all @g@ in @__d__@ holds:
--      @g '*' v ('start' g) '==' v ('end' g) '*' 'amap' l ('amap' r) g@.
--
--  (3) Triangle identities:
--
--      (1) For all @x@ in @'Point' __c__@ holds:
--      @'one' ('pmap' l x) == v ('pmap' l x) '*' 'amap' l (u x)@. 
--
--      (2) For all @y@ in @'Point' __d__@ holds:
--      @'one' ('pmap' r y) == 'amap' r (v y) '*' u ('pmap' r y)@.
--
--  The following diagrams illustrate the above equations
--
--  naturality of the right unit @u@ (Equations 1.1 and 1.2):
--
-- @
--         u a
--     a -------> pmap r (pmap l a)         
--     |                |
--   f |                | amap r (amap l f)
--     v                v
--     b -------> pmap r (pmap l b)
--         u b
--
-- @
--
--  naturality of the left unit @v@ (Equations 2.1 and 2.2):
--
-- @
--         v a
--    a <------- pmap l (pmap r a)
--    |                |
--  g |                | amap l (ampa r g)
--    v                v
--    b <------ pmap l (pmap r b)
--         v b
-- @
--
--  the left adjoint of the right unit @u@ is 'one' (Equation 3.1, see 'adjl'):
--
-- @
--                                  pmap l x         x
--                                 /   |             |
--                                /    |             |
--                               /     |             |
--                 amap l (u x) /      | one  ~  u x |    
--                             /       |             |
--                            /        |             |
--                           v         v             v
--  pmap l (pmap r (pmap l x)) ---> pmap l x    pmap r (pmap l x)
--                         v (pmap l x)
-- @
--
-- the right adjoint of the left unit @v@ is 'one' (Equation 3.2, see 'adjr'):
--
-- @
--                             u (pmap r y)
--  pmap l (pmap r y)     pmap r y ---> pmap r (pmap l (pmap r y))
--        |                  |         /
--        |                  |        /
--        | v y    ~     one |       / amap r (v y)
--        |                  |      /
--        |                  |     /
--        v                  v    v
--        y               pmap r y
-- @
data Adjunction h d c where
  Adjunction
    :: h c d -- ^ the homomorphism from right to left.
    -> h d c -- ^ the homomorphism from left to right.
    -> (Point c -> c) -- ^ the unit on the right side.
    -> (Point d -> d) -- ^ the unit on the left side.
    -> Adjunction h d c

--------------------------------------------------------------------------------
-- unitr -

-- | the unit on the right side.
unitr :: Adjunction h d c -> Point c -> c
unitr (Adjunction _ _ u _) = u

--------------------------------------------------------------------------------
-- unitl -

-- | the unit on the left side.
unitl :: Adjunction h d c -> Point d -> d
unitl (Adjunction _ _ _ v) = v

--------------------------------------------------------------------------------
-- adjr -

-- | the right adjoint @g'@ of a factor in @g@ in @__d__@
--
--  __Property__ Let @x@ be in @__c__@ and @g@ in @__d__@ with @'start' g '==' 'pmap' l x@
--  then the right adjoint @g'@ of @g@ is given by @g' = 'amap' r g '*' u x@.
--
--
-- @
--                             u x
--       pmap l x           x -----> pmap r (pmap l x)
--          |               |       /
--          |               |      /
--          |               |     /
--          | g     ~    g' |    / amap r g
--          |               |   /
--          |               |  /
--          v               v v
--          y            pmap r y
-- @
adjr :: Hom Mlt h => Adjunction h d c -> Point c -> d -> c
adjr adj@(Adjunction _ r _ _) = adjrStruct adj (tau (range r)) where
  adjrStruct :: Hom Mlt h
    => Adjunction h d c -> Struct Mlt c -> Point c -> d -> c
  adjrStruct (Adjunction _ r u _) Struct x f = amap r f * u x


-- | the left adjoint @f'@ of a factor @f@ in @__c__@.
--
-- __Property__ Let @y@ be in @__d__@ and @f@ in @__c__@ with @'end' f '==' 'pmap' r y@
-- then the left adjoint @f'@ of @f@ is given by @f' = v y '*' 'amap' l f@.
--
--
-- @
--                      pmap l x           x
--                       /   |             |
--                      /    |             |
--                     /     |             |
--           amap l f /      | f'   ~    f |
--                   /       |             |
--                  /        |             |
--                 v         v             v
--  pmap l (pmap r y) -----> y          pmap r y
--                      v y
-- @
adjl :: Hom Mlt h => Adjunction h d c -> Point d -> c -> d
adjl adj@(Adjunction l _ _ _) = adjlStruct adj (tau (range l)) where
  adjlStruct :: Hom Mlt h
    => Adjunction h d c -> Struct Mlt d -> Point d -> c -> d
  adjlStruct (Adjunction l _ _ v) Struct y f = v y * amap l f

--------------------------------------------------------------------------------
-- adjHomMlt -

-- | attest of being 'Multiplicative' homomorphous.
adjHomMlt :: Hom Mlt h => Adjunction h d c -> Homomorphous Mlt d c
adjHomMlt (Adjunction _ r _ _) = tauHom (homomorphous r)

--------------------------------------------------------------------------------
-- adjHomDisj -

-- | the induce adjunction.
adjHomDisj ::
  ( HomMultiplicative h
  , Transformable (ObjectClass h) s
  )
  => Adjunction h x y -> Adjunction (Variant2 Covariant (HomDisj s o h)) x y
adjHomDisj (Adjunction l r u v) = Adjunction (homDisj l) (homDisj r) u v

--------------------------------------------------------------------------------
-- adjMapCnt -

adjMapCnt ::
  ( HomMultiplicativeDisjunctive h -- haskell type checker identifies it as reduntant, but it is needed!
  , FunctorialOriented h
  )
  => Variant2 Contravariant (Inv2 h) x x'
  -> Variant2 Contravariant (Inv2 h) y y'
  -> Adjunction (Variant2 Covariant h) x y -> Adjunction (Variant2 Covariant h) y' x'
adjMapCnt (Contravariant2 (Inv2 tx fx)) (Contravariant2 (Inv2 ty fy))
  (Adjunction (Covariant2 l) (Covariant2 r) u v) = Adjunction l' r' u' v' where

  l' = Covariant2 (ty . r . fx) 
  r' = Covariant2 (tx . l . fy)
  u' = amapf tx . v . pmapf fx
  v' = amapf ty . u . pmapf fy

--------------------------------------------------------------------------------
-- Duality -

type instance Dual (Adjunction h x y)
  = Adjunction (Variant2 Covariant (HomDisj Mlt Op h)) (Op y) (Op x)

--------------------------------------------------------------------------------
-- coAdjunction -

coAdjunctionStruct ::
  ( HomMultiplicative h
  , Transformable (ObjectClass h) s
  , TransformableGRefl o s
  , DualisableMultiplicative s o
  )
  => Homomorphous s x y
  -> Adjunction h x y -> Adjunction (Variant2 Covariant (HomDisj s o h)) (o y) (o x)
coAdjunctionStruct (sx:>:sy) adj = adjMapCnt (isoHomDisj sx) (isoHomDisj sy) (adjHomDisj adj)

coAdjunctionOp :: HomMultiplicative h => Adjunction h x y -> Dual (Adjunction h x y)
coAdjunctionOp a = coAdjunctionStruct (adjHomMlt a) a 


{-  
coAdjunction sx sy a = Adjunction l' r' u' v' where
  Adjunction (Covariant2 l) (Covariant2 r) u v = adjHomDisj a

  qh :: HomDisj s o h x y -> Proxy h
  qh _ = Proxy
  
  l' = Covariant2 (t . r . f) where  -- r :: HomDisj s o h x y, l' :: HomDisj s o h (o x) (o y)
         Contravariant2 (Inv2 _ f) = isoHomDisj sx
         Contravariant2 (Inv2 t _) = isoHomDisj sy
        
  r' = Covariant2 (t . l . f) where  -- l :: HomDisj s o h y x, r' :: HomDisj s o h (o y) (o x)
         Contravariant2 (Inv2 _ f) = isoHomDisj sy
         Contravariant2 (Inv2 t _) = isoHomDisj sx
         
  u' = amap t . v . pmap f where     -- u' :: Point (o x) -> o x, v :: Point x -> x
         Contravariant2 (Inv2 t f) = isoHomDisj' (qh l) sx

  v' = amap t . u . pmap f where     -- v' :: Point (o y) -> o y, u :: Point y -> y
         Contravariant2 (Inv2 t f) = isoHomDisj' (qh l) sy
-}
{-
--------------------------------------------------------------------------------
-- Adjunction - Duality -

type instance Dual (Adjunction h d c) = Adjunction (OpHom h) (Op c) (Op d)


-- | the dual adjunction.
coAdjunction :: Hom Mlt h => Adjunction h d c -> Dual (Adjunction h d c)
coAdjunction (Adjunction l r u v)
  = Adjunction (OpHom r) (OpHom l) (coUnit v) (coUnit u) where

  coUnit :: (Point x -> x) -> Point (Op x) -> Op x
  coUnit u = Op . u

--------------------------------------------------------------------------------
-- relAdjunctionRightUnit -

relAdjunctionRightUnitHom :: (Hom Mlt h, Show2 h)
  => Homomorphous Mlt d c -> Adjunction h d c -> Point c -> Statement
relAdjunctionRightUnitHom (Struct :>: Struct) (Adjunction l r u v) x
  = And [ valid (ux,vlx)
        , Label "1.1" :<=>: (orientation ux == x :> pmap r (pmap l x))
            :?> Params ["x":=show x,"u x":=show ux,"l":=show2 l,"r":=show2 r]
        , Label "3.1" :<=>: (one lx == vlx * amap l ux)
            :?> Params ["x":=show x,"pmap l x":= show lx,"l":=show2 l,"r":=show2 r]
        ]
  where ux  = u x
        vlx = v lx
        lx  = pmap l x

--------------------------------------------------------------------------------
-- relAdjunctionRightNatural -

relAdjunctionRightNaturalHom :: (Hom Mlt h, Show2 h)
  => Homomorphous Mlt d c -> Adjunction h d c -> c -> Statement
relAdjunctionRightNaturalHom (Struct :>: Struct) (Adjunction l r u _) f
  = Label "1.2" :<=>: (u (end f) * f == amap r (amap l f) * u (start f))
      :?> Params ["f":=show f,"l":=show2 l,"r":=show2 r]


--------------------------------------------------------------------------------
-- prpAdjunctionRight -

-- | validity of the unit on the right side.
prpAdjunctionRight :: (Hom Mlt h, Show2 h) => Adjunction h d c -> Point c -> c -> Statement
prpAdjunctionRight adj@(Adjunction _ r _ _) x f = Prp "AdjunctionRight" :<=>:
  And [ relAdjunctionRightUnitHom s adj x
      , relAdjunctionRightNaturalHom s adj f
      ]
  where s = tauHom (homomorphous r)

--------------------------------------------------------------------------------
-- prpAdjunctionLeft -

-- | validity of the unit on the left side.
prpAdjunctionLeft :: (Hom Mlt h, Show2 h) => Adjunction h d c -> Point d -> d -> Statement
prpAdjunctionLeft adj y g = Prp "AdjucntionLeft" :<=>:
  prpAdjunctionRight (coAdjunction adj) y (Op g)

--------------------------------------------------------------------------------
-- prpAjunction -

-- | validity of an adjunction according to the properties of 'Adjunction'.
prpAdjunction
  :: (Hom Mlt h, Entity2 h)
  => Adjunction h d c
  -> X (Point d) -> X d
  -> X (Point c) -> X c
  -> Statement
prpAdjunction adj@(Adjunction l r _ _) xpd xd xpc xc = Prp "Adjunction" :<=>:
  And [ valid2 l
      , valid2 r
      , Forall (xTupple2 xpc xc) (uncurry (prpAdjunctionRight adj))
      , Forall (xTupple2 xpd xd) (uncurry (prpAdjunctionLeft adj))
      ]

--------------------------------------------------------------------------------
-- Adjunction - Validable -

instance ( HomMultiplicative h, Entity2 h
         , XStandardPoint d, XStandard d, XStandardPoint c, XStandard c
         )
  => Validable (Adjunction h d c) where
  valid adj = Label "Mlt" :<=>:
    prpAdjunction adj xStandard xStandard xStandard xStandard

-}
