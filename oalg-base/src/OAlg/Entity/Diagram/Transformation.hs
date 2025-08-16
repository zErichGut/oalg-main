
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Entity.Diagram.Transformation
-- Description : natural transformations between diagrams
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- natural transformations between 'Diagram's.
module OAlg.Entity.Diagram.Transformation
  (
    -- * DiagramTrafo
    DiagramTrafo(..), dgts, dgtTypeRefl
  , dgtMap, dgtMapCnt

  ) where

import Data.Kind
import Data.Typeable
import Data.Array as A

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality

import OAlg.Data.Either

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative as M
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Vectorial as V
import OAlg.Structure.Algebraic

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative

import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Entity.Diagram.Quiver
import OAlg.Entity.Diagram.Definition

--------------------------------------------------------------------------------
-- DiagramTrafo -

-- | natural transformations between two 'Diagram's.
--
-- __Property__ Let @'DiagramTrafo' a b t@ be in
-- @'DiagramTrafo' __t__ __n__ __m__ __a__@ for a 'Multiplicative' structure __@a@__,
-- then holds
--
-- (1) @'dgQuiver' a '==' 'dgQuiver' b@.
--
-- (2) For all @0 '<=' i '<' n@ holds: @'orientation' (t i) '==' p i ':>' q i@ where
-- @p = 'dgPoints' a@ and @q = 'dgPoints' b@.
--
-- (3) For all @0 '<=' j '<' m@ holds: @t (e j) 'M.*' f j '==' g j 'M.*' t (s j)@
-- where @f = 'dgArrows' a@, @g = 'dgArrows' b@, @s j@ is the index of the start point of
-- the @j@-th arrow and @e j@ is the index of the end point.
--
-- @
--                    t (s j)
--    s j     p (s j) --------> q (s j)
--     |         |                 |
--   j |     f j |                 | g j
--     |         |                 |
--     v         v                 v
--    e j     p (e j) --------> q (e j)
--                    t (e j)
-- @
data DiagramTrafo t n m a
  = DiagramTrafo (Diagram t n m a) (Diagram t n m a) (FinList n a)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- dgts -

-- | the underlying list of factors.
dgts :: DiagramTrafo t n m a -> FinList n a
dgts (DiagramTrafo _ _ fs) = fs

--------------------------------------------------------------------------------
-- dgtTypeRefl -

dgtTypeRefl :: DiagramTrafo t n m a -> Dual (Dual t) :~: t
dgtTypeRefl (DiagramTrafo a _ _) = dgTypeRefl a

--------------------------------------------------------------------------------
-- dgtMap -

dgtMap :: HomMultiplicative h
  => h x y -> DiagramTrafo t n m x -> DiagramTrafo t n m y
dgtMap h (DiagramTrafo a b ts)
  = DiagramTrafo (dgMap h a) (dgMap h b) (amap1 (amap h) ts)

instance (HomMultiplicative h)
  => ApplicativeG (DiagramTrafo t n m) h (->) where
  amapG = dgtMap

--------------------------------------------------------------------------------
-- dgtMapCnt -

dgtMapCnt :: HomMultiplicativeDisjunctive h
  => Variant2 Contravariant h a b -> DiagramTrafo t n m a -> DiagramTrafo (Dual t) n m b
dgtMapCnt h@(Contravariant2 h') (DiagramTrafo a b ts)
  = DiagramTrafo (dgMapCnt h b) (dgMapCnt h a) (amap1 (amap h') ts)

--------------------------------------------------------------------------------
-- DiagramTrafo - Dual1 -

type instance Dual1 (DiagramTrafo t n m) = DiagramTrafo (Dual t) n m

instance (Show a, ShowPoint a) => ShowDual1 (DiagramTrafo t n m) a
instance (Eq a, EqPoint a) => EqDual1 (DiagramTrafo t n m) a

dgtToBidual :: ( DualisableMultiplicative s o, TransformableMlt s
               , TransformableGRefl o s
               )
  => Struct s x -> DiagramTrafo t n m x -> DiagramTrafo t n m (o (o x))
dgtToBidual s = dgtMap (Covariant2 (t' . t)) where
  Contravariant2 (Inv2 t _)  = toDualO s
  Contravariant2 (Inv2 t' _) = toDualO (tauO s)

dgtFromBidual :: ( DualisableMultiplicative s o, TransformableMlt s
                 , TransformableGRefl o s
                 )
  => Struct s x -> DiagramTrafo t n m (o (o x)) -> DiagramTrafo t n m x
dgtFromBidual s = dgtMap (Covariant2 (f . f')) where
  Contravariant2 (Inv2 _ f)  = toDualO s
  Contravariant2 (Inv2 _ f') = toDualO (tauO s)

instance ( DualisableMultiplicative s o, TransformableMlt s
         , TransformableGRefl o s, Transformable s Type
         )
  => ReflexiveG s (->) o (DiagramTrafo t n m) where
  reflG s = Inv2 (dgtToBidual s) (dgtFromBidual s)

instance ( DualisableMultiplicative s o, TransformableMlt s
         , TransformableGRefl o s, Transformable s Type
         , t' ~ Dual t, t ~ Dual t'
         )
  => DualisableGPair s (->) o (DiagramTrafo t n m) (DiagramTrafo t' n m) where
  toDualGLft s = dgtMapCnt (Contravariant2 t) where
    Contravariant2 (Inv2 t _) = toDualO s
  toDualGRgt s = dgtMapCnt (Contravariant2 t) where
    Contravariant2 (Inv2 t _) = toDualO s

instance ( DualisableMultiplicative s o, TransformableMlt s
         , TransformableGRefl o s, Transformable s Type
         , t ~ Dual (Dual t)
         )
  => DualisableGBi s (->) o (DiagramTrafo t n m)

instance (HomMultiplicative h, DualisableGBi s (->) o (DiagramTrafo t n m))
  => ApplicativeG (SDualBi (DiagramTrafo t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = smapBi h

--------------------------------------------------------------------------------
-- DiagramTrafo - Entity -

l1, l2, l3 :: Label
l1 = Label "1"
l2 = Label "2"
l3 = Label "3"

vldTrDiscrete :: Oriented a
  => N -> FinList n (Point a) -> FinList n (Point a) -> FinList n a -> Statement
vldTrDiscrete _ Nil Nil Nil = SValid
vldTrDiscrete i (p:|ps) (q:|qs) (t:|ts)
  = And [ valid t
        , l2 :<=>: (orientation t == p :> q)
            :?> Params ["(i,p,q,t)":=show (i,p,q,t)]
        , vldTrDiscrete (succ i) ps qs ts
        ]

vldTrChainTo :: Multiplicative a
  => N -> (Point a,FinList m a) -> (Point a,FinList m a) -> FinList (m+1) a -> Statement
vldTrChainTo i (p,fs) (q,gs) (t:|ts)
  = And [ valid t
        , l2 :<=>: (orientation t == p:>q)
            :?> Params ["(i,p,q,t)":=show (i,p,q,t)]
        , vldChTo i fs gs (t:|ts)
        ] where
  vldChTo :: Multiplicative a
    => N -> FinList m a -> FinList m a -> FinList (m+1) a -> Statement
  vldChTo _ Nil Nil (_:|Nil) = SValid
  vldChTo i (f:|fs) (g:|gs) (r:|s:|ts)
    = And [ valid s
          , l2 :<=>: (orientation s == p' :> q')
              :?> Params ["(i,p',q',s)":=show (i,p',q',s)]
          , l3 :<=>: (r*f == g*s)
              :?> Params ["(i,r,f,g,s)":=show (i,r,f,g,s)]
          , vldChTo (succ i) fs gs (s:|ts)
          ] where
    p' = start f
    q' = start g
  
vldTrPrlLR :: Multiplicative a
  => (Point a,Point a,FinList m a) -> (Point a,Point a,FinList m a)
  -> FinList N2 a -> Statement
vldTrPrlLR (p,p',fs) (q,q',gs) (r:|s:|Nil)
  = And [ valid (r,s)
        , l2 :<=>: (orientation r == p :> q)
            :?> Params ["(p,q,r)":=show (p,q,r)]
        , l2 :<=>: (orientation s == p' :> q')
            :?> Params ["(p',q',s)":=show (p',q',s)]
        , vld 0 r s fs gs
        ] where
  vld :: Multiplicative a => N -> a -> a -> FinList m a -> FinList m a -> Statement
  vld _ _ _ Nil Nil = SValid
  vld j r s (f:|fs) (g:|gs)
    = And [ valid (f,g)
          , l3 :<=>: (s*f == g*r)
              :?> Params ["(j,r,s,f,g)":=show (j,r,s,f,g)]
          , vld (succ j) r s fs gs
          ]

vldTrSink :: Multiplicative a
  => (Point a,FinList m a) -> (Point a,FinList m a) -> FinList (m+1) a -> Statement
vldTrSink (p,fs) (q,gs) (t:|ts)
  = And [ valid t
        , l2 :<=>: (orientation t == p :> q)
            :?> Params ["(j,t,p,q)":= show (0::N,t,p,q)]
        , vld 1 t fs gs ts
        ] where
  vld :: Multiplicative a
    => N -> a -> FinList m a -> FinList m a -> FinList m a -> Statement
  vld _ _ Nil Nil Nil = SValid
  vld j t0 (f:|fs) (g:|gs) (t:|ts) 
    = And [ valid (f,g,t)
          , l2 :<=>: (orientation t == start f :> start g)
              :?> Params ["(j,f,g,t)":=show (j,f,g,t)]
          , l3 :<=>: (t0*f == g*t)
              :?> Params ["(j,t0,f,g,t)":= show (j,t0,f,g,t)]
          , vld (succ j) t0 fs gs ts
          ]

vldTrGen :: Multiplicative a
  => Diagram t n m a -> Diagram t n m a -> FinList n a -> Statement
vldTrGen a b ts
  = And [ l1 :<=>: (qa == dgQuiver b)
            :?> Params ["(a,b)":=show (a,b)]
        , vldTr 0 (dgPoints a) (dgPoints b) ts
        , vldCm 0 (qvOrientations qa) (dgArrows a) (dgArrows b) (toArray ts) 
        ] where

  qa = dgQuiver a
  
  vldTr :: Multiplicative a
    => N -> FinList n (Point a) -> FinList n (Point a) -> FinList n a -> Statement
  vldTr _ Nil Nil Nil = SValid
  vldTr i (p:|ps) (q:|qs) (t:|ts)
    = And [ valid t
          , l1 :<=>: (orientation t == p :> q)
              :?> Params ["(i,p,q,t)":= show (i,p,q,t)]
          , vldTr (succ i) ps qs ts
          ]
  vldCm :: Multiplicative a
    => N 
    -> FinList m (Orientation N) -> FinList m a -> FinList m a
    -> Array N a
    -> Statement
  vldCm _ Nil Nil Nil _ = SValid
  vldCm j ((s:>e):|os) (f:|fs) (g:|gs) t
    = And [ l3 :<=>: let {ts = t A.! s;te = t A.! e} in (te * f == g * ts)
              :?> Params ["(j,s,e,f,g,ts,te)":= show (j,s,e,f,g,ts,te)]
          , vldCm (succ j) os fs gs t
          ]

vldTr :: Multiplicative a => DiagramTrafo t n m a -> Statement
vldTr t@(DiagramTrafo a b ts) = case (a,b) of
  (DiagramEmpty, DiagramEmpty)              -> SValid
  (DiagramDiscrete ps,DiagramDiscrete qs)   -> vldTrDiscrete 0 ps qs ts
  (DiagramChainTo p fs,DiagramChainTo q gs) -> vldTrChainTo 0 (p,fs) (q,gs) ts
  (DiagramParallelLR p p' fs,DiagramParallelLR q q' gs)
    -> vldTrPrlLR (p,p',fs) (q,q',gs) ts
  (DiagramSink p fs,DiagramSink q gs)       -> vldTrSink (p,fs) (q,gs) ts
  (DiagramGeneral _ _,DiagramGeneral _ _)   -> vldTrGen a b ts

  _                                         -> case dgtTypeRefl t of
    Refl -> vldTr t' where
      SDualBi (Left1 t') = amapG toOp (SDualBi (Right1 t))
      Contravariant2 (Inv2 toOp _) = toDualOpMlt


instance Multiplicative a => Validable (DiagramTrafo t n m a) where
  valid t@(DiagramTrafo a b _) = Label "DiagramTrafo" :<=>:
    And [ valid (a,b) 
        , vldTr t
        ]

--------------------------------------------------------------------------------
-- Multiplicative -

type instance Point (DiagramTrafo t n m a) = Diagram t n m a
instance (Show a, ShowPoint a) => ShowPoint (DiagramTrafo t n m a)
instance (Eq a, EqPoint a) => EqPoint (DiagramTrafo t n m a)
instance Oriented a => ValidablePoint (DiagramTrafo t n m a)
instance (Typeable a, Typeable t, Typeable n, Typeable m) => TypeablePoint (DiagramTrafo t n m a)
instance ( Multiplicative a
         , Typeable t, Typeable n, Typeable m
         )
  => Oriented (DiagramTrafo t n m a) where
  orientation (DiagramTrafo a b _) = a:>b

instance ( Multiplicative a
         , Typeable t, Typeable n, Typeable m
         )
  => Multiplicative (DiagramTrafo t n m a) where
  one d = DiagramTrafo d d ts where
    ts = amap1 one $ dgPoints d
    
  DiagramTrafo a b fs * DiagramTrafo c d gs
    | d == a    = DiagramTrafo c b (amap1 (uncurry (*)) (fs `zip` gs))
    | otherwise = throw NotMultiplicable

  npower t 1                       = t
  npower t _ | not (isEndo t)      = throw NotExponential
  npower (DiagramTrafo a _ ts) n = DiagramTrafo a a (amap1 (`npower` n) ts)

type instance Root (DiagramTrafo t n m a) = Orientation (Diagram t n m a)
instance (Show a, ShowPoint a) => ShowRoot (DiagramTrafo t n m a)
instance (Eq a, EqPoint a) => EqRoot (DiagramTrafo t n m a)
instance Oriented a => ValidableRoot (DiagramTrafo t n m a)
instance (Typeable a, Typeable t, Typeable n, Typeable m) => TypeableRoot (DiagramTrafo t n m a)
instance ( Distributive a
         , Typeable t, Typeable n, Typeable m
         )
  => Fibred (DiagramTrafo t n m a) where

instance ( Distributive a
         , Typeable t, Typeable n, Typeable m
         )
  => FibredOriented (DiagramTrafo t n m a)

instance ( Distributive a
         , Typeable t, Typeable n, Typeable m
         )
  => Additive (DiagramTrafo t n m a) where
  zero (a:>b) = DiagramTrafo a b zs where
    zs = amap1 (zero . uncurry (:>)) (dgPoints a `zip` dgPoints b)
    
  DiagramTrafo a b fs + DiagramTrafo c d gs
    | a:>b == c:>d = DiagramTrafo a b (amap1 (uncurry (+)) (fs `zip` gs))
    | otherwise    = throw NotAddable

  ntimes n (DiagramTrafo a b ts) = DiagramTrafo a b (amap1 (ntimes n) ts)

instance ( Distributive a
         , Typeable t, Typeable n, Typeable m
         )
  => Distributive (DiagramTrafo t n m a)

instance ( Distributive a, Abelian a
         , Typeable t, Typeable n, Typeable m
         )
  => Abelian (DiagramTrafo t n m a) where
  negate (DiagramTrafo a b ts) = DiagramTrafo a b (amap1 negate ts)
  ztimes z (DiagramTrafo a b ts) = DiagramTrafo a b (amap1 (ztimes z) ts)

instance ( Algebraic a
         , Typeable t, Typeable n, Typeable m
         )
  => Vectorial (DiagramTrafo t n m a) where
  type Scalar (DiagramTrafo t n m a) = Scalar a
  s ! (DiagramTrafo a b ts) = DiagramTrafo a b (amap1 (s V.!) ts)

instance ( Algebraic a
         , Typeable t, Typeable n, Typeable m
         )
  => Algebraic (DiagramTrafo t n m a)

