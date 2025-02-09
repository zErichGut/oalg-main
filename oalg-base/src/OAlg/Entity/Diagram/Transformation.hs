
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
  ( -- * Transformation
    Transformation(..), trfs

    -- * Duality
  , coTransformation
  ) where

import Data.Typeable
import Data.Array as A

import OAlg.Prelude

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative as M
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Vectorial as V
import OAlg.Structure.Algebraic

import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Entity.Diagram.Quiver
import OAlg.Entity.Diagram.Definition

--------------------------------------------------------------------------------
-- Transformation -

-- | natural transformations between two 'Diagram's.
--
-- __Property__ Let @'Transformation' a b t@ be in
-- @'Transformation' __t__ __n__ __m__ __a__@ for a 'Multiplicative' structure __@a@__,
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
data Transformation t n m a
  = Transformation (Diagram t n m a) (Diagram t n m a) (FinList n a)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- trfs -

-- | the underlying list of factors.
trfs :: Transformation t n m a -> FinList n a
trfs (Transformation _ _ fs) = fs

--------------------------------------------------------------------------------
-- Transformaltion - Duality -

type instance Dual (Transformation t n m a) = Transformation (Dual t) n m (Op a)

-- | the dual transformation.
coTransformation :: Transformation t n m a -> Dual (Transformation t n m a)
coTransformation (Transformation a b ts)
  = Transformation (coDiagram b) (coDiagram a) (amap1 Op ts)

--------------------------------------------------------------------------------
-- Transformation - Entity -

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

vldTr :: Multiplicative a => Transformation t n m a -> Statement
vldTr t@(Transformation a b ts) = case (a,b) of
  (DiagramEmpty, DiagramEmpty)              -> SValid
  (DiagramDiscrete ps,DiagramDiscrete qs)   -> vldTrDiscrete 0 ps qs ts
  (DiagramChainTo p fs,DiagramChainTo q gs) -> vldTrChainTo 0 (p,fs) (q,gs) ts
  (DiagramParallelLR p p' fs,DiagramParallelLR q q' gs)
    -> vldTrPrlLR (p,p',fs) (q,q',gs) ts
  (DiagramSink p fs,DiagramSink q gs)       -> vldTrSink (p,fs) (q,gs) ts
  (DiagramGeneral _ _,DiagramGeneral _ _)   -> vldTrGen a b ts
  _                                         -> vldTr (coTransformation t)

instance Multiplicative a => Validable (Transformation t n m a) where
  valid t@(Transformation a b _) = Label "Transformation" :<=>:
    And [ valid (a,b) 
        , vldTr t
        ]

instance ( Multiplicative a
         , Typeable t, Typeable n, Typeable m
         )
  => Entity (Transformation t n m a)

--------------------------------------------------------------------------------
-- Multiplicative -

instance ( Multiplicative a
         , Typeable t, Typeable n, Typeable m
         )
  => Oriented (Transformation t n m a) where
  type Point (Transformation t n m a) = Diagram t n m a
  orientation (Transformation a b _) = a:>b

instance ( Multiplicative a
         , Typeable t, Typeable n, Typeable m
         )
  => Multiplicative (Transformation t n m a) where
  one d = Transformation d d ts where
    ts = amap1 one $ dgPoints d
    
  Transformation a b fs * Transformation c d gs
    | d == a    = Transformation c b (amap1 (uncurry (*)) (fs `zip` gs))
    | otherwise = throw NotMultiplicable

  npower t 1                       = t
  npower t _ | not (isEndo t)      = throw NotExponential
  npower (Transformation a _ ts) n = Transformation a a (amap1 (`npower` n) ts)

instance ( Distributive a
         , Typeable t, Typeable n, Typeable m
         )
  => Fibred (Transformation t n m a) where
  type Root (Transformation t n m a) = Orientation (Diagram t n m a)
  
instance ( Distributive a
         , Typeable t, Typeable n, Typeable m
         )
  => FibredOriented (Transformation t n m a)

instance ( Distributive a
         , Typeable t, Typeable n, Typeable m
         )
  => Additive (Transformation t n m a) where
  zero (a:>b) = Transformation a b zs where
    zs = amap1 (zero . uncurry (:>)) (dgPoints a `zip` dgPoints b)
    
  Transformation a b fs + Transformation c d gs
    | a:>b == c:>d = Transformation a b (amap1 (uncurry (+)) (fs `zip` gs))
    | otherwise    = throw NotAddable

  ntimes n (Transformation a b ts) = Transformation a b (amap1 (ntimes n) ts)

instance ( Distributive a
         , Typeable t, Typeable n, Typeable m
         )
  => Distributive (Transformation t n m a)

instance ( Distributive a, Abelian a
         , Typeable t, Typeable n, Typeable m
         )
  => Abelian (Transformation t n m a) where
  negate (Transformation a b ts) = Transformation a b (amap1 negate ts)
  ztimes z (Transformation a b ts) = Transformation a b (amap1 (ztimes z) ts)

instance ( Algebraic a
         , Typeable t, Typeable n, Typeable m
         )
  => Vectorial (Transformation t n m a) where
  type Scalar (Transformation t n m a) = Scalar a
  s ! (Transformation a b ts) = Transformation a b (amap1 (s V.!) ts)

instance ( Algebraic a
         , Typeable t, Typeable n, Typeable m
         )
  => Algebraic (Transformation t n m a)
