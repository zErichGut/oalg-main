
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE FlexibleContexts, RankNTypes #-}


-- |
-- Module      : OAlg.Limes.Cone.Definition
-- Description : cones over diagrams
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- cones over 'Diagram's.
module OAlg.Limes.Cone.Definition
  (
    -- * Cone
    Cone(..), Perspective(..)
  , cnDiagram, cnDiagramTypeRefl
  , tip, shell, cnArrows, cnPoints
  , cnMap, cnMapMlt, cnMapDst
  
    -- ** Distributive
  , cnZeroHead
  , cnKernel, cnCokernel
  , cnDiffHead
  , ConeZeroHead(..)
  , coConeZeroHead, czFromOpOp, coConeZeroHeadInv
  
    -- ** Duality
  , cnToOp, cnFromOp, ConeDuality(..)
  , coCone, coConeInv, cnFromOpOp

    -- * Cone Struct
  , ConeStruct(..), cnStructOp, cnStructMlt, cnStruct
 
    -- * Orientation
  , cnPrjOrnt, cnInjOrnt

    -- * Chain
  , cnPrjChainTo, cnPrjChainToInv
  , cnPrjChainFrom, cnPrjChainFromInv
  , FactorChain(..)
  ) where

import Control.Monad

import Data.Typeable
import Data.Array hiding (range)

import OAlg.Prelude

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Fibred
import OAlg.Structure.Multiplicative as Mlt
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive
import OAlg.Hom.Definition

import OAlg.Limes.Perspective

--------------------------------------------------------------------------------
-- Cone -

-- | cone over a diagram.
--
-- __Properties__ Let @c@ be in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ then holds:
--
-- (1) If @c@ matches @'ConeProjective' d t cs@ for a 'Multiplicative' structure __@a@__
-- then holds:
--
--     (1) For all @ci@ in @cs@ holds: @'start' ci '==' t@ and
--     @'end' ci '==' pi@ where @pi@ in @'dgPoints' d@.
--
--     (2) For all @aij@ in @'dgArrows' d@ holds: @aij 'Mlt.*' ci '==' cj@
--     where @ci@, @cj@ in @cs@.
--
-- (2) If @c@ matches @'ConeInjective' d t cs@ for a 'Multiplicative' structure __@a@__
-- then holds:
--
--     (1) For all @ci@ in @cs@ holds: @'end' ci '==' t@ and
--     @'start' ci '==' pi@ where @pi@ in @'dgPoints' d@.
--
--     (2) For all @aij@ in @'dgArrows' d@ holds: @cj 'Mlt.*' aij '==' ci@
--     where @ci@, @cj@ in @cs@.
--
-- (3) If @c@ matches @'ConeKernel' p k@ for a 'Distributive' structure __@a@__ then holds:
--
--     (1) @'end' k '==' p0@ where @p0@ in @'dgPoints' p@
--
--     (2) For all @a@ in @'dgArrows' p@ holds: @a 'Mlt.*' k '==' 'zero' (t ':>' p1)@
--     where @t = 'start' k@ and @p0@, @p1@ in @'dgPoints' p@.
--
-- (4) If @c@ matches @'ConeCokernel' p k@ for a 'Distributive' structure __@a@__ then
-- holds:
--
--     (1) @'start' k '==' p0@ where @p0@ in @'cnPoints' c@
--
--     (2) For all @a@ in @'dgArrows' p@ holds: @k 'Mlt.*' a '==' 'zero' (p1 ':>' t)@ where
--     @t = 'end' k@ and @p0@, @p1@ in @'dgPoints' p@.
data Cone s p t n m a where
  ConeProjective :: Multiplicative a
    => Diagram t n m a -> Point a -> FinList n a -> Cone Mlt Projective t n m a
  ConeInjective  :: Multiplicative a
    => Diagram t n m a -> Point a -> FinList n a -> Cone Mlt Injective t n m a
  ConeKernel     :: Distributive a
    => Diagram (Parallel LeftToRight) N2 m a -> a
    -> Cone Dst Projective (Parallel LeftToRight)  N2 m a
  ConeCokernel   :: Distributive a
    => Diagram (Parallel RightToLeft) N2 m a -> a
    -> Cone Dst Injective (Parallel RightToLeft) N2 m a


--------------------------------------------------------------------------------
-- ConeStruct -

-- | cone structures.
data ConeStruct s a where
  ConeStructMlt :: Multiplicative a => ConeStruct Mlt a
  ConeStructDst :: Distributive a => ConeStruct Dst a

deriving instance Show (ConeStruct s a)
deriving instance Eq (ConeStruct s a)

--------------------------------------------------------------------------------
-- cnStructOp -

-- | the opposite cone structure.
cnStructOp :: ConeStruct s a -> ConeStruct s (Op a)
cnStructOp cs = case cs of
  ConeStructMlt -> ConeStructMlt
  ConeStructDst -> ConeStructDst

--------------------------------------------------------------------------------
-- cnStructMlt -

-- | the 'Multiplicative' structure of a cone structure.
cnStructMlt :: ConeStruct s a -> Struct Mlt a
cnStructMlt cs = case cs of
  ConeStructMlt -> Struct
  ConeStructDst -> Struct

--------------------------------------------------------------------------------
-- cnStruct -

-- | the associated structure of a cone structure.
cnStruct :: ConeStruct s a -> Struct s a
cnStruct cs = case cs of
  ConeStructMlt -> Struct
  ConeStructDst -> Struct

--------------------------------------------------------------------------------
-- cnDiagram -

-- | the underlying diagram.
cnDiagram :: Cone s p t n m a -> Diagram t n m a
cnDiagram (ConeProjective d _ _) = d
cnDiagram (ConeInjective d _ _)  = d
cnDiagram (ConeKernel d _)       = d
cnDiagram (ConeCokernel d _)     = d

--------------------------------------------------------------------------------
-- cnDiagramTypeRefl -

-- | reflexivity of the underlying diagram type.
cnDiagramTypeRefl :: Cone s p t n m a -> Dual (Dual t) :~: t
cnDiagramTypeRefl (ConeProjective d _ _) = dgTypeRefl d
cnDiagramTypeRefl (ConeInjective d _ _)  = dgTypeRefl d
cnDiagramTypeRefl (ConeKernel d _)       = dgTypeRefl d
cnDiagramTypeRefl (ConeCokernel d _)     = dgTypeRefl d


--------------------------------------------------------------------------------
-- cnMap -

cnMapMltStruct :: Hom Mlt h => Struct Mlt b -> h a b
  -> Cone Mlt p t n m a -> Cone Mlt p t n m b
cnMapMltStruct Struct h c = case c of
  ConeProjective d t as -> ConeProjective (dgMap h d) (pmap h t) (fmap (amap h) as)
  ConeInjective d t as -> ConeInjective (dgMap h d) (pmap h t) (fmap (amap h) as)

-- | mapping of a cone under a 'Multiplicative' homomorphism.
cnMapMlt :: Hom Mlt h => h a b -> Cone Mlt p t n m a -> Cone Mlt p t n m b
cnMapMlt h = cnMapMltStruct (tau $ range h) h

cnMapDstStruct :: Hom Dst h => Struct Dst b -> h a b
  -> Cone Dst p t n m a -> Cone Dst p t n m b
cnMapDstStruct Struct h c = case c of
  ConeKernel d a   -> ConeKernel (dgMap h d) (amap h a)
  ConeCokernel d a -> ConeCokernel (dgMap h d) (amap h a)

-- | mapping of a cone under a 'Distributive' homomorphism.
cnMapDst :: Hom Dst h => h a b -> Cone Dst p t n m a -> Cone Dst p t n m b
cnMapDst h = cnMapDstStruct (tau $ range h) h

-- | mapping of a cone.
cnMap :: Hom s h => h a b -> Cone s p t n m a -> Cone s p t n m b
cnMap h c = case c of
  ConeProjective _ _ _ -> cnMapMlt h c
  ConeInjective _ _ _  -> cnMapMlt h c
  ConeKernel _ _       -> cnMapDst h c
  ConeCokernel _ _     -> cnMapDst h c
  
instance HomMultiplicative h => Applicative1 h (Cone Mlt p t n m) where
  amap1 = cnMapMlt

instance HomDistributive h => Applicative1 h (Cone Dst p t n m) where
  amap1 = cnMapDst

--------------------------------------------------------------------------------
-- Cone - Dual -

type instance Dual (Cone s p t n m a) = Cone s (Dual p) (Dual t) n m (Op a)

--------------------------------------------------------------------------------
-- coCone -

-- | to the dual cone, with its inverse 'coConeInv'.
coCone :: Cone s p t n m a -> Dual (Cone s p t n m a)
coCone c = case c of
  ConeProjective d t as -> ConeInjective (coDiagram d) t (fmap Op as)
  ConeInjective d t as  -> ConeProjective (coDiagram d) t (fmap Op as)
  ConeKernel d a        -> ConeCokernel (coDiagram d) (Op a)
  ConeCokernel d a      -> ConeKernel (coDiagram d) (Op a)

--------------------------------------------------------------------------------
-- cnFromOpOp -

-- | from @'Op' '.' 'Op'@.
cnFromOpOp :: ConeStruct s a -> Cone s p t n m (Op (Op a)) -> Cone s p t n m a
cnFromOpOp ConeStructMlt = cnMapMlt isoFromOpOpMlt
cnFromOpOp ConeStructDst = cnMapDst isoFromOpOpDst 

--------------------------------------------------------------------------------
-- coConeInv -

-- | from the dual cone, with its inverse 'coCone'.
coConeInv :: ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (Cone s p t n m a) -> Cone s p t n m a
coConeInv cs Refl Refl = cnFromOpOp cs . coCone

--------------------------------------------------------------------------------
-- ConeDuality -

-- | 'Op'-duality between cone types.
data ConeDuality s f g a where
  ConeDuality :: ConeStruct s a
    -> f a :~: Cone s p t n m a
    -> g (Op a) :~: Dual (Cone s p t n m a)
    -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
    -> ConeDuality s f g a

--------------------------------------------------------------------------------
-- cnToOp -

-- | to @__g__ ('Op' __a__)@.
cnToOp :: ConeDuality s f g a -> f a -> g (Op a)
cnToOp (ConeDuality _ Refl Refl _ _) = coCone

--------------------------------------------------------------------------------
-- cnFromOp -

-- | from @__g__ ('Op' __a__)@.
cnFromOp :: ConeDuality s f g a -> g (Op a) -> f a
cnFromOp (ConeDuality cs Refl Refl rp rt) = coConeInv cs rp rt

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
tip :: Cone s p t n m a -> Point a
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
-- @'fmap' 'end' ('shell' c) '==' 'cnPoints' c@.
--
-- (2) If __@p@__ is equal to __'Injective'__ then holds:
-- @'fmap' 'start' ('shell' c) '==' 'cnPoints' c@.
shell :: Cone s p t n m a -> FinList n a
shell (ConeProjective _ _ as) = as
shell (ConeInjective _ _ as)  = as
shell (ConeKernel (DiagramParallelLR _ q _) k)     = k:|zero (start k :> q):|Nil
shell (ConeCokernel (DiagramParallelRL _ q _) k) =  k:|zero (q :> end k):|Nil

--------------------------------------------------------------------------------
-- cnPoints -

-- | the points of the underlying diagram, i.e. @'dgPoints' '.' 'cnDiagram'@. 
cnPoints :: Oriented a => Cone s p t n m a -> FinList n (Point a)
cnPoints = dgPoints . cnDiagram

--------------------------------------------------------------------------------
-- cnArrows -

-- | the arrows of the underlying diagram, i.e. @'dgArrows' '.' 'cnDiagram'@.
cnArrows :: Cone s p t n m a -> FinList m a
cnArrows = dgArrows . cnDiagram

--------------------------------------------------------------------------------
-- cnDstAdjZero -

-- | adjoins a 'zero' arrow to the diagram and the cone.
cnDstAdjZero :: Cone Dst p t n m a -> Cone Mlt p t n (m+1) a
cnDstAdjZero (ConeKernel d@(DiagramParallelLR _ r _) k)
  = ConeProjective (dgPrlAdjZero d) t (k:|zero (t:>r):|Nil) where t = start k
cnDstAdjZero c@(ConeCokernel _ _)
  = coConeInv ConeStructMlt Refl Refl $ cnDstAdjZero $ coCone c

--------------------------------------------------------------------------------
-- ConeZeroHead -

-- | predicate for cones where the first arrow of its underlying diagram is equal to 'zero'.
newtype ConeZeroHead s p t n m a = ConeZeroHead (Cone s p t n m a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ConeZeroHead - Validable -

instance Distributive a
  => Validable (ConeZeroHead s p d n (S m) a) where
  valid (ConeZeroHead c)
    = And [ valid c
          , relIsZero $ head $ dgArrows $ cnDiagram c
          ]

instance ( Distributive a
         , Typeable s, Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Entity (ConeZeroHead s p t n (S m) a)

--------------------------------------------------------------------------------
-- ConeZeroHead - Dual -

type instance Dual (ConeZeroHead s p t n m a) = ConeZeroHead s (Dual p) (Dual t) n m (Op a)

-- | to the dual, with its inverse 'coConeZeroHead'.
coConeZeroHead :: ConeZeroHead s p t n m a -> Dual (ConeZeroHead s p t n m a)
coConeZeroHead (ConeZeroHead c) = ConeZeroHead $ coCone c

-- | from the bidual.
czFromOpOp :: ConeStruct s a
  -> ConeZeroHead s p t n m (Op (Op a)) -> ConeZeroHead s p t n m a
czFromOpOp sa (ConeZeroHead c) = ConeZeroHead $ cnFromOpOp sa c

-- | from the dual, with its inverse 'coConeZeroHead'.
coConeZeroHeadInv :: ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (ConeZeroHead s p t n m a) -> ConeZeroHead s p t n m a
coConeZeroHeadInv sa rp rt (ConeZeroHead c)
  = ConeZeroHead $ coConeInv sa rp rt c

--------------------------------------------------------------------------------
-- cnDiffHead -

-- | subtracts to every arrow of the underlying parallel diagram the first arrow and
-- adapts the shell accordingly.
cnDiffHead :: (Distributive a, Abelian a)
  => Cone Mlt p (Parallel d) n (m+1) a -> ConeZeroHead Mlt p (Parallel d)  n (m+1) a
cnDiffHead (ConeProjective d t (a:|as)) = ConeZeroHead $ case d of
  DiagramParallelLR _ _ _ -> ConeProjective (dgPrlDiffHead d) t (a:|fmap toZero as)
  DiagramParallelRL _ _ _ -> ConeProjective (dgPrlDiffHead d) t (toZero a:|as)
  where toZero a = zero (root a)
cnDiffHead c@(ConeInjective d _ _) = case d of
  DiagramParallelLR _ _ _ ->   coConeZeroHeadInv ConeStructMlt Refl Refl
                             $ cnDiffHead $ coCone c
  DiagramParallelRL _ _ _ ->   coConeZeroHeadInv ConeStructMlt Refl Refl
                             $ cnDiffHead $ coCone c

--------------------------------------------------------------------------------
-- cnZeroHead -

-- | embedding of a cone in a distributive structure to its multiplicative cone.
cnZeroHead :: Cone Dst p t n m a -> ConeZeroHead Mlt p t n (m+1) a
cnZeroHead = ConeZeroHead . cnDstAdjZero 

--------------------------------------------------------------------------------
-- cnKernel -

-- | the kernel cone of a zero headed parallel cone, i.e. the inverse of 'cnZeroHead'.
cnKernel :: (Distributive a, p ~ Projective, t ~ Parallel LeftToRight)
  => ConeZeroHead Mlt p t n (m+1) a -> Cone Dst p t n m a
cnKernel (ConeZeroHead (ConeProjective d _ cs)) = case d of
  DiagramParallelLR l r as -> ConeKernel (DiagramParallelLR l r (tail as)) (head cs)

--------------------------------------------------------------------------------
-- cnCokernel

-- | the cokernel cone of a zero headed parallel cone, i.e. the inverse of 'cnZeroHead'.
cnCokernel :: (Distributive a, p ~ Injective, t ~ Parallel RightToLeft)
  => ConeZeroHead Mlt p t n (m+1) a -> Cone Dst p t n m a
cnCokernel = coConeInv ConeStructDst Refl Refl . cnKernel . coConeZeroHead

--------------------------------------------------------------------------------
-- relConePrjMlt -

prm :: N -> Message
prm i = Params["i":=show i]

lE, lS, lO, lC, lB :: Label
lE = Label "end"
lS = Label "start"
lO = Label "orientation"
lC = Label "commutative"
lB = Label "bound"

tp2 :: FinList N2 a -> (a,a)
tp2 (a:|b:|Nil) = (a,b)

ht :: FinList (n+1) a -> (a,FinList n a)
ht (x:|xs) = (x,xs)

relConePrjMlt :: Multiplicative a
  => Diagram t n m a -> Point a -> FinList n a -> Statement
relConePrjMlt DiagramEmpty t Nil = valid t

relConePrjMlt (DiagramDiscrete ps) t cs = valid t && vld 0 t ps cs where
  vld :: Multiplicative a => N -> Point a -> FinList n (Point a) -> FinList n a
         -> Statement
  vld _ _ Nil Nil = SValid
  vld i t (p:|ps) (c:|cs)
    = And [ valid p
          , valid c
          , lO :<=>: (orientation c == t :> p) :?> prm i
          , vld (succ i) t ps cs
          ]

relConePrjMlt (DiagramChainTo l as) t cs = valid cl && vld 0 l as t cl cs' where
  (cl,cs') = ht cs
  vld :: Multiplicative a
    => N -> Point a -> FinList m a -> Point a -> a -> FinList m a -> Statement
  vld i l Nil t cl Nil
    = lO :<=>: (orientation cl == t:>l):?>prm i
  vld i l (a:|as) t cl (c:|cs)
    = And [ valid a
          , valid c
          , lO :<=>: (end a == l):?>prm i
          , lO :<=>: (orientation c == t:>start a):?>prm i
          , lC :<=>: (a*c == cl):?>prm i
          , vld (succ i) (start a) as t c cs 
          ]

relConePrjMlt (DiagramChainFrom l as) t cs = vld 0 l as t cl cs' where
  (cl,cs') = ht cs
  vld :: Multiplicative a
    => N -> Point a -> FinList m a -> Point a -> a -> FinList m a -> Statement
  vld i l Nil t cl Nil
    = And [ valid cl
          , lO :<=>: (orientation cl == t :> l):?>prm i
          ]
  vld i l (a:|as) t cl (c:|cs)
    = And [ valid a
          , valid cl
          , lO :<=>: (start a == l):?>prm i
          , lO :<=>: (orientation cl == t:>start a):?>prm i
          , lC :<=>: (a*cl == c):?>prm i
          , vld (succ i) (end a) as t c cs
          ]

relConePrjMlt (DiagramParallelLR p q as) t cs
  = And [ valid cp
        , valid cq
        , lO :<=>: (orientation cp == t:>p):?>prm 0
        , lO :<=>: (orientation cq == t:>q):?>prm 1
        , vld 0 (p:>q) as cp cq
        ] where
  (cp,cq) = tp2 cs
  vld :: Multiplicative a => N -> Orientation (Point a)
    -> FinList m a -> a -> a -> Statement
  vld _ _ Nil _ _ = SValid
  vld i o (a:|as) cp cq
    = And [ valid a
          , lO :<=>: (orientation a == o):?>prm i
          , lC :<=>: (a*cp == cq):?>prm i
          , vld (succ i) o as cp cq
          ]
relConePrjMlt (DiagramParallelRL p q as) t cs
  = And [ valid cp
        , valid cq
        , lO :<=>: (orientation cp == t:>p):?>prm 0
        , lO :<=>: (orientation cq == t:>q):?>prm 1
        , vld 0 (q:>p) as cp cq
        ] where
  (cp,cq) = tp2 cs
  vld :: Multiplicative a => N -> Orientation (Point a)
    -> FinList n a -> a -> a -> Statement
  vld _ _ Nil _ _ = SValid
  vld i o (a:|as) cp cq
    = And [ valid a
          , lO :<=>: (orientation a == o):?>prm i
          , lC :<=>: (a*cq == cp):?>prm i
          , vld (succ i) o as cp cq
          ]

relConePrjMlt (DiagramSource s as) t cs
  = And [ valid c0
        , lO :<=>: (orientation c0 == t:>s):?>prm 0
        , vld 0 t s as c0 cs'
        ] where
  (c0,cs')  = ht cs 
  vld :: Multiplicative a => N -> Point a -> Point a
         -> FinList m a -> a -> FinList m a -> Statement
  vld _ _ _ Nil _ Nil = SValid
  vld i t s (a:|as) c0 (c:|cs)
    = And [ valid a
          , lS :<=>: (start a == s):?>prm i
          , lO :<=>: (orientation c == t:>end a):?>prm i
          , lC :<=>: (a*c0 == c):?>prm i
          , vld (succ i) t s as c0 cs
          ]

relConePrjMlt (DiagramSink e as) t cs
  = And [ valid c0
        , lO :<=>: (orientation c0 == t:>e):?>prm 0
        , vld 0 t e as c0 cs'
        ] where
  (c0,cs') = ht cs
  vld :: Multiplicative a => N -> Point a -> Point a
         -> FinList m a -> a -> FinList m a -> Statement
  vld _ _ _ Nil _ Nil = SValid
  vld i t e (a:|as) c0 (c:|cs)
    = And [ valid a
          , lE :<=>: (end a == e):?>prm i
          , lO :<=>: (orientation c == t:>start a):?>prm i
          , lC :<=>: (a*c == c0):?>prm i
          , vld (succ i) t e as c0 cs
          ]
relConePrjMlt (DiagramGeneral ps aijs) t cs
  = And [ vldO 0 t ps cs
        , vldC 0 (toArray cs) aijs
        ] where
  vldO :: Oriented a => N -> Point a
    -> FinList n (Point a) -> FinList n a -> Statement
  vldO _ _ Nil Nil = SValid
  vldO i t (p:|ps) (c:|cs)
    = And [ valid c
          , lO :<=>: (orientation c == t:>p):?>prm i
          , vldO (succ i) t ps cs
          ]

  vldC :: Multiplicative a => N -> Array N a
    -> FinList m (a,Orientation N) -> Statement
  vldC _ _ Nil = SValid
  vldC l cs ((a,i:>j):|aijs)
    = And [ valid a
          , lB :<=>: (inRange (bounds cs) i) :?> Params["l":=show l,"i":=show i]
          , lB :<=>: (inRange (bounds cs) j) :?> Params["l":=show l,"j":=show j]
          , lO :<=>: (orientation a == end ci :> end cj)
                     :?>Params["l":=show l,"(i,j)":=show (i,j)]
          , lC :<=>: (a*ci == cj):?>Params["l":=show l,"(i,j)":=show (i,j)]
          , vldC (succ l) cs aijs
          ] where ci = cs ! i
                  cj = cs ! j


--------------------------------------------------------------------------------
-- relCone -

-- | validity of a 'Cone'.
relCone :: Cone s p t n m a -> Statement
relCone (ConeProjective d t cs) = relConePrjMlt d t cs
relCone c@(ConeKernel _ _)      = relCone (cnDstAdjZero c)
relCone c                       = relCone (coCone c)

--------------------------------------------------------------------------------
-- Cone - Validable -

instance Validable (Cone s p t n m a) where
  valid c = Label "Cone" :<=>: relCone c 

--------------------------------------------------------------------------------
-- Cone - Entity -

deriving instance Show (Cone s p t n m a)
deriving instance Eq (Cone s p t n m a)

instance ( Typeable s, Typeable p, Typeable t, Typeable n, Typeable m, Typeable a
         ) => Entity (Cone s p t n m a)


--------------------------------------------------------------------------------
-- Cone - Oriented -

instance (Oriented a, Typeable s, Typeable p, Typeable d, Typeable m)
  => Oriented (Cone s p (Parallel d) N2 m a) where
  type Point (Cone s p (Parallel d) N2 m a) = Point a
  orientation c = orientation $ cnDiagram c
  
--------------------------------------------------------------------------------
-- cnPrjOrnt -

-- | the projective cone on 'Orientation' with the underlying given diagram and tip with the given
-- point. 
cnPrjOrnt :: Entity p
  => p -> Diagram t n m (Orientation p) -> Cone Mlt Projective t n m (Orientation p)
cnPrjOrnt p d = ConeProjective d p (amap1 (p:>) $ dgPoints d)

cnPrjDstOrnt :: (Entity p, t ~ Parallel LeftToRight, n ~ N2)
  => p -> Diagram t n m (Orientation p) -> Cone Dst Projective t n m (Orientation p)
cnPrjDstOrnt t d@(DiagramParallelLR p _ _) = ConeKernel d (t:>p)

--------------------------------------------------------------------------------
-- cnInjOrnt -

-- | the injective cone on 'Orientation' with the underlying given diagram and tip with the given
-- point. 
cnInjOrnt :: Entity p
  => p -> Diagram t n m (Orientation p) -> Cone Mlt Injective t n m (Orientation p)
cnInjOrnt p d = ConeInjective d p (amap1 (:>p) $ dgPoints d)

cnInjDstOrnt :: (Entity p, t ~ Parallel RightToLeft, n ~ N2)
  => p -> Diagram t n m (Orientation p) -> Cone Dst Injective t n m (Orientation p)
cnInjDstOrnt t d@(DiagramParallelRL _ q _) = ConeCokernel d (q:>t)
  
instance ( Entity p
         , XStandard p, XStandard (Diagram t n m (Orientation p))
         ) => XStandard (Cone Mlt Projective t n m (Orientation p)) where
  xStandard = do
    dg <- xStandard
    p  <- xStandard
    return (cnPrjOrnt p dg)

instance ( Entity p, t ~ Parallel LeftToRight, n ~ N2
         , XStandard p, XStandard (Diagram t n m (Orientation p))
         ) => XStandard (Cone Dst Projective t n m (Orientation p)) where
  xStandard = do
    dg <- xStandard
    t  <- xStandard
    return (cnPrjDstOrnt t dg)
                                 
instance ( Entity p
         , XStandard p, XStandard (Diagram t n m (Orientation p))
         ) => XStandard (Cone Mlt Injective t n m (Orientation p)) where
  xStandard = do
    dg <- xStandard
    p  <- xStandard
    return (cnInjOrnt p dg)

instance ( Entity p, t ~ Parallel RightToLeft, n ~ N2
         , XStandard p, XStandard (Diagram t n m (Orientation p))
         ) => XStandard (Cone Dst Injective t n m (Orientation p)) where
  xStandard = do
    dg <- xStandard
    t  <- xStandard
    return (cnInjDstOrnt t dg)

--------------------------------------------------------------------------------
-- cnChain -

-- | predicate for a factor with 'end' point at the starting point of the given chain.
--
-- __Property__
--
-- (1) Let @'FactorChain' f d@ be in @'FactorChain' 'To'  __n__ __a__@
-- for a 'Multiplicative' structure @__a__@ then holds:
-- @'end' f '==' 'chnToStart' d@.
--
-- (2) Let @'FactorChain' f d@ be in @'FactorChain' 'From'  __n__ __a__@
-- for a 'Multiplicative' structure @__a__@ then holds:
-- @'end' f '==' 'chnFromStart' d@.
data FactorChain s n a = FactorChain a (Diagram (Chain s) (n+1) n a)
  deriving (Show,Eq)

instance Oriented a => Validable (FactorChain To n a) where
  valid (FactorChain f d)
    = And [ valid f
          , valid d
          , end f .==. chnToStart d
          ]

instance Oriented a => Validable (FactorChain From n a) where
  valid (FactorChain f d)
    = And [ valid f
          , valid d
          , end f .==. chnFromStart d
          ]

instance (Multiplicative a, Typeable n) => Entity (FactorChain To n a)
instance (Multiplicative a, Typeable n) => Entity (FactorChain From n a)

--------------------------------------------------------------------------------
-- cnPrjChainTo

-- | the induced 'Projective' cone with ending factor given by the given 'FactorChain'.
--
-- __Property__ Let @h = 'FactorChain' f d@ be in
-- @'FactorChain' 'To' __n__ __a__@ for a 'Multiplicative' structure @__a__@ and
-- @'ConeProjective' d' _ (_':|'..':|'c':|''Nil') = 'cnPrjChainTo' h@ then holds:
-- @d' '==' d@ and @c '==' f@.
cnPrjChainTo :: Multiplicative a
  => FactorChain To n a -> Cone Mlt Projective (Chain To) (n+1) n a
cnPrjChainTo (FactorChain f d@(DiagramChainTo _ as))
  = ConeProjective d (start f) (cmp f as) where
  cmp :: Multiplicative a => a -> FinList n a -> FinList (n+1) a
  cmp f Nil     = f:|Nil
  cmp f (a:|as) = (a*c):|cs where cs@(c:|_) = cmp f as

--------------------------------------------------------------------------------
-- cnPrjChainToInv -

-- | the underlying factor chain of a projective chain to cone, i.e the inverse of
-- 'cnPrjChainToInv'.
cnPrjChainToInv :: Cone Mlt Projective (Chain To) (n+1) n a -> FactorChain To n a
cnPrjChainToInv (ConeProjective d _ cs) = FactorChain (f cs) d where
  f :: FinList (n+1) a -> a
  f (c:|Nil)       = c
  f (_:|cs@(_:|_)) = f cs

--------------------------------------------------------------------------------
-- chPrjChainFrom -

-- | the induced 'Projective' cone with starting factor given by the given 'FactorChain'.
--
-- __Property__ Let @h = 'FactorChain' f d@ be in
-- @'FactorChain' 'From' __n__ __a__@ for a 'Multiplicative' structure @__a__@ and
-- @'ConeProjective' d' _ (c':|'_) = 'cnPrjChainFrom' h@ then holds:
-- @d' '==' d@ and @c '==' f@.
cnPrjChainFrom :: Multiplicative a
  => FactorChain From n a -> Cone Mlt Projective (Chain From) (n+1) n a
cnPrjChainFrom (FactorChain f d@(DiagramChainFrom _ as))
  = ConeProjective d (start f) (cmp f as) where
  cmp :: Multiplicative a => a -> FinList n a -> FinList (n+1) a
  cmp f Nil     = f:|Nil
  cmp f (a:|as) = f :| cmp f' as where f' = a*f

--------------------------------------------------------------------------------
-- cnPrjChainFromInv -

-- | the underlying factor chain of a projective chain from cone, i.e. the inverse of
-- 'cnPrjChainFrom'.
cnPrjChainFromInv :: Cone Mlt Projective (Chain From) (n+1) n a -> FactorChain From n a
cnPrjChainFromInv (ConeProjective d _ (c:|_)) = FactorChain c d

