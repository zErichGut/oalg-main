
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
-- Description : definition of cones over diagrams
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of 'Cone's over 'Diagram's.
module OAlg.Limes.Cone.Definition
  (

    -- * Cone
    Cone(..), diagrammaticObject
  , Perspective(..), cnMltOrDst, coneStruct
  , cnDiagramTypeRefl
  , tip, shell, cnArrows, cnPoints
  , cnMap, cnMapMlt, cnMapDst
  
    -- ** Distributive
  , cnZeroHead
  , cnKernel, cnCokernel
  , cnDiffHead
  , ConeZeroHead(..)
  , coConeZeroHead, czFromOpOp, coConeZeroHeadInv
  
    -- ** Duality
  , ConeDuality(..)
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

import OAlg.Data.Either

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
import OAlg.Limes.Diagrammatic

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

instance Diagrammatic d => Diagrammatic (Cone s p d) where diagram = diagram . diagrammaticObject

--------------------------------------------------------------------------------
-- cnDiagramTypeRefl -

-- | reflexivity of the underlying diagram type.
cnDiagramTypeRefl :: Diagrammatic d => Cone s p d t n m a -> Dual (Dual t) :~: t
cnDiagramTypeRefl c = dgTypeRefl (diagram c)

--------------------------------------------------------------------------------
-- coneDiagram -

-- | mapping a 'Diagrammatic'-'Cone' to a 'Diagram'-'Cone'.
coneDiagram :: Diagrammatic d => Cone s p d t n m a -> Cone s p Diagram t n m a
coneDiagram (ConeProjective d t s) = ConeProjective (diagram d) t s
coneDiagram (ConeInjective d t s)  = ConeInjective (diagram d) t s
coneDiagram (ConeKernel d k)       = ConeKernel (diagram d) k
coneDiagram (ConeCokernel d k)     = ConeCokernel (diagram d) k

--------------------------------------------------------------------------------
-- cnMap -

cnMapMltStruct :: (DiagrammaticApplicative h d, Hom Mlt h)
  => Struct Mlt b -> h a b -> Cone Mlt p d t n m a -> Cone Mlt p d t n m b
cnMapMltStruct Struct h c = case c of
  ConeProjective d t as  -> ConeProjective (dmap h d) (pmap h t) (fmap (amap h) as)
  ConeInjective d t as   -> ConeInjective (dmap h d) (pmap h t) (fmap (amap h) as)


-- | mapping of a cone under a 'Multiplicative' homomorphism.
cnMapMlt :: (DiagrammaticApplicative h d, Hom Mlt h)
  => h a b -> Cone Mlt p d t n m a -> Cone Mlt p d t n m b
cnMapMlt h = cnMapMltStruct (tau $ range h) h

cnMapDstStruct :: (DiagrammaticApplicative h d, Hom Dst h) => Struct Dst b
  -> h a b -> Cone Dst p d t n m a -> Cone Dst p d t n m b
cnMapDstStruct Struct h c = case c of
  ConeKernel d a   -> ConeKernel (dmap h d) (amap h a)
  ConeCokernel d a -> ConeCokernel (dmap h d) (amap h a)
  
-- | mapping of a cone under a 'Distributive' homomorphism.
cnMapDst :: (DiagrammaticApplicative h d, Hom Dst h)
  => h a b -> Cone Dst p d t n m a -> Cone Dst p d t n m b
cnMapDst h = cnMapDstStruct (tau $ range h) h

-- | mapping of a cone.
cnMap :: (DiagrammaticApplicative h d, Hom s h) => h a b -> Cone s p d t n m a -> Cone s p d t n m b
cnMap h c = case c of
  ConeProjective _ _ _ -> cnMapMlt h c
  ConeInjective _ _ _  -> cnMapMlt h c
  ConeKernel _ _       -> cnMapDst h c
  ConeCokernel _ _     -> cnMapDst h c

instance (DiagrammaticApplicative h d, HomMultiplicative h)
  => Applicative1 h (Cone Mlt p d t n m) where amap1 = cnMapMlt

instance (DiagrammaticApplicative h d, HomDistributive h)
  => Applicative1 h (Cone Dst p d t n m) where amap1 = cnMapDst

--------------------------------------------------------------------------------
-- Cone - Dual -

type instance Dual (Cone s p d t n m a) = Cone s (Dual p) d (Dual t) n m (Op a)

--------------------------------------------------------------------------------
-- coCone -

-- | to the dual cone, with its inverse 'coConeInv'.
coCone :: DiagrammaticDualisable s d => Struct s a -> Cone s p d t n m a -> Dual (Cone s p d t n m a)
coCone s c = case c of
  ConeProjective d t as -> ConeInjective (coDiagrammatic s d) t (fmap Op as)
  ConeInjective d t as  -> ConeProjective (coDiagrammatic s d) t (fmap Op as)
  ConeKernel d a        -> ConeCokernel (coDiagrammatic s d) (Op a)
  ConeCokernel d a      -> ConeKernel (coDiagrammatic s d) (Op a)

--------------------------------------------------------------------------------
-- cnFromOpOp -

-- | from @'Op' '.' 'Op'@.
cnFromOpOp :: DiagrammaticDualisable s d
  => ConeStruct s a -> Cone s p d t n m (Op (Op a)) -> Cone s p d t n m a
cnFromOpOp ConeStructMlt = cnMapMlt isoFromOpOpMlt
cnFromOpOp ConeStructDst = cnMapDst isoFromOpOpDst 


--------------------------------------------------------------------------------
-- coConeInv -

-- | from the dual cone, with its inverse 'coCone'.
coConeInv :: DiagrammaticDualisable s d
  => ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (Cone s p d t n m a) -> Cone s p d t n m a
coConeInv cs Refl Refl = cnFromOpOp cs . coCone (tauOp (cnStruct cs))

--------------------------------------------------------------------------------
-- ConeDuality -

-- | duality for 'Diagrammatic'-'Cone's.
data ConeDuality s d x y where
  ConeDuality :: Dual (Dual p) :~: p -> DiagrammaticDuality s d (d t n m) (d (Dual t) n m)
    -> ConeDuality s d (Cone s p d t n m) (Cone s (Dual p) d (Dual t) n m)

instance OpDualisable (ConeDuality s d) (ConeStruct s) where
  opdToOp (ConeDuality _ (DiagrammaticDuality _)) s     = coCone (cnStruct s)
  opdFromOp (ConeDuality rp (DiagrammaticDuality rt)) s = coConeInv s rp rt   

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
-- @'fmap' 'end' ('shell' c) '==' 'cnPoints' c@.
--
-- (2) If __@p@__ is equal to __'Injective'__ then holds:
-- @'fmap' 'start' ('shell' c) '==' 'cnPoints' c@.
shell :: Diagrammatic d => Cone s p d t n m a -> FinList n a
shell (ConeProjective _ _ as) = as
shell (ConeInjective _ _ as)  = as
shell (ConeKernel d k)        = k:|zero (start k :> q):|Nil where DiagramParallelLR _ q _ = diagram d
shell (ConeCokernel d k)      = k:|zero (q :> end k):|Nil where DiagramParallelRL _ q _ = diagram d

--------------------------------------------------------------------------------
-- cnPoints -

-- | the points of the underlying diagram, i.e. @'dgPoints' '.' 'cnDiagram'@. 
cnPoints :: (Diagrammatic d, Oriented a) => Cone s p d t n m a -> FinList n (Point a)
cnPoints = dgPoints . diagram

--------------------------------------------------------------------------------
-- cnArrows -

-- | the arrows of the underlying diagram, i.e. @'dgArrows' '.' 'cnDiagram'@.
cnArrows :: Diagrammatic d => Cone s p d t n m a -> FinList m a
cnArrows = dgArrows . diagram

--------------------------------------------------------------------------------
-- cnDstAdjZero -

-- | adjoins a 'zero' arrow to the diagram and the cone.
cnDstAdjZero :: Cone Dst p Diagram t n m a -> Cone Mlt p Diagram t n (m+1) a
cnDstAdjZero (ConeKernel d@(DiagramParallelLR _ r _) k)
  = ConeProjective (dgPrlAdjZero d) t (k:|zero (t:>r):|Nil) where t = start k
cnDstAdjZero c@(ConeCokernel _ _)
  = coConeInv ConeStructMlt Refl Refl $ cnDstAdjZero $ coCone Struct c


--------------------------------------------------------------------------------
-- ConeZeroHead -

-- | predicate for cones where the first arrow of its underlying diagram is equal to 'zero'.
newtype ConeZeroHead s p d t n m a = ConeZeroHead (Cone s p d t n m a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ConeZeroHead - Validable -

instance (Distributive a, Diagrammatic d, Validable (d t n (S m) a))
  => Validable (ConeZeroHead s p d t n (S m) a) where
  valid (ConeZeroHead c)
    = And [ valid c
          , relIsZero $ head $ dgArrows $ diagram c
          ]

instance ( Distributive a
         , Diagrammatic d
         , Entity (d t n (S m) a)
         , Typeable d, Typeable s, Typeable p, Typeable t, Typeable n, Typeable m
         )
  => Entity (ConeZeroHead s p d t n (S m) a)

--------------------------------------------------------------------------------
-- ConeZeroHead - Dual -

type instance Dual (ConeZeroHead s p d t n m a) = ConeZeroHead s (Dual p) d (Dual t) n m (Op a)

-- | to the dual, with its inverse 'coConeZeroHead'.
coConeZeroHead :: DiagrammaticDualisable s d
  => Struct s a -> ConeZeroHead s p d t n m a -> Dual (ConeZeroHead s p d t n m a)
coConeZeroHead s (ConeZeroHead c) = ConeZeroHead $ coCone s c

-- | from the bidual.
czFromOpOp :: DiagrammaticDualisable s d
  => ConeStruct s a -> ConeZeroHead s p d t n m (Op (Op a)) -> ConeZeroHead s p d t n m a
czFromOpOp s (ConeZeroHead c) = ConeZeroHead $ cnFromOpOp s c

-- | from the dual, with its inverse 'coConeZeroHead'.
coConeZeroHeadInv :: DiagrammaticDualisable s d
  => ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (ConeZeroHead s p d t n m a) -> ConeZeroHead s p d t n m a
coConeZeroHeadInv s rp rt (ConeZeroHead c)
  = ConeZeroHead $ coConeInv s rp rt c

--------------------------------------------------------------------------------
-- cnDiffHead -

-- | subtracts to every arrow of the underlying parallel diagram the first arrow and
-- adapts the shell accordingly.
cnDiffHead :: (Distributive a, Abelian a)
  => Cone Mlt p Diagram (Parallel d) n (m+1) a -> ConeZeroHead Mlt p Diagram (Parallel d) n (m+1) a
cnDiffHead (ConeProjective d t s) = ConeZeroHead $ case d of
  DiagramParallelLR _ _ _ -> ConeProjective (dgPrlDiffHead d) t (a:|fmap toZero as) where a:|as = s
  DiagramParallelRL _ _ _ -> ConeProjective (dgPrlDiffHead d) t (toZero a:|as) where a:|as = s
  where toZero a = zero (root a)
cnDiffHead c@(ConeInjective d _ _) = case d of
  DiagramParallelLR _ _ _ ->   coConeZeroHeadInv ConeStructMlt Refl Refl
                             $ cnDiffHead $ coCone Struct c
  DiagramParallelRL _ _ _ ->   coConeZeroHeadInv ConeStructMlt Refl Refl
                             $ cnDiffHead $ coCone Struct c

--------------------------------------------------------------------------------
-- cnZeroHead -

-- | embedding of a cone in a distributive structure to its multiplicative cone.
cnZeroHead :: Cone Dst p Diagram t n m a -> ConeZeroHead Mlt p Diagram t n (m+1) a
cnZeroHead = ConeZeroHead . cnDstAdjZero 

--------------------------------------------------------------------------------
-- cnKernel -

-- | the kernel cone of a zero headed parallel cone, i.e. the inverse of 'cnZeroHead'.
cnKernel :: (Distributive a, p ~ Projective, t ~ Parallel LeftToRight)
  => ConeZeroHead Mlt p Diagram t n (m+1) a -> Cone Dst p Diagram t n m a
cnKernel (ConeZeroHead (ConeProjective d _ cs)) = case d of
  DiagramParallelLR l r as -> ConeKernel (DiagramParallelLR l r (tail as)) (head cs)

--------------------------------------------------------------------------------
-- cnCokernel

-- | the cokernel cone of a zero headed parallel cone, i.e. the inverse of 'cnZeroHead'.
cnCokernel :: (Distributive a, p ~ Injective, t ~ Parallel RightToLeft)
  => ConeZeroHead Mlt p Diagram t n (m+1) a -> Cone Dst p Diagram t n m a
cnCokernel = coConeInv ConeStructDst Refl Refl . cnKernel . coConeZeroHead Struct

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

-- | validity of a 'Diagram'-'Cone'.
relConeDiagram :: Cone s p Diagram t n m a -> Statement
relConeDiagram (ConeProjective d t cs) = relConePrjMlt d t cs
relConeDiagram c@(ConeKernel _ _)      = relConeDiagram (cnDstAdjZero c)
relConeDiagram c                       = case coneStruct c of
  ConeStructMlt                       -> relConeDiagram (coCone Struct c)
  ConeStructDst                       -> relConeDiagram (coCone Struct c)

--------------------------------------------------------------------------------
-- relCone -

-- | validity of a 'Cone'.
relCone :: Diagrammatic d => Cone s p d t n m a -> Statement
relCone = relConeDiagram . coneDiagram

--------------------------------------------------------------------------------
-- Cone - Validable -

instance (Diagrammatic d, Validable (d t n m a)) => Validable (Cone s p d t n m a) where
  valid c = Label "Cone" :<=>:
    And [ valid (diagrammaticObject c)
        , relCone c
        ]

--------------------------------------------------------------------------------
-- Cone - Entity -

deriving instance Show (d t n m a) => Show (Cone s p d t n m a)
deriving instance Eq (d t n m a) => Eq (Cone s p d t n m a)

instance ( Diagrammatic d
         , Entity (d t n m a)
         , Typeable d, Typeable s, Typeable p, Typeable t, Typeable n, Typeable m, Typeable a
         ) => Entity (Cone s p d t n m a)


--------------------------------------------------------------------------------
-- Cone - Oriented -

instance ( Oriented a, Diagrammatic d, Entity (d (Parallel t) N2 m a)
         , Typeable d, Typeable s, Typeable p, Typeable t, Typeable m
         )
  => Oriented (Cone s p d (Parallel t) N2 m a) where
  type Point (Cone s p d (Parallel t) N2 m a) = Point a
  orientation c = orientation $ diagram c
  
--------------------------------------------------------------------------------
-- cnPrjOrnt -

-- | the projective cone on 'Orientation' with the underlying given diagram and tip with the given
-- point. 
cnPrjOrnt :: (Diagrammatic d, Entity p)
  => p -> d t n m (Orientation p) -> Cone Mlt Projective d t n m (Orientation p)
cnPrjOrnt p d = ConeProjective d p (amap1 (p:>) $ dgPoints $ diagram d)

cnPrjDstOrnt :: (Diagrammatic d, Entity p, t ~ Parallel LeftToRight, n ~ N2)
  => p -> d t n m (Orientation p) -> Cone Dst Projective d t n m (Orientation p)
cnPrjDstOrnt t d = ConeKernel d (t:>p) where DiagramParallelLR p _ _ = diagram d

--------------------------------------------------------------------------------
-- cnInjOrnt -

-- | the injective cone on 'Orientation' with the underlying given diagram and tip with the given
-- point. 
cnInjOrnt :: (Diagrammatic d, Entity p)
  => p -> d t n m (Orientation p) -> Cone Mlt Injective d t n m (Orientation p)
cnInjOrnt p d = ConeInjective d p (amap1 (:>p) $ dgPoints $ diagram d)

cnInjDstOrnt :: (Diagrammatic d, Entity p, t ~ Parallel RightToLeft, n ~ N2)
  => p -> d t n m (Orientation p) -> Cone Dst Injective d t n m (Orientation p)
cnInjDstOrnt t d = ConeCokernel d (q:>t) where DiagramParallelRL _ q _ = diagram d
  
instance ( Entity p
         , Diagrammatic d
         , XStandard p, XStandard (d t n m (Orientation p))
         ) => XStandard (Cone Mlt Projective d t n m (Orientation p)) where
  xStandard = do
    d <- xStandard
    p <- xStandard
    return (cnPrjOrnt p d)

instance ( Entity p, t ~ Parallel LeftToRight, n ~ N2
         , Diagrammatic d
         , XStandard p, XStandard (d t n m (Orientation p))
         ) => XStandard (Cone Dst Projective d t n m (Orientation p)) where
  xStandard = do
    d <- xStandard
    t <- xStandard
    return (cnPrjDstOrnt t d)
                                 
instance ( Entity p
         , Diagrammatic d
         , XStandard p, XStandard (d t n m (Orientation p))
         ) => XStandard (Cone Mlt Injective d t n m (Orientation p)) where
  xStandard = do
    d <- xStandard
    p <- xStandard
    return (cnInjOrnt p d)

instance ( Entity p, t ~ Parallel RightToLeft, n ~ N2
         , Diagrammatic d
         , XStandard p, XStandard (d t n m (Orientation p))
         ) => XStandard (Cone Dst Injective d t n m (Orientation p)) where
  xStandard = do
    d <- xStandard
    t <- xStandard
    return (cnInjDstOrnt t d)

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
  => FactorChain To n a -> Cone Mlt Projective Diagram (Chain To) (n+1) n a
cnPrjChainTo (FactorChain f d@(DiagramChainTo _ as))
  = ConeProjective d (start f) (cmp f as) where
  cmp :: Multiplicative a => a -> FinList n a -> FinList (n+1) a
  cmp f Nil     = f:|Nil
  cmp f (a:|as) = (a*c):|cs where cs@(c:|_) = cmp f as

--------------------------------------------------------------------------------
-- cnPrjChainToInv -

-- | the underlying factor chain of a projective chain to cone, i.e the inverse of
-- 'cnPrjChainToInv'.
cnPrjChainToInv :: Cone Mlt Projective Diagram (Chain To) (n+1) n a -> FactorChain To n a
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
  => FactorChain From n a -> Cone Mlt Projective Diagram (Chain From) (n+1) n a
cnPrjChainFrom (FactorChain f d@(DiagramChainFrom _ as))
  = ConeProjective d (start f) (cmp f as) where
  cmp :: Multiplicative a => a -> FinList n a -> FinList (n+1) a
  cmp f Nil     = f:|Nil
  cmp f (a:|as) = f :| cmp f' as where f' = a*f

--------------------------------------------------------------------------------
-- cnPrjChainFromInv -

-- | the underlying factor chain of a projective chain from cone, i.e. the inverse of
-- 'cnPrjChainFrom'.
cnPrjChainFromInv :: Cone Mlt Projective Diagram (Chain From) (n+1) n a -> FactorChain From n a
cnPrjChainFromInv (ConeProjective d _ (c:|_)) = FactorChain c d


