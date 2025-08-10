
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Entity.Diagram.Definition
-- Description : definition of diagrams on oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Diagram's on 'Oriented' structures.
module OAlg.Entity.Diagram.Definition
  (

    -- * Diagram
    Diagram(..), DiagramType(..), rt'
  , dgType, dgTypeRefl, dgPoints, dgCenter, dgArrows
  , dgMap, dgMapCnt, dgMapS
  , dgQuiver

     -- ** Chain
  , chnToStart, chnFromStart

    -- ** Parallel
  , dgPrlAdjZero
  , dgPrlTail, dgPrlDiffHead
  , dgPrlDiffTail

    -- * SomeDiagram
  , SomeDiagram(..), sdgMap

    -- * X
  , XDiagram(..)
  , xDiagram, xDiagramChain
  , xSomeDiagram, dstSomeDiagram
  , xSomeDiagramOrnt

  )
  where

import Control.Monad 

import Data.Kind
import Data.Typeable
import Data.Array as A hiding (range)
import Data.Foldable (toList)

import OAlg.Prelude hiding (T)

import OAlg.Category.Dualisable
import OAlg.Category.SDuality

import OAlg.Data.Either

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Hom.Definition
import OAlg.Hom.Oriented

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.FinList as S

import OAlg.Entity.Diagram.Quiver

--------------------------------------------------------------------------------
-- DiagramType -

-- | the types of a 'Diagram'.
data DiagramType
  = Empty
  | Discrete
  | Chain Site
  | Parallel Direction
  | Star Site
  | General
  deriving (Show,Eq,Ord)

----------------------------------------
-- DiagramType - Dual -

type instance Dual 'Empty                   = 'Empty
type instance Dual 'Discrete                = 'Discrete
type instance Dual ('Chain t)               = 'Chain (Dual t)
type instance Dual ('Parallel 'LeftToRight) = 'Parallel 'RightToLeft
type instance Dual ('Parallel 'RightToLeft) = 'Parallel 'LeftToRight
type instance Dual ('Star 'To)              = 'Star 'From
type instance Dual ('Star 'From)            = 'Star 'To
type instance Dual 'General                 = 'General


--------------------------------------------------------------------------------
-- rt'

-- | 'Dual' is well defined on diagram types.
rt' :: forall (t :: DiagramType) . Dual (Dual t) :~: t -> Dual (Dual (Dual t)) :~: Dual t
rt' Refl = Refl

--------------------------------------------------------------------------------
-- Diagram -

-- | diagram for a 'Oriented' structure __@a@__ of type __@t@__ having __@n@__ points
--   and __@m@__ arrows.
--
--   __Properties__ Let @d@ be in @'Diagram' __t__ __n__ __m__ __a__@ for a 'Oriented'
--   structure __@a@__, then holds:
--
--   (1) If @d@ matches @'DiagramChainTo' e as@ then holds: @e '==' 'end' a0@ and
--   @'start' ai '==' 'end' ai+1@ for all @i = 0..m-2@
--   where @a0':|'..':|'ai':|'..':|'am-1':|''Nil' = as@.
--
--   (2) If @d@ matches @'DiagramChainFrom' s as@ then holds: @s '==' 'start' a0@ and
--   @'end' ai '==' 'start' ai+1@ for all @i = 0..m-2@
--   where @a0':|'..':|'ai':|'..':|'am-1':|''Nil' = as@.
--
--   (3) If @d@ matches @'DiagramParallelLR' l r as@ then holds:
--   @'orientation' a '==' l':>'r@ for all @a@ in @as@.
--
--   (4) If @d@ matches @'DiagramParallelRL' l r as@ then holds:
--   @'orientation' a '==' r':>'l@ for all @a@ in @as@.
--
--   (5) If @d@ matches @'DiagramSink' e as@ then holds: @e '==' 'end' a@
--   for all @a@ in @as@.
--
--   (6) If @d@ matches @'DiagramSource' s as@ then holds: @s '==' 'start' a@
--   for all @a@ in @as@.
--
--   (7) If @d@ matches @'DiagramGeneral' ps aijs@ then holds@ @pi '==' 'start' aij@ and
--   @pj '==' 'end' aij@ for all @aij@ in @aijs@ and @ps = p0..pn-1@.
data Diagram t n m a where
  DiagramEmpty      :: Diagram 'Empty N0 N0 a
  DiagramDiscrete   :: FinList n (Point a) -> Diagram Discrete n N0 a  
  DiagramChainTo    :: Point a -> FinList m a -> Diagram (Chain To) (m+1) m a  
  DiagramChainFrom  :: Point a -> FinList m a -> Diagram (Chain From) (m+1) m a  
  DiagramParallelLR :: Point a -> Point a -> FinList m a
    -> Diagram (Parallel LeftToRight) N2 m a
  DiagramParallelRL :: Point a -> Point a -> FinList m a
    -> Diagram (Parallel RightToLeft) N2 m a
  DiagramSink       :: Point a -> FinList m a -> Diagram (Star To) (m+1) m a
  DiagramSource     :: Point a -> FinList m a -> Diagram (Star From) (m+1) m a  
  DiagramGeneral    :: FinList n (Point a) -> FinList m (a,Orientation N)
    -> Diagram General n m a

deriving instance (Show a, ShowPoint a) => Show (Diagram t n m a)
deriving instance (Eq a, EqPoint a) => Eq (Diagram t n m a)

--------------------------------------------------------------------------------
-- dgType -

-- | the type of a diagram.
dgType :: Diagram t n m a -> DiagramType
dgType d = case d of
  DiagramEmpty            -> Empty
  DiagramDiscrete _       -> Discrete
  DiagramChainTo _ _      -> Chain To
  DiagramChainFrom _ _    -> Chain From
  DiagramParallelLR _ _ _ -> Parallel LeftToRight
  DiagramParallelRL _ _ _ -> Parallel RightToLeft
  DiagramSink _ _         -> Star To
  DiagramSource _ _       -> Star From
  DiagramGeneral _ _      -> General

--------------------------------------------------------------------------------
-- dgTypeRefl -

-- | reflexivity of the underlying diagram type.
dgTypeRefl :: Diagram t n m a -> Dual (Dual t) :~: t
dgTypeRefl d = case d of
  DiagramEmpty            -> Refl
  DiagramDiscrete _       -> Refl
  DiagramChainTo _ _      -> Refl
  DiagramChainFrom _ _    -> Refl
  DiagramParallelLR _ _ _ -> Refl
  DiagramParallelRL _ _ _ -> Refl
  DiagramSink _ _         -> Refl
  DiagramSource _ _       -> Refl
  DiagramGeneral _ _      -> Refl

--------------------------------------------------------------------------------
-- dgPoints -

-- | the points of a diagram.
dgPoints :: Oriented a => Diagram t n m a -> FinList n (Point a)
dgPoints d = case d of
  DiagramEmpty            -> Nil
  DiagramDiscrete ps      -> ps
  DiagramChainTo e as     -> e:|amap1 start as
  DiagramChainFrom s as   -> s:|amap1 end as
  DiagramParallelLR p q _ -> p :| q :| Nil
  DiagramParallelRL p q _ -> p :| q :| Nil
  DiagramSink p as        -> p :| amap1 start as
  DiagramSource p as      -> p :| amap1 end as
  DiagramGeneral ps _     -> ps

--------------------------------------------------------------------------------
-- dgArrows -

-- | the arrows of a diagram.
dgArrows :: Diagram t n m a -> FinList m a
dgArrows d = case d of
  DiagramEmpty             -> Nil
  DiagramDiscrete _        -> Nil
  DiagramChainTo _ as      -> as
  DiagramChainFrom _ as    -> as
  DiagramParallelLR _ _ as -> as
  DiagramParallelRL _ _ as -> as
  DiagramSink _ as         -> as
  DiagramSource _ as       -> as
  DiagramGeneral _  as     -> amap1 fst as

--------------------------------------------------------------------------------
-- dgCenter -

-- | the center point of a 'Star'-diagram.
dgCenter :: Diagram (Star t) n m c -> Point c
dgCenter (DiagramSink c _)   = c
dgCenter (DiagramSource c _) = c

--------------------------------------------------------------------------------
-- Diagram - Duality -

type instance Dual1 (Diagram t n m)  = Diagram (Dual t) n m

instance (Show a, ShowPoint a) => ShowDual1 (Diagram t n m) a
instance (Eq a, EqPoint a) => EqDual1 (Diagram t n m) a

--------------------------------------------------------------------------------
-- dgMap -

-- | mapping of a diagram via a 'Covariant' homomorphism on 'Oriented' structures.
--
-- __Properties__ Let @d@ be in @'Diagram __t n m a__@ and
-- @'Covariant2' h@ in @'SVariant' 'Covariant' __h a b__@ with
-- @'HomOrientedDisjunctive' __s o h__@, then holds:
--
-- (1) @'dgArrows' ('dgMapCov' q h d) '==' 'amap1' ('amap' h) ('dgArrows' d)@.
--
-- (2) @'dgPoints' ('dgMapCov' q h d) '==' 'amap1' ('pmap' h) ('dgPoints' d)@.
--
-- where @q@ is any proxy in @__q s o__@.
dgMap :: HomOriented h => h x y -> Diagram t n m x -> Diagram t n m y
dgMap h d                  =  case d of
  DiagramEmpty             -> DiagramEmpty
  DiagramDiscrete ps       -> DiagramDiscrete (amap1 hPnt ps)
  DiagramChainTo e as      -> DiagramChainTo (hPnt e) (amap1 hArw as)
  DiagramChainFrom s as    -> DiagramChainFrom  (hPnt s) (amap1 hArw as)
  DiagramParallelLR l r as -> DiagramParallelLR (hPnt l) (hPnt r) (amap1 hArw as)
  DiagramParallelRL l r as -> DiagramParallelRL (hPnt l) (hPnt r) (amap1 hArw as)
  DiagramSink e as         -> DiagramSink (hPnt e) (amap1 hArw as)
  DiagramSource s as       -> DiagramSource (hPnt s) (amap1 hArw as)
  DiagramGeneral ps aijs   -> DiagramGeneral (amap1 hPnt ps)
                                (amap1 (\(a,o) -> (hArw a,o)) aijs)
  where hPnt = pmap h
        hArw = amap h

--------------------------------------------------------------------------------
-- dgMapCnt -

-- | mapping of a diagram via a 'Contravariant' homomorphism on 'Oriented' structures.
--
-- __Properties__ Let @d@ be in @'Diagram __t n m a__@ and
-- @'Contravariant2' h@ in @'SVariant' 'Contravariant' __h a b__@ with
-- @'HomOrientedDisjunctive' __s o h__@, then holds:
--
-- (1) @'dgArrows' ('dgMapCov' q h d) '==' 'amap1' ('amap' h) ('dgArrows' d)@.
--
-- (2) @'dgPoints' ('dgMapCov' q h d) '==' 'amap1' ('pmap' h) ('dgPoints' d)@.
--
-- where @q@ is any proxy in @__q s o__@.
dgMapCnt :: HomOrientedDisjunctive h
  => Variant2 Contravariant h x y -> Diagram t n m x -> Dual1 (Diagram t n m) y
dgMapCnt (Contravariant2 h) d = case d of
  DiagramEmpty             -> DiagramEmpty
  DiagramDiscrete ps       -> DiagramDiscrete (amap1 hPnt ps)
  DiagramChainTo e as      -> DiagramChainFrom (hPnt e) (amap1 hArw as)
  DiagramChainFrom s as    -> DiagramChainTo (hPnt s) (amap1 hArw as)
  DiagramParallelLR l r as -> DiagramParallelRL (hPnt l) (hPnt r) (amap1 hArw as)
  DiagramParallelRL l r as -> DiagramParallelLR (hPnt l) (hPnt r) (amap1 hArw as)
  DiagramSink e as         -> DiagramSource (hPnt e) (amap1 hArw as)
  DiagramSource s as       -> DiagramSink (hPnt s) (amap1 hArw as)
  DiagramGeneral ps aijs   -> DiagramGeneral
                                (amap1 hPnt ps)
                                (amap1 (\(a,o) -> (hArw a,opposite o)) aijs)
  where hPnt = pmap h
        hArw = amap h

--------------------------------------------------------------------------------
-- dgMapS -

-- | the canonically induced application given by 'dgMap' and 'dgMapCnt'.
dgMapS :: (HomOrientedDisjunctive h, t ~ Dual (Dual t))
  => h x y -> SDualBi (Diagram t n m) x -> SDualBi (Diagram t n m) y
dgMapS h (SDualBi s) = SDualBi $ case toVariant2 h of
  Right2 hCov        -> case s of
    Right1 d         -> Right1 (dgMap hCov d)
    Left1 d'         -> Left1 (dgMap hCov d')
  Left2 hCnt         -> case s of
    Right1 d         -> Left1 (dgMapCnt hCnt d)
    Left1 d'         -> Right1 (dgMapCnt hCnt d')

--------------------------------------------------------------------------------
-- Diagram - DualisableGBiDual1 -

dgToBidual :: (DualisableOriented s o, TransformableOrt s, TransformableGRefl o s)
  => Struct s x -> Diagram t n m x -> Diagram t n m (o (o x))
dgToBidual s = dgMap (Covariant2 (t' . t)) where
  Contravariant2 (Inv2 t _)  = isoO s
  Contravariant2 (Inv2 t' _) = isoO (tauO s) 

dgFromBidual :: (DualisableOriented s o, TransformableOrt s, TransformableGRefl o s)
  => Struct s x -> Diagram t n m (o (o x)) -> Diagram t n m x
dgFromBidual s = dgMap (Covariant2 (f . f')) where
  Contravariant2 (Inv2 _ f)  = isoO s
  Contravariant2 (Inv2 _ f') = isoO (tauO s) 

instance (Transformable s Type, DualisableOriented s o, TransformableOrt s, TransformableGRefl o s)
  => ReflexiveG s (->) o (Diagram t n m) where
  reflG s = Inv2 (dgToBidual s) (dgFromBidual s)

instance (DualisableOriented s o, Transformable s Type, TransformableGRefl o s, TransformableOrt s
         , t' ~ Dual t, t ~ Dual t'
         )
  => DualisableGBi s (->) o (Diagram t n m) (Diagram t' n m) where
  toDualGLft s = dgMapCnt (Contravariant2 t) where
    Contravariant2 (Inv2 t _) = isoO s

  toDualGRgt s = dgMapCnt (Contravariant2 t) where
    Contravariant2 (Inv2 t _) = isoO s


instance ( DualisableOriented s o, Transformable s Type, TransformableGRefl o s, TransformableOrt s
         , t ~ Dual (Dual t)
         )
  => DualisableGBiDual1 s (->) o (Diagram t n m)

--------------------------------------------------------------------------------
-- Diagram - FunctorialG -

instance HomOriented h => ApplicativeG (Diagram t n m) h (->) where amapG = dgMap

instance HomOriented h => ApplicativeGDual1 (Diagram t n m) h (->)

instance (HomOriented h, FunctorialOriented h) => FunctorialG (Diagram t n m) h (->)

instance
  ( HomOriented h
  , DualisableOriented s o
  , TransformableOrt s, TransformableGRefl o s
  , t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (Diagram t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h

instance
  ( HomOriented h
  , DualisableOriented s o
  , TransformableOrt s, TransformableGRefl o s
  , t ~ Dual (Dual t)
  )  
  => FunctorialG (SDualBi (Diagram t n m)) (HomDisj s o h) (->)

--------------------------------------------------------------------------------
-- Diagram - Validable -

instance Oriented a => Validable (Diagram t n m a) where
  valid d = case d of
    DiagramEmpty -> SValid
    DiagramDiscrete ps -> valid ps
    DiagramChainTo e as -> valid e && vld 0 e as where
      vld :: Oriented a => N -> Point a -> FinList m a -> Statement
      vld _ _ Nil     = SValid
      vld i e (a:|as) = And [ valid a
                            , lC :<=>: (end a == e):?>prm i
                            , vld (succ i) (start a) as
                            ]
                        
    DiagramParallelLR l r as -> valid o && vld 0 o as where 
      o = l:>r
      vld :: Oriented a => N -> Orientation (Point a) -> FinList m a -> Statement
      vld _ _ Nil = SValid
      vld i o (a:|as)
        = And [ valid a
              , lO :<=>: (orientation a == o):?>prm i
              , vld (succ i) o as
              ]

    DiagramSink e as -> valid e && vld 0 e as where
      vld :: Oriented a => N -> Point a -> FinList m a -> Statement
      vld _ _ Nil     = SValid
      vld i e (a:|as)
        = And [ valid a
              , lE :<=>: (end a == e):?>prm i
              , vld (succ i) e as
              ]

    DiagramGeneral ps aijs -> And [ valid ps
                                  , vld 0 (toArray ps) aijs
                                  ] where
      vld :: Oriented a
        => N -> Array N (Point a) -> FinList m (a,Orientation N) -> Statement
      vld _ _ Nil = SValid
      vld l ps ((a,i:>j):|aijs)
        = And [ valid a
              , lB :<=>: (inRange (bounds ps) i) :?> Params["l":=show l,"i":=show i]
              , lB :<=>: (inRange (bounds ps) j) :?> Params["l":=show l,"j":=show j]
              , lO :<=>: (orientation a == (ps!i):>(ps!j))
                         :?>Params["l":=show l,"(i,j)":=show (i,j)]
              , vld (succ l) ps aijs
              ]

    _ -> case dgTypeRefl d of
      Refl -> valid d' where
        SDualBi (Left1 d')          = amapG toOp (SDualBi (Right1 d))
        Contravariant2 (Inv2 toOp _) = isoOpOrt
    where prm :: N -> Message
          prm i = Params["i":=show i]
          lC = Label "chain"
          lE = Label "end"
          lO = Label "orientation"
          lB = Label "bound"


instance Oriented a => ValidableDual1 (Diagram t n m) a

--------------------------------------------------------------------------------
-- Diagram - Oriented -

type instance Point (Diagram (Parallel d) n m a) = Point a
instance ShowPoint a => ShowPoint (Diagram (Parallel d) n m a)
instance EqPoint a => EqPoint (Diagram (Parallel d) n m a)
instance Oriented a => ValidablePoint (Diagram (Parallel d) n m a)
instance TypeablePoint a => TypeablePoint (Diagram (Parallel d) n m a)
instance (Oriented a, Typeable d, Typeable n, Typeable m)
  => Oriented (Diagram (Parallel d) n m a) where
  orientation (DiagramParallelLR l r _) = l:>r
  orientation (DiagramParallelRL l r _) = r:>l

--------------------------------------------------------------------------------
-- dgQuiver -

-- | the underlying quiver of a diagram.
dgQuiver :: Oriented a => Diagram t n m a -> Quiver n m
dgQuiver DiagramEmpty = Quiver W0 Nil
dgQuiver (DiagramDiscrete ps) = Quiver (toW ps) Nil
dgQuiver (DiagramChainTo _ as) = Quiver (SW (toW os)) os where
  os = chnTo 0 as
  chnTo :: N -> FinList m x -> FinList m (Orientation N)
  chnTo _ Nil     = Nil
  chnTo j (_:|os) = (j' :> j):|chnTo j' os where j' = succ j
dgQuiver (DiagramParallelLR _ _ as) = Quiver attest (amap1 (const (0:>1)) as)
dgQuiver (DiagramSink _ as) = Quiver (SW (toW os)) os where
  os = snk 1 as
  snk :: N -> FinList m x -> FinList m (Orientation N)
  snk _ Nil     = Nil
  snk j (_:|os) = (j:>0):|snk (succ j) os
dgQuiver (DiagramGeneral ps os) = Quiver (toW ps) (amap1 snd os)
dgQuiver d = case dgTypeRefl d of
  Refl -> coQuiverInv $ dgQuiver d' where
    SDualBi (Left1 d') = amapG toOp (SDualBi (Right1 d))
    Contravariant2 (Inv2 toOp _) = isoOpOrt

--------------------------------------------------------------------------------
-- chnToStart -

-- | the last point of the chain.
chnToStart :: Oriented a => Diagram (Chain To) n m a -> Point a
chnToStart (DiagramChainTo e as) = case as of
    Nil   -> e
    a:|as -> st (start a) as where
      st :: Oriented a => Point a -> FinList m a -> Point a
      st s Nil      = s
      st _ (a:|as)  = st (start a) as

--------------------------------------------------------------------------------
-- chnFromStart -

-- | the first point of the chain.
chnFromStart :: Diagram (Chain From) n m a -> Point a
chnFromStart (DiagramChainFrom s _) = s

--------------------------------------------------------------------------------
-- chnFromEnd -

chnFromEnd :: Oriented a => Diagram (Chain From) n m a -> Point a
chnFromEnd d@(DiagramChainFrom _ _) = chnToStart d' where
  SDualBi (Left1 d') = amapG toOp (SDualBi (Right1 d))
  Contravariant2 (Inv2 toOp _) = isoOpOrt

--------------------------------------------------------------------------------
-- Diagram (Chain t) - Oriented -

type instance Point (Diagram (Chain t) n m a) = Point a
instance ShowPoint a => ShowPoint (Diagram (Chain t) n m a)
instance EqPoint a => EqPoint (Diagram (Chain t) n m a)
instance Oriented a => ValidablePoint (Diagram (Chain t) n m a)
instance TypeablePoint a => TypeablePoint (Diagram (Chain t) n m a)
instance (Oriented a, Typeable t, Typeable n, Typeable m) => Oriented (Diagram (Chain t) n m a) where
  
  start (DiagramChainFrom s _) = s
  start d@(DiagramChainTo _ _) = chnToStart d

  end d@(DiagramChainFrom _ _) = chnFromEnd d
  end (DiagramChainTo e _)     = e

--------------------------------------------------------------------------------
-- dgPrlAdjZero -

-- | adjoins a 'zero' arrow as the first parallel arrow.
dgPrlAdjZero :: Distributive a
  => Diagram (Parallel LeftToRight) n m a -> Diagram (Parallel LeftToRight) n (m+1) a
dgPrlAdjZero (DiagramParallelLR l r as) = DiagramParallelLR l r (zero (l:>r):|as)

--------------------------------------------------------------------------------
-- dgPrlTail -

-- | the _/tail/__ of a parallel diagram.
dgPrlTail :: Diagram (Parallel d) n (m+1) a -> Diagram (Parallel d) n m a
dgPrlTail (DiagramParallelLR l r as) = DiagramParallelLR l r (tail as)
dgPrlTail (DiagramParallelRL l r as) = DiagramParallelRL l r (tail as)

--------------------------------------------------------------------------------
-- dgPrlDiffTail -

-- | subtracts the first arrow to all the others an drops it.
dgPrlDiffTail :: Abelian a
  => Diagram (Parallel d) n (m+1) a -> Diagram (Parallel d) n m a
dgPrlDiffTail = dgPrlTail . dgPrlDiffHead

--------------------------------------------------------------------------------
-- dgPrlDiffHead -

-- | subtracts to every arrow of the parallel diagram the first arrow.
dgPrlDiffHead :: Abelian a
  => Diagram (Parallel d) n (m+1) a -> Diagram (Parallel d) n (m+1) a
dgPrlDiffHead d = case d of
  DiagramParallelLR l r as -> DiagramParallelLR l r (amap1 (diff $ head as) as)
  DiagramParallelRL l r as -> DiagramParallelRL l r (amap1 (diff $ head as) as)
  where diff a x = x - a

--------------------------------------------------------------------------------
-- XDiagram -

-- | generator for random variables of diagrams.
data XDiagram t n m a where
  XDiagramEmpty      :: XDiagram 'Empty N0 N0 a
  XDiagramDiscrete   :: Any n -> X (Point a) -> XDiagram Discrete n N0 a
  XDiagramChainTo    :: Any m -> XOrtSite To a -> XDiagram (Chain To) (m+1) m a  
  XDiagramChainFrom  :: Any m -> XOrtSite From a -> XDiagram (Chain From) (m+1) m a
  XDiagramParallelLR :: Any m -> XOrtOrientation a
    -> XDiagram (Parallel LeftToRight) N2 m a
  XDiagramParallelRL :: Any m -> XOrtOrientation a
    -> XDiagram (Parallel RightToLeft) N2 m a
  XDiagramSink       :: Any m -> XOrtSite To a -> XDiagram (Star To) (m+1) m a
  XDiagramSource     :: Any m -> XOrtSite From a -> XDiagram (Star From) (m+1) m a

--------------------------------------------------------------------------------
-- XDiagram - Dualisable -

type instance Dual1 (XDiagram t n m) = XDiagram (Dual t) n m
type instance Dual (XDiagram t n m a) = Dual1 (XDiagram t n m) (Op a)

-- | the co-'XDiagram'.
coXDiagram :: XDiagram t n m a -> Dual (XDiagram t n m a)
coXDiagram xd = case xd of
  XDiagramEmpty           -> XDiagramEmpty
  XDiagramDiscrete n xp   -> XDiagramDiscrete n xp
  XDiagramChainTo m xe    -> XDiagramChainFrom m (coXOrtSite xe)
  XDiagramChainFrom m xs  -> XDiagramChainTo m (coXOrtSite xs)
  XDiagramParallelLR m xo -> XDiagramParallelRL m (coXOrtOrientation xo)
  XDiagramParallelRL m xo -> XDiagramParallelLR m (coXOrtOrientation xo)
  XDiagramSink m xe       -> XDiagramSource m (coXOrtSite xe)
  XDiagramSource m xs     -> XDiagramSink m (coXOrtSite xs)

--------------------------------------------------------------------------------
-- xDiagram -

xDiscrete :: p a -> Any n -> X (Point a) -> X (Diagram Discrete n N0 a)
xDiscrete _ _ XEmpty    = XEmpty
xDiscrete _ W0 _        = return (DiagramDiscrete Nil)
xDiscrete pa (SW n') xp = do
  DiagramDiscrete ps <- xDiscrete pa n' xp
  p <- xp
  return (DiagramDiscrete (p:|ps))

xChain :: Oriented a => Any m -> XOrtSite To a -> X (Diagram (Chain To) (m+1) m a)
xChain m xe@(XEnd xp _) = do
  e      <- xp
  (_,as) <- xchn m xe e
  return (DiagramChainTo e as)
  where xchn :: Oriented a => Any m -> XOrtSite To a -> Point a -> X (Point a, FinList m a)
        xchn W0 _ e                    = return (e,Nil)
        xchn (SW m') xe@(XEnd _ xea) e = do
          (s,as) <- xchn m' xe e
          a <- xea s
          return (start a,as |: a)
          
xParallel :: Oriented a
  => Any m -> XOrtOrientation a -> X (Diagram (Parallel LeftToRight) N2 m a)
xParallel W0 xo = do
  l <- xoPoint xo
  r <- xoPoint xo
  return (DiagramParallelLR l r Nil)
xParallel (SW m') xo = do
  DiagramParallelLR l r as <- xParallel m' xo
  a <- xoArrow xo (l:>r)
  return (DiagramParallelLR l r (a:|as))

xSink :: Oriented a
  => Any m -> XOrtSite To a -> X (Diagram (Star To) (m+1) m a)
xSink W0 xe = do
  e <- xosPoint xe
  return (DiagramSink e Nil)
xSink (SW m') xe@(XEnd _ xea) = do
  DiagramSink e as <- xSink m' xe
  a <- xea e
  return (DiagramSink e (a:|as))


-- | the induced random variables of diagrams.
xDiagram :: Oriented a => Dual (Dual t) :~: t
  -> XDiagram t n m a -> X (Diagram t n m a)
xDiagram rt@Refl xd = case xd of
  XDiagramEmpty           -> return DiagramEmpty
  XDiagramDiscrete n xp   -> xDiscrete xd n xp
  XDiagramChainTo m xs    -> xChain m xs
  XDiagramParallelLR m xo -> xParallel m xo
  XDiagramSink m xe       -> xSink m xe
  _                       ->   amap1 (\d' -> let SDualBi (Right1 d)
                                                   = amapG fromOp (SDualBi (Left1 d'))
                                                 Contravariant2 (Inv2 _ fromOp) = isoOpOrt
                                             in d)
                             $ xDiagram (rt' rt) $ coXDiagram xd

-- | random variable for 'Chain's.
xDiagramChain :: (Oriented x, Attestable m, n ~ m + 1)
  => XOrtSite t x -> X (Diagram (Chain t) n m x)
xDiagramChain xo@(XStart _ _) = xDiagram Refl (XDiagramChainFrom m xo) where m = attest
xDiagramChain xo@(XEnd _ _)   = xDiagram Refl (XDiagramChainTo m xo) where m = attest

--------------------------------------------------------------------------------
-- X (Diagram t n m OS) - Standard -

instance (Oriented a, n ~ N0, m ~ N0) => XStandard (Diagram 'Empty n m a) where
  xStandard = xDiagram Refl XDiagramEmpty

instance (Oriented a, m ~ N0, XStandardPoint a, Attestable n)
  => XStandard (Diagram Discrete n m a) where
  xStandard = xDiagram Refl (XDiagramDiscrete n xStandard) where n = attest

instance (Oriented a, n ~ N2, XStandardOrtOrientation a, Attestable m)
  => XStandard (Diagram (Parallel LeftToRight) n m a) where
  xStandard = xDiagram Refl (XDiagramParallelLR m xStandardOrtOrientation) where
    m = attest

instance (Oriented a, n ~ N2, XStandardOrtOrientation a, Attestable m)
  => XStandard (Diagram (Parallel RightToLeft) n m a) where
  xStandard = xDiagram Refl (XDiagramParallelRL m xStandardOrtOrientation) where
    m = attest

instance (Oriented a, XStandardOrtSite To a, Attestable m)
  => XStandard (Diagram (Star To) (S m) m a) where
  xStandard = xDiagram Refl (XDiagramSink m xStandardOrtSite) where m = attest

instance (Oriented a, XStandardOrtSite From a, Attestable m)
  => XStandard (Diagram (Star From) (S m) m a) where
  xStandard = xDiagram Refl (XDiagramSource m xStandardOrtSite) where m = attest

--------------------------------------------------------------------------------
-- X (Diagram (Chain t) (m+1) m -

instance (Oriented a, XStandardOrtSite t a, Attestable m, n ~ m + 1)
  => XStandard (Diagram (Chain t) n m a) where
  xStandard = xDiagramChain xStandardOrtSite


instance (Oriented x, XStandardOrtSite To x, XStandardOrtSite From x, Attestable m, n ~ m+1)
  => XStandardDual1 (SDualBi (Diagram (Chain To) n m)) x

instance (Oriented x, XStandardOrtSite From x, Attestable m, n ~ m+1)
  => XStandardDual1 (Diagram (Chain To) n m) x

instance (Attestable m, n ~ m+1)
  => TransformableG (SDualBi (Diagram (Chain To) n m)) OrtSiteX EqE where
  tauG Struct = Struct

instance (Oriented x, XStandardOrtSite To x, XStandardOrtSite From x, Attestable m, n ~ m+1)
  => XStandardDual1 (SDualBi (Diagram (Chain From) n m)) x

instance (Oriented x, XStandardOrtSite To x, Attestable m, n ~ m+1)
  => XStandardDual1 (Diagram (Chain From) n m) x
  
instance (Attestable m, n ~ m+1)
  => TransformableG (SDualBi (Diagram (Chain From) n m)) OrtSiteX EqE where
  tauG Struct = Struct

--------------------------------------------------------------------------------
-- SomeDiagram -

-- | some diagram.
data SomeDiagram a where
  SomeDiagram :: Diagram t n m a -> SomeDiagram a

deriving instance Oriented a => Show (SomeDiagram a)

instance Oriented a => Eq (SomeDiagram a) where
  SomeDiagram a == SomeDiagram b
    = and [ dgType a == dgType b
          , eqPnts a b
          , eqArws a b
          , eqOrnt a b
          ]
    where
      eqPnts :: Oriented x => Diagram t n m x -> Diagram t' n' m' x -> Bool
      eqPnts a b = (toList $ dgPoints a) == (toList $ dgPoints b)

      eqArws :: Oriented x => Diagram t n m x -> Diagram t' n' m' x -> Bool
      eqArws a b = (toList $ dgArrows a) == (toList $ dgArrows b)

      eqOrnt :: Diagram t n m x -> Diagram t' n' m' x -> Bool
      eqOrnt (DiagramGeneral _ o) (DiagramGeneral _ o')
        = (toList $ amap1 snd o) == (toList $ amap1 snd o')
      eqOrnt _ _ = True

instance Oriented a => Validable (SomeDiagram a) where
  valid (SomeDiagram d) = valid d

--------------------------------------------------------------------------------
-- sdgMap -

sdgMap :: (HomOriented h, DualisableOriented s o, TransformableGRefl o s, TransformableOrt s)
  => HomDisj s o h x y -> SomeDiagram x -> SomeDiagram y
sdgMap h (SomeDiagram d)   = case dgTypeRefl d of
  Refl                    -> case amapG h (SDualBi (Right1 d)) of
    SDualBi (Right1 d')  -> SomeDiagram d'
    SDualBi (Left1 d')   -> SomeDiagram d'
  
instance (HomOriented h, DualisableOriented s o, TransformableGRefl o s, TransformableOrt s)
  => ApplicativeG SomeDiagram (HomDisj s o h) (->) where
  amapG = sdgMap

instance ( HomOriented h, DualisableOriented s o
         , TransformableGRefl o s, TransformableOrt s
         ) => FunctorialG SomeDiagram (HomDisj s o h) (->)

--------------------------------------------------------------------------------
-- xSomeDiagram -

-- | the induced random variable of some diagrams.
xSomeDiagram :: Oriented a
  => X SomeNatural
  -> XOrtSite To a -> XOrtSite From a
  -> XOrtOrientation a
  -> X (SomeDiagram a)
xSomeDiagram xn xTo xFrom xO = do
  n <- xn
  case n of
    SomeNatural W0 -> join $ xOneOf (xe xTo:xsd W0 xTo xFrom xO)
    SomeNatural n  -> join $ xOneOf (xsd n xTo xFrom xO)
  where

  xe :: Oriented a => x a -> X (SomeDiagram a)
  xe _ = xDiagram Refl (XDiagramEmpty) >>= return . SomeDiagram

  xsd :: Oriented a
    => Any n
    -> XOrtSite To a -> XOrtSite From a
    -> XOrtOrientation a
    -> [X (SomeDiagram a)]
  xsd n xTo xFrom xO
    = [ xDiscrete n xp
      , xChainTo n xTo
      , xChainFrom n xFrom
      , xParallelLR n xO
      , xParallelRL n xO
      , xSink n xTo
      , xSource n xFrom
      ]
    where xp = xoPoint xO

  xDiscrete :: Oriented a => Any n -> X (Point a) -> X (SomeDiagram a)
  xDiscrete n xp
    = amap1 SomeDiagram $ xDiagram Refl (XDiagramDiscrete n xp)

  xChainTo :: Oriented a => Any n -> XOrtSite To a -> X (SomeDiagram a)
  xChainTo n xTo
    = amap1 SomeDiagram $ xDiagram Refl (XDiagramChainTo n xTo)

  xChainFrom :: Oriented a => Any n -> XOrtSite From a -> X (SomeDiagram a)
  xChainFrom n xFrom = amap1 (sdgMap f) $ xChainTo n (coXOrtSite xFrom) where
    Contravariant2 (Inv2 _ f) = isoOpOrt
  
  xParallelLR :: Oriented a => Any n -> XOrtOrientation a -> X (SomeDiagram a)
  xParallelLR n xO = amap1 SomeDiagram $ xDiagram Refl (XDiagramParallelLR n xO)
   
  xParallelRL :: Oriented a => Any n -> XOrtOrientation a -> X (SomeDiagram a)
  xParallelRL n xO = amap1 (sdgMap f) $ xParallelLR n (coXOrtOrientation xO) where
    Contravariant2 (Inv2 _ f) = isoOpOrt
    
  xSink :: Oriented a => Any n -> XOrtSite To a -> X (SomeDiagram a)
  xSink n xTo = amap1 SomeDiagram $ xDiagram Refl (XDiagramSink n xTo)

  xSource :: Oriented a => Any n -> XOrtSite From a -> X (SomeDiagram a)
  xSource n xFrom = amap1 (sdgMap f) $ xSink n (coXOrtSite xFrom) where
    Contravariant2 (Inv2 _ f) = isoOpOrt

--------------------------------------------------------------------------------
-- dstSomeDiagram -

-- | distribution of a random variable of some diagrams.
dstSomeDiagram :: Oriented a => Int -> X (SomeDiagram a) -> IO ()
dstSomeDiagram n xd = putDstr cnstr n xd where
  cnstr (SomeDiagram a) = [aspCnstr a]

--------------------------------------------------------------------------------
-- xSomeDiagramOrnt -

-- | random variable of some diagram of @'Orientation' __p__@.
xSomeDiagramOrnt :: Entity p => X SomeNatural -> X p -> X (SomeDiagram (Orientation p))
xSomeDiagramOrnt xn xp
  = xSomeDiagram xn (xEndOrnt xp) (xStartOrnt xp) (xoOrnt xp)


xsd :: X (SomeDiagram OS)
xsd = xSomeDiagramOrnt xn xStandard where xn = amap1 someNatural $ xNB 0 20

