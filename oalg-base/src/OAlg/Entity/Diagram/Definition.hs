
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- {-# LANGUAGE UndecidableInstances #-}
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
{-
    -- * Diagram
    Diagram(..), DiagramType(..), rt'
  , dgType, dgTypeRefl, dgPoints, dgCenter, dgArrows, dgMap
  , dgQuiver

     -- ** Chain
  , chnToStart, chnFromStart

    -- ** Parallel
  , dgPrlAdjZero
  , dgPrlTail, dgPrlDiffHead
  , dgPrlDiffTail


    -- ** Duality
  , coDiagram
  , DiagramDuality(..), DiagramOpDuality
  , dgOpDuality, dgOpDualityOrt

    -- * SomeDiagram
  , SomeDiagram(..), sdgMap

    -- ** Duality
  , SomeDiagramDuality(..), SomeDiagramOpDuality
  , sdgOpDuality, sdgOpDualityOrt

    -- * X
  , XDiagram(..)
  , xDiagram
  , xSomeDiagram, dstSomeDiagram
  , xSomeDiagramOrnt
-}
  )
  where

import Control.Monad 

import Data.Kind
import Data.Typeable
import Data.Array as A hiding (range)
import Data.Foldable (toList)

import OAlg.Prelude hiding (T)

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Proxy

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Definition

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
type instance Dual ('Chain 'From)           = 'Chain 'To
type instance Dual ('Chain 'To)             = 'Chain 'From 
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
-- dgMapCov -

-- | mapping of a diagram via a 'Covariant' homomorphism on 'Oriented' structures.
--
-- __Properties__ Let @d@ be in @'Diagram __t n m a__@ and
-- @'Covariant2' h@ in @'HomVariant' 'Covariant' __h a b__@ with
-- @'HomDisjunctiveOriented' __s o h__@, then holds:
--
-- (1) @'dgArrows' ('dgMapCov' q h d) '==' 'amap1' ('amap' h) ('dgArrows' d)@.
--
-- (2) @'dgPoints' ('dgMapCov' q h d) '==' 'amap1' ('pmap' h) ('dgPoints' d)@.
--
-- where @q@ is any proxy in @__q s o__@.
dgMapCov :: HomDisjunctiveOriented o h
  => q o -> HomVariant Covariant h a b -> Diagram t n m a -> Diagram t n m b
dgMapCov _ (Covariant2 h) d = case d of
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


{-
instance (HomOriented h, SDualisableOriented s o)
  => ApplicativeG (Diagram t n m) (HomVariant Covariant (HomOrt s o h)) (->) where
  amapG h = dgMapCov (q h) h where
    q :: HomVariant Covariant (HomOrt s o h) x y -> Proxy2 s o
    q _ = Proxy2
-}

--------------------------------------------------------------------------------
-- dgMapCnt -

-- | mapping of a diagram via a 'Contravariant' homomorphism on 'Oriented' structures.
--
-- __Properties__ Let @d@ be in @'Diagram __t n m a__@ and
-- @'Contravariant2' h@ in @'HomVariant' 'Contravariant' __h a b__@ with
-- @'HomDisjunctiveOriented' __s o h__@, then holds:
--
-- (1) @'dgArrows' ('dgMapCov' q h d) '==' 'amap1' ('amap' h) ('dgArrows' d)@.
--
-- (2) @'dgPoints' ('dgMapCov' q h d) '==' 'amap1' ('pmap' h) ('dgPoints' d)@.
--
-- where @q@ is any proxy in @__q s o__@.
dgMapCnt :: HomDisjunctiveOriented o h
  => q o -> HomVariant Contravariant h a b -> Diagram t n m a -> Diagram (Dual t) n m b
dgMapCnt _ (Contravariant2 h) d = case d of
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
-- SDualisableOrientedRefl -

class SDualisableOriented s s o => SDualisableOrientedRefl s o

instance (TransformableOrt s, TransformableOp s) => SDualisableOrientedRefl s Op

--------------------------------------------------------------------------------
-- Diagram - Duality -

type instance Dual1 (Diagram t n m)  = Diagram (Dual t) n m

dgMapCovEmpty :: (TransformableOrt s, SDualisableOriented r s o)
  => HomVariant Covariant (HomOrtEmpty r s o) x y -> Diagram t n m x -> Diagram t n m y
dgMapCovEmpty h = dgMapCov (q h) h where
  q :: HomVariant Covariant (HomOrtEmpty r s o) x y -> Proxy o
  q _ = Proxy

dgMapCntEmpty :: (TransformableOrt s, SDualisableOriented r s o)
  => HomVariant Contravariant (HomOrtEmpty r s o) x y
  -> Diagram t n m x -> Diagram (Dual t) n m y
dgMapCntEmpty h = dgMapCnt (q h) h where
  q :: HomVariant v (HomOrtEmpty r s o) x y -> Proxy o
  q _ = Proxy

instance (TransformableOrt s, SDualisableOrientedRefl Ort o)
  => ReflexiveG s (->) o (Diagram t n m) where
  reflG s = Inv2 u v where
    r = tauOrt s
    Contravariant2 t = homOrtToDualEmpty r
    Contravariant2 t' = homOrtToDualEmpty (tau1 r)
    u = dgMapCovEmpty $ Covariant2 (t' . t)

    Contravariant2 f = homOrtFromDualEmpty r
    Contravariant2 f' = homOrtFromDualEmpty (tau1 r)
    v = dgMapCovEmpty $ Covariant2 (f . f')

instance (TransformableOrt s, SDualisableOrientedRefl Ort o)
  => ReflexiveG s (->) o (SDual (Diagram t n m)) where
  reflG s = Inv2 (mapSDual u) (mapSDual v) where Inv2 u v = reflG s

instance ( TransformableOrt s, SDualisableOrientedRefl Ort o
         , TransformableGRefl o s
         , SDualisableOriented Ort s o
         , Dual (Dual t) ~ t
         )
  => DualisableGBi s (->) o (Diagram t n m) (SDual (Diagram t n m)) where
  toDualGLft s = SDual . dgMapCntEmpty (homOrtToDualEmpty s)
  toDualGRgt s = dgMapCntEmpty (homOrtToDualEmpty s) . fromSDual

instance ( TransformableOrt s, SDualisableOrientedRefl Ort o
         , TransformableGRefl o s
         , SDualisableOriented Ort s o
         , Dual (Dual t) ~ t
         )
  => SDualisable s o (Diagram t n m)


deriving instance (Show a, ShowPoint a) => Show (SDuality (Diagram t n m) a)

dgToOp :: Oriented x => HomOrtEmpty Ort Ort Op x (Op x)
dgToOp = t where Contravariant2 t = homOrtToDual (Struct :: Oriented x => Struct Ort x)

dgFromOp :: Oriented x => HomOrtEmpty Ort Ort Op (Op x) x
dgFromOp = f where Contravariant2 f = homOrtFromDual (Struct :: Oriented x => Struct Ort x)

{-
homOrtToDualOp :: (TransformableOrt s, TransformableOp s)
  => Struct s x -> HomOrtEmpty Ort s Op x (Op x)
homOrtToDualOp s = t where Contravariant2 t = homOrtToDual s

type DiagramDuaity t n m = SDuality (Diagram t n m) (SDual (Diagram t n m))
-}


{-
--------------------------------------------------------------------------------
-- dgToOp -

-- | to the dual diagram accroding to the @__Op__@-duality with inverse 'dgFromOp'.
dgToOpS :: Dual (Dual t) :~: t -> Struct Ort x -> Diagram t n m x -> SDual (Diagram t n m) (Op x)
dgToOpS Refl = sdlToDualLft

-- | to the dual diagram accroding to the @__Op__@-duality with inverse 'dgFromOp'.
dgToOp :: Oriented x =>  Dual (Dual t) :~: t -> Diagram t n m x -> Diagram (Dual t) n m (Op x)
dgToOp r d = fromSDual $ dgToOpS r (s d) d where
  s :: Oriented x => q x -> Struct Ort x
  s _ = Struct

--------------------------------------------------------------------------------
-- dgFromOp -

-- | from the dual diagram accroding to the @__Op__@-duality with inverse 'dgToOp'.
dgFromOpS :: Dual (Dual t) :~: t -> Struct Ort x -> SDual (Diagram t n m) (Op x) -> Diagram t n m x
dgFromOpS Refl = sdlFromDualLft

-- | from the dual diagram accroding to the @__Op__@-duality
dgFromOp :: Oriented x => Dual (Dual t) :~: t -> Diagram (Dual t) n m (Op x) -> Diagram t n m x
dgFromOp r d' = dgFromOpS r (s d') (SDual d') where
  s :: Oriented x => q (Op x) -> Struct Ort x
  s _ = Struct

--------------------------------------------------------------------------------
-- DiagramDuality -

type DiagramDuality t n m = SDuality (Diagram t n m) (SDual (Diagram t n m))


ff :: ( Morphism h
         , ApplicativeG (SDuality (Diagram t n m) (SDual (Diagram t n m))) h (->)
         , TransformableOrt s, TransformableTyp s
         , SDualisableOriented s o
         , Dual (Dual t) ~ t
         )
  => HomOrt s o h x y -> DiagramDuality t n m x -> DiagramDuality t n m y
ff = amapG


instance ( Morphism h
         , ApplicativeG (SDuality (Diagram t n m) (SDual (Diagram t n m))) h (->)
         , TransformableOrt s, TransformableTyp s
         , SDualisableOriented s o
         , Dual (Dual t) ~ t
         )
  => ApplicativeG (SDuality (Diagram t n m) (SDual (Diagram t n m))) (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h




--------------------------------------------------------------------------------
-- Diagram - Dual -


type instance Dual (Diagram t n m a) = Dual1 (Diagram t n m) (Op a)

--------------------------------------------------------------------------------
-- SDualDigram -

newtype SDuality d s (o :: Type -> Type) x = SDuality (Either1 d (Dual1 d) x)


sdProxy :: SDuality d s o x -> Proxy2 s o
sdProxy _ = Proxy2


class HomDisjunctiveOriented s o h => SD s o h d where
  sdMapCov :: q s o -> HomVariant Covariant h x y -> d x -> d y
  sdMapCnt :: q s o -> HomVariant Contravariant h x y -> d x -> (Dual1 d) y

instance HomDisjunctiveOriented s o h => SD s o h (Diagram t n m) where
  sdMapCov = dgMapCov
  sdMapCnt = dgMapCnt

sdMapLeft :: SD s o h d => q s o -> h x y -> d x -> SDuality d s o y
sdMapLeft q h d = SDuality $ case toVariant2 h of
  Right2 hCov -> Left1 $ sdMapCov q hCov d
  Left2 hCnt  -> Right1 $ sdMapCnt q hCnt d

sdMapRight :: (SD s o h d, Dual1 (Dual1 d) ~ d) => q s o -> h x y -> Dual1 d x -> SDuality d s o y
sdMapRight q h d = SDuality $ case toVariant2 h of
    Right2 hCov -> Right1 $ sdMapCov q hCov d
    -- Left2 hCnt  -> Left1 $ sdMapCnt q hCnt d
-}

{-
--------------------------------------------------------------------------------
-- dgMap -

dgMapLeft :: HomDisjunctiveOriented s o h
  => q s o -> h a b -> Diagram t n m a -> SDualDiagram s o t n m b
dgMapLeft q h d = SDualDiagram $ case toVariant2 h of
  Right2 hCov -> Left1 $ dgMapCov q hCov d
  Left2 hCnt  -> Right1 $ dgMapCnt q hCnt d

dgMapRight :: (HomDisjunctiveOriented s o h, Dual (Dual t) ~ t)
  => q s o -> h a b -> Diagram (Dual t) n m a -> SDualDiagram s o t n m b
dgMapRight q h d     = SDualDiagram $ case toVariant2 h of
    Right2 hCov -> Right1 $ dgMapCov q hCov d
    Left2 hCnt  -> Left1 $ dgMapCnt q hCnt d

dgMap :: (HomDisjunctiveOriented s o h, Dual (Dual t) ~ t)
  => h a b -> SDualDiagram s o t n m a -> SDualDiagram s o t n m b
dgMap h s@(SDualDiagram d) = either1 (dgMapLeft q h) (dgMapRight q h) d where q = sdProxy s


instance HomDisjunctiveOriented s o h
  => ApplicativeG (SDualDiagram s o Discrete n m) h (->) where
  amapG = dgMap
-}

{-
--------------------------------------------------------------------------------
-- dgMap -

-- | mapping of a diagram via a homomorphism on 'Oriented' structures.
--
-- __Definition__ Let @h@ be in @__h__ __a__ __b__@ and @d@ in @'Diagram' ___t__ __n__ __m__ __a__@
-- with @'Hom' 'Ort' __h__@, then we define @d' = 'dgMap' h d@ as follows: Let @hPnt = 'pmap' h@ and
-- @hArw = ''amap' h@ in
--
-- @
-- d' = case d of
--   DiagramEmpty             -> DiagramEmpty
--   DiagramDiscrete ps       -> DiagramDiscrete (amap1 hPnt ps)
--   DiagramChainTo e as      -> DiagramChainTo (hPnt e) (amap1 hArw as)
--   DiagramChainFrom s as    -> DiagramChainFrom  (hPnt s) (amap1 hArw as)
--   DiagramParallelLR l r as -> DiagramParallelLR (hPnt l) (hPnt r) (amap1 hArw as)
--   DiagramParallelRL l r as -> DiagramParallelRL (hPnt l) (hPnt r) (amap1 hArw as)
--   DiagramSink e as         -> DiagramSink (hPnt e) (amap1 hArw as)
--   DiagramSource s as       -> DiagramSource (hPnt s) (amap1 hArw as)
--   DiagramGeneral ps aijs   -> DiagramGeneral (amap1 hPnt ps) (amap1 (\(a,o) -> (hArw a,o)) aijs)
-- @
dgMap :: Hom Ort h => h a b -> Diagram t n m a -> Diagram t n m b
dgMap h d = case d of
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

instance HomOriented h => Applicative1 h (Diagram t n m) where amap1 = dgMap

instance FunctorialHomOriented h => Functorial1 h (Diagram t n m)

--------------------------------------------------------------------------------
-- coDiagram -

-- | mapping a diagram to its co-diagram according to the given structural duality on oriented
-- structures.
--
-- __Definition__ Let @q@ be in @__q__ __i__ __o__@, @s@ in @'Struct' __s__ __a__@ and
-- @d@ in @'Diagram' __t__ __n__ __m__ __a__@ with @'SDualityOriented' __q__ __s__ __i__ __o__@, then
-- we define @d' = 'coDiagram' q s d@ as follows: Let @coPnt = 'sdlToDualPnt' q s@ and
-- @coArw = 'sdlToDual' q s@ in
--
-- @
-- d' = case d of
--   DiagramEmpty             -> DiagramEmpty
--   DiagramDiscrete ps       -> DiagramDiscrete (amap1 coPnt ps)
--   DiagramChainTo p as      -> DiagramChainFrom (coPnt p) (amap1 coArw as)
--   DiagramChainFrom p as    -> DiagramChainTo (coPnt p) (amap1 coArw as)
--   DiagramParallelLR l r as -> DiagramParallelRL (coPnt l) (coPnt r) (amap1 coArw as)
--   DiagramParallelRL l r as -> DiagramParallelLR (coPnt l) (coPnt r) (amap1 coArw as)
--   DiagramSink p as         -> DiagramSource (coPnt p) (amap1 coArw as)
--   DiagramSource p as       -> DiagramSink (coPnt p) (amap1 coArw as)
--   DiagramGeneral ps aijs   -> DiagramGeneral (amap1 coPnt ps) (amap1 (\(a,o) -> (coArw a,opposite o)) aijs)
-- @
--
-- From the definition above, the definition for 'dgMap', the properties for 'SDuality' and
-- 'SDualityOriented' follows easily:
--
-- __Properties__ For all @q@ in @__q__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'SDualityOriented __q__ __s__ __i__ __o__@ holds:
--
-- (1) @'coDiagram' q s' '.' 'coDiagram' q s '.=.' 'dgMap' r@ where
-- @s' = 'sdlTau' q s@ and @'Inv2' r _ = 'sdlRefl' q s@.
--
-- (2) @'coDiagram' q s'' '.' 'dgMap' r '.=.' 'dgMap' r'' '.' 'coDiagram' q s@ where
-- @s' = 'sdlTau' q s@, @s'' = 'sdlTau' q s'@, @'Inv2' r _ = 'sdlRefl' q s@ and
-- @'Inv2' r'' _ = 'sdlRefl' q s'@.
coDiagram :: SDualityOriented d s i o
  => d i o -> Struct s a
  -> Diagram t n m a -> Dual1 (Diagram t n m) (o a)
coDiagram q s d = case d of
  DiagramEmpty             -> DiagramEmpty
  DiagramDiscrete ps       -> DiagramDiscrete (amap1 coPnt ps)
  DiagramChainTo e as      -> DiagramChainFrom (coPnt e) (amap1 coArw as)
  DiagramChainFrom s as    -> DiagramChainTo (coPnt s) (amap1 coArw as)
  DiagramParallelLR l r as -> DiagramParallelRL (coPnt l) (coPnt r) (amap1 coArw as)
  DiagramParallelRL l r as -> DiagramParallelLR (coPnt l) (coPnt r) (amap1 coArw as)
  DiagramSink e as         -> DiagramSource (coPnt e) (amap1 coArw as)
  DiagramSource s as       -> DiagramSink (coPnt s) (amap1 coArw as)
  DiagramGeneral ps aijs   -> DiagramGeneral
                                (amap1 coPnt ps)
                                (amap1 (\(a,o) -> (coArw a,opposite o)) aijs)

  where coPnt = sdlToDualPnt q s
        coArw = sdlToDual q s

--------------------------------------------------------------------------------
-- DiagramDuality -

-- | 'SDuality1' for 'Diagram's where 'sdlToDual1Fst' and 'sdlToDualSnd' are given by 'coDiagram'.
--
-- __Note__
--
-- (1) The definition of 'sdlToDualSnd' is also given by 'coDiagram' under the assumption of
-- @'Dual' ('Dual' __t__) ':~:' __t__@.
--
-- (2) From the properties of 'coDiagram' and the note 3 of 'SDuality1' follows, that all the
-- properties of 'SDuality1' for 'DiagramDuality' holds.
data DiagramDuality q s i o a b where
  DiagramDuality
    :: SDualityOriented q s i o
    => q i o
    -> Dual (Dual t) :~: t
    -> DiagramDuality q s i o (Diagram t n m) (Dual1 (Diagram t n m))

instance BiFunctorial1 i (DiagramDuality q s i o) where
  fnc1Fst (DiagramDuality _ _) = Functor1
  fnc1Snd (DiagramDuality _ _) = Functor1

instance SReflexive s i o => SDuality1 (DiagramDuality q s) s i o where
  sdlToDual1Fst (DiagramDuality q _)    = coDiagram q
  sdlToDual1Snd (DiagramDuality q Refl) = coDiagram q

--------------------------------------------------------------------------------
-- DiagramOpDuality -

-- | 'DiagramDuality' according to 'IsoOp'.
type DiagramOpDuality s = DiagramDuality OpDuality s (IsoOp s) Op
  
--------------------------------------------------------------------------------
-- dgOpDuality -

-- | 'Op'-duality for 'Diagram's.
dgOpDuality :: (TransformableTyp s, TransformableOp s, TransformableOrt s)
  => Dual (Dual t) :~: t
  -> DiagramOpDuality s (Diagram t n m) (Dual1 (Diagram t n m))
dgOpDuality = DiagramDuality OpDuality

--------------------------------------------------------------------------------
-- dgOpDualityOrt -

-- | 'Op'-duality for 'Diagram' on 'Ort'-structures.
dgOpDualityOrt :: Dual (Dual t) :~: t
  -> DiagramOpDuality Ort (Diagram t n m) (Dual1 (Diagram t n m))
dgOpDualityOrt = dgOpDuality

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

    _ -> valid $ sdlToDual1Fst dOp sOrt d

    where dOp  = dgOpDualityOrt (dgTypeRefl d)
          sOrt = Struct :: Oriented x => Struct Ort x
    
          prm :: N -> Message
          prm i = Params["i":=show i]
          lC = Label "chain"
          lE = Label "end"
          lO = Label "orientation"
          lB = Label "bound"
    
--------------------------------------------------------------------------------
-- Diagram - Entity -

instance (Oriented a, Typeable t, Typeable n, Typeable m) => Entity (Diagram t n m a)

--------------------------------------------------------------------------------
-- Diagram - Oriented -

instance (Oriented a, Typeable d, Typeable n, Typeable m)
  => Oriented (Diagram (Parallel d) n m a) where
  type Point (Diagram (Parallel d) n m a) = Point a
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
dgQuiver d = coQuiverInv $ dgQuiver $ sdlToDual1Fst dOp sOrt d where
  dOp  = dgOpDualityOrt (dgTypeRefl d)
  sOrt = Struct :: Oriented a => Struct Ort a

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
chnFromEnd d@(DiagramChainFrom _ _) = chnToStart $ sdlToDual1Fst dOp sOrt d where
  dOp  = dgOpDualityOrt (dgTypeRefl d)
  sOrt = Struct :: Oriented a => Struct Ort a


--------------------------------------------------------------------------------
-- Diagram (Chain t) - Oriented -

instance (Oriented a, Typeable t, Typeable n, Typeable m) => Oriented (Diagram (Chain t) n m a) where
  type Point (Diagram (Chain t) n m a) = Point a
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
xDiagram rt xd = case xd of
  XDiagramEmpty           -> return DiagramEmpty
  XDiagramDiscrete n xp   -> xDiscrete xd n xp
  XDiagramChainTo m xs    -> xChain m xs
  XDiagramParallelLR m xo -> xParallel m xo
  XDiagramSink m xe       -> xSink m xe
  _                       ->   amap1 (sdlFromDual1Fst dOp sOrt)
                             $ xDiagram (rt' rt) $ coXDiagram xd
  where dOp  = dgOpDualityOrt rt
        sOrt = Struct :: Oriented a => Struct Ort a

--------------------------------------------------------------------------------
-- X (Diagram t n m OS) - Standard -

instance (Oriented a, n ~ N0, m ~ N0) => XStandard (Diagram 'Empty n m a) where
  xStandard = xDiagram Refl XDiagramEmpty

instance (Oriented a, m ~ N0, XStandardPoint a, Attestable n)
  => XStandard (Diagram Discrete n m a) where
  xStandard = xDiagram Refl (XDiagramDiscrete n xStandard) where n = attest

instance (Oriented a, XStandardOrtSite To a, Attestable m)
  => XStandard (Diagram (Chain To) (S m) m a) where
  xStandard = xDiagram Refl (XDiagramChainTo m xStandardOrtSite) where m = attest

instance (Oriented a, XStandardOrtSite From a, Attestable m)
  => XStandard (Diagram (Chain From) (S m) m a) where
  xStandard = xDiagram Refl (XDiagramChainFrom m xStandardOrtSite) where m = attest

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

instance Oriented a => Entity (SomeDiagram a)

--------------------------------------------------------------------------------
-- sdgMap -

-- | mapping of some diagram via a homomorphism on 'Oriented' structures.
sdgMap :: Hom Ort h => h a b -> SomeDiagram a -> SomeDiagram b
sdgMap h (SomeDiagram a) = SomeDiagram (dgMap h a)

--------------------------------------------------------------------------------
-- SomeDiagram - Duality -

type instance Dual1 SomeDiagram    = SomeDiagram
type instance Dual (SomeDiagram a) = Dual1 SomeDiagram (Op a)

--------------------------------------------------------------------------------
-- coSomeDiagram -

-- | dual of 'SomeDiagram'.
coSomeDiagram :: SDualityOriented d s i o
  => d i o -> Struct s a
  -> SomeDiagram a -> Dual1 SomeDiagram (o a)
coSomeDiagram dlt sOrt (SomeDiagram d) = SomeDiagram (coDiagram dlt sOrt d)

--------------------------------------------------------------------------------
-- SomeDiagramDuality -

-- | 'SDuality1' for 'SomeDiagram's.
data SomeDiagramDuality d s i o a b where
  SomeDiagramDuality
    :: SDualityOriented d s i o
    => d i o
    -> SomeDiagramDuality d s i o SomeDiagram (Dual1 SomeDiagram)

instance HomOriented h => Applicative1 h SomeDiagram where
  amap1 = sdgMap
  
instance FunctorialHomOriented h => Functorial1 h SomeDiagram

instance FunctorialHomOriented i => BiFunctorial1 i (SomeDiagramDuality d s i o) where
  fnc1Fst (SomeDiagramDuality _) = Functor1
  fnc1Snd (SomeDiagramDuality _) = Functor1

instance (SReflexive s i o, FunctorialHomOriented i)
  => SDuality1 (SomeDiagramDuality d s) s i o where
  sdlToDual1Fst (SomeDiagramDuality dlt) = coSomeDiagram dlt
  sdlToDual1Snd (SomeDiagramDuality dlt) = coSomeDiagram dlt

--------------------------------------------------------------------------------
-- SomeDiagramOpDuality -

-- | 'SDuality1' for 'SomeDiagram' according to 'IsoOp'.
type SomeDiagramOpDuality s = SomeDiagramDuality OpDuality s (IsoOp s) Op

--------------------------------------------------------------------------------
-- sdgOpDuality -

-- | 'Op'-duality for 'SomeDiagram's.
sdgOpDuality :: (TransformableTyp s, TransformableOp s, TransformableOrt s)
  => SomeDiagramOpDuality s SomeDiagram (Dual1 SomeDiagram)
sdgOpDuality = SomeDiagramDuality OpDuality

--------------------------------------------------------------------------------
-- sdgOpDualityOrt -

-- | 'Op'-duality for 'SomeDiagram' on 'Ort'-structures.
sdgOpDualityOrt :: SomeDiagramOpDuality Ort SomeDiagram (Dual1 SomeDiagram)
sdgOpDualityOrt = sdgOpDuality

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
  xChainFrom n xFrom = amap1 (sdlFromDual1Fst d s) $ xChainTo n (coXOrtSite xFrom) where
    d = sdgOpDualityOrt
    s = Struct :: Oriented a => Struct Ort a
          
  xParallelLR :: Oriented a => Any n -> XOrtOrientation a -> X (SomeDiagram a)
  xParallelLR n xO = amap1 SomeDiagram $ xDiagram Refl (XDiagramParallelLR n xO)
   
  xParallelRL :: Oriented a => Any n -> XOrtOrientation a -> X (SomeDiagram a)
  xParallelRL n xO = amap1 (sdlFromDual1Fst d s) $ xParallelLR n (coXOrtOrientation xO) where
    d = sdgOpDualityOrt
    s = Struct :: Oriented a => Struct Ort a

  xSink :: Oriented a => Any n -> XOrtSite To a -> X (SomeDiagram a)
  xSink n xTo = amap1 SomeDiagram $ xDiagram Refl (XDiagramSink n xTo)

  xSource :: Oriented a => Any n -> XOrtSite From a -> X (SomeDiagram a)
  xSource n xFrom = amap1 (sdlFromDual1Fst d s) $ xSink n (coXOrtSite xFrom) where
    d = sdgOpDualityOrt
    s = Struct :: Oriented a => Struct Ort a

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

-}
