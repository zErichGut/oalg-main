
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE RankNTypes #-}


-- |
-- Module      : OAlg.Entity.Slice.Definition
-- Description : definition of slicing a multiplicative structure
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of slicing a 'Multiplicative' structures according a given indexed 'Point'.
module OAlg.Entity.Slice.Definition
  (
    -- * Slice
    Slice(..), slice, slSiteType

    -- ** Duality
  , coSlice, coSliceInv
  , slFromOpOp, slToOpOp

    -- * Factor
  , SliceFactor(..), slfFactor, slfIndex
  
    -- * Sliced
  , Sliced(..)

    -- * Hom
  , SliceFactorDrop(..)

    -- * Limes

  , DiagramSlicedCenter(..)
  , LimesSlicedTip(..), lstLimes

    -- ** Projective
  , slfTerminalPoint
  , slfPullback

    -- ** Injective
  , slfLimitsInjective

    -- * X
  , xSliceTo, xSliceFrom
  , xosXOrtSiteToSliceFactorTo
  , xosXOrtSiteFromSliceFactorFrom
  , xosAdjTerminal
  ) where

import Control.Monad

import Data.Typeable
import Data.List ((++))
import Data.Either

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative as M
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Operational
import OAlg.Structure.Vectorial

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone
import OAlg.Limes.Universal
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.TerminalAndInitialPoint
import OAlg.Limes.ProductsAndSums
import OAlg.Limes.PullbacksAndPushouts

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding ((++))
import OAlg.Entity.Diagram

import OAlg.Data.Symbol

--------------------------------------------------------------------------------
-- Sliced -

-- | Slicing a 'Multiplicative' structures at the 'Point' given by the type of the index
--  __@i@__. 
--
--  __Note__ The constraint @'Singleton1' __i__@ ensures that the distinguished point
--  depends only on the type __@i c@__.
class (Entity1 i, Singleton1 i) => Sliced i c where
  -- | the distingueished point of the given index type @__i__@.
  slicePoint :: i c -> Point c


instance Sliced i c => Sliced i (Op c) where
  slicePoint i = to i $ slicePoint $ fo i where
    
    fo :: Singleton1 i => i (Op c) -> i c
    fo _ = unit1

    to :: p (Op c) -> Point c -> Point (Op c)
    to _ = id

--------------------------------------------------------------------------------
-- Slice -

-- | slice over __@c@__ by a given 'Site' and indexed by @__i__@.
data Slice s i c where
  SliceFrom :: i c -> c -> Slice From i c
  SliceTo :: i c -> c -> Slice To i c

instance (Show1 i, Show c) => Show (Slice s i c) where
  show (SliceFrom i c) = "SliceFrom[" ++ show1 i ++ "] (" ++ show c ++ ")"
  show (SliceTo i c)   = "SliceTo[" ++ show1 i ++ "] (" ++ show c ++ ")"
  
instance (Eq1 i, Eq c) => Eq (Slice s i c) where
  SliceFrom i f == SliceFrom j g = eq1 i j && f == g
  SliceTo i f == SliceTo j g     = eq1 i j && f == g

--------------------------------------------------------------------------------
-- slice -

-- | the underlying slice.
slice :: Slice s i c -> c
slice (SliceFrom _ p) = p
slice (SliceTo _ p)   = p

--------------------------------------------------------------------------------
-- slSiteType -

-- | the 'Site' type of a slice.
slSiteType :: Slice s i c -> Either (s :~: From) (s :~: To)
slSiteType (SliceFrom _ _ ) = Left Refl
slSiteType (SliceTo _ _)    = Right Refl

--------------------------------------------------------------------------------
-- Slice - Dual -

type instance Dual (Slice s i c) = Slice (Dual s) i (Op c)

-- | to the dual 'Slice'.
coSlice :: Singleton1 i => Slice s i c -> Dual (Slice s i c)
coSlice (SliceFrom _ f) = SliceTo unit1 (Op f)
coSlice (SliceTo _ f)   = SliceFrom unit1 (Op f)

slFromOpOp :: Singleton1 i => Slice s i (Op (Op c)) -> Slice s i c
slFromOpOp (SliceFrom _ (Op (Op f))) = SliceFrom unit1 f
slFromOpOp (SliceTo _ (Op (Op t))) = SliceTo unit1 t

slToOpOp :: Singleton1 i => Slice s i c -> Slice s i (Op (Op c))
slToOpOp (SliceFrom _ f) = SliceFrom unit1 (Op (Op f))
slToOpOp (SliceTo _ t)   = SliceTo unit1 (Op (Op t))

slSiteBidual :: Slice s i c -> Dual (Dual s) :~: s
slSiteBidual (SliceFrom _ _) = Refl
slSiteBidual (SliceTo _ _) = Refl

coSliceInv :: Singleton1 i => Dual (Dual s) :~: s -> Dual (Slice s i c) -> Slice s i c
coSliceInv Refl = slFromOpOp . coSlice

--------------------------------------------------------------------------------
-- Slice - Validable -

-- | validity of a 'Slice'.
relValidSlice :: (Oriented c, Sliced i c)
  => Slice s i c -> Statement
relValidSlice s@(SliceFrom i f)
  = And [ valid1 i
        , valid f
        , let p = slicePoint i in
            (start f == p):?>Params ["s":=show s]
        ]
relValidSlice s                 = relValidSlice (coSlice s)


instance (Oriented c, Sliced i c) => Validable (Slice s i c) where
  valid s = Label "Slice" :<=>: relValidSlice s


instance (Oriented c, Sliced i c, Typeable s) => Entity (Slice s i c)

--------------------------------------------------------------------------------
-- SliceFactor -

-- | factor between two slices.
--
--  __Property__ Let @SliceFactor a b f@ be in
-- @'SliceFactor' __s__ __i__ __c__@ for a 'Multiplicative' structure __@c@__
-- constrained by @'Sliced' __i__ __c__@ then holds:
--
-- (1) If @a@ matches @'SliceFrom' _ a'@ then holds: Let @'SliceFrom' _ b' = b@ in
--
--     (1) @'orientation' f '==' 'end' a' ':>' 'end' b'@.
--
--     (2) @b' '==' f 'M.*' a'@.
--
-- (2) If @a@ matches @'SliceTo' _ a'@ then holds: Let @'SliceTo' _ b' = b@ in
--
--     (1) @'orientation' f '==' 'start' a' ':>' 'start' b'@.
--
--     (2) @a' '==' b' 'M.*' f@ .
data SliceFactor s i c = SliceFactor (Slice s i c) (Slice s i c) c
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- slfFactor -

-- | the underlying factor.
slfFactor :: SliceFactor s i c -> c       
slfFactor (SliceFactor _ _ f) = f

--------------------------------------------------------------------------------
-- slfIndex -

-- | the associated index.
slfIndex :: Sliced i c => f (SliceFactor To i c) -> i c
slfIndex _ = unit1

--------------------------------------------------------------------------------
-- SliceFactor - Dual -

type instance Dual (SliceFactor s i c) = SliceFactor (Dual s) i (Op c)

-- | to the dual 'SliceFactor'.
coSliceFactor :: Singleton1 i
  => SliceFactor s i c -> Dual (SliceFactor s i c)
coSliceFactor (SliceFactor a b t)
  = SliceFactor (coSlice b) (coSlice a) (Op t)

--------------------------------------------------------------------------------
-- SliceTransformatin - Entity -

-- | validity of a 'SliceFactor'.
relValidSliceFactor :: (Multiplicative c, Sliced i c) => SliceFactor s i c -> Statement
relValidSliceFactor (SliceFactor a@(SliceFrom _ a') b@(SliceFrom _ b') t)
  = And [ valid a
        , valid b
        , valid t
        , Label "1.1" :<=>: (orientation t == end a' :> end b')
            :?> prm
        , Label "1.2" :<=>: (b' == t*a') :?> prm
        ] where prm = Params ["(a,b,t)":=show (a,b,t)]
relValidSliceFactor t = relValidSliceFactor (coSliceFactor t)

instance (Multiplicative c, Sliced i c) => Validable (SliceFactor s i c) where
  valid t = Label "SliceFactor"
    :<=>: relValidSliceFactor t

instance (Multiplicative c, Sliced i c, Typeable s) => Entity (SliceFactor s i c)

--------------------------------------------------------------------------------
-- SliceFactor - Multiplicative -

instance (Multiplicative c, Sliced i c, Typeable s) => Oriented (SliceFactor s i c) where
  type Point (SliceFactor s i c) = Slice s i c
  orientation (SliceFactor a b _) = a :> b


instance (Multiplicative c, Sliced i c, Typeable s)
  => Multiplicative (SliceFactor s i c) where
  one s = SliceFactor s s o where
    o = case s of
      SliceFrom _ f -> one (end f)
      SliceTo _ f   -> one (start f)

  SliceFactor c d f * SliceFactor a b g
    | c == b    = SliceFactor a d (f*g)
    | otherwise = throw NotMultiplicable

  npower (SliceFactor a b t) n = SliceFactor a b (npower t n)

--------------------------------------------------------------------------------
-- SliceFactor - TerminalPoint -

-- | terminal point for factors sliced to a 'Point'.
slfTerminalPoint :: (Multiplicative c, Sliced i c) => TerminalPoint (SliceFactor To i c)
slfTerminalPoint = LimesProjective l u where
  o  :: (Multiplicative c, Sliced i c) => i c -> Slice To i c
  o i = SliceTo i (one (slicePoint i))

  l = ConeProjective DiagramEmpty (o unit1) Nil
  u (ConeProjective _ s@(SliceTo _ f) Nil) = SliceFactor s (tip l) f

--------------------------------------------------------------------------------
-- DiagramSlicedCenter -

-- | predicate for a @'Star' __t__@ diagram with center 'Point' given by the index type
-- @__i__ __c__@.
--
-- __Property__ Let @'DiagramSlicedCenter' i d@ be in
-- @'DiagramSlicedCenter' __i__ __t__ __n__ __m__ __c__@ then holds:
-- @'slicePoint' i '==' 'dgCenter' d@.
data DiagramSlicedCenter i t n m c where
  DiagramSlicedCenter :: Sliced i c
    => i c
    -> Diagram (Star t) n m c
    -> DiagramSlicedCenter i t n m c

instance Oriented c => Show (DiagramSlicedCenter i t n m c) where
  show (DiagramSlicedCenter i d)
    = "DiagramSlicedCenter[" ++ show1 i ++ "] (" ++ show d ++ ")"

instance Oriented c => Validable (DiagramSlicedCenter i t n m c) where
  valid (DiagramSlicedCenter i d)
    = And [ valid1 i
          , valid d
          , (slicePoint i == dgCenter d)
              :?> Params["i":=show1 i,"d":=show d] 
          ]

--------------------------------------------------------------------------------
-- slfPullback -

-- | the induced pullback.
slfPullback :: Multiplicative c
  => Products n (SliceFactor To i c)
  -> DiagramSlicedCenter i To (n+1) n c -> Pullback n c
slfPullback prds (DiagramSlicedCenter kc d@(DiagramSink _ as))
  = LimesProjective lim univ where
    pPrd = amap1 (SliceTo kc) as
    dPrd = DiagramDiscrete pPrd
    LimesProjective lPrd uPrd = limes prds dPrd
    
    lim = ConeProjective d (end t) (t:|cs) where
      SliceTo _ t = tip lPrd
      cs = amap1 (\(SliceFactor _ _ f) -> f) $ shell lPrd 
      
    univ (ConeProjective _ _ (t:|cs)) = u where
      SliceFactor _ _ u = uPrd cnPrd
      t' = SliceTo kc t
      cnPrd = ConeProjective dPrd t' csPrd
      csPrd = amap1 (uncurry (SliceFactor t')) (pPrd `zip` cs)

--------------------------------------------------------------------------------
-- LimesSlicedTip -

-- | predicate for a limes with a sliced tip of the universal cone.
--
--  __Property__ Let @'LimesSlicedTip' i l@ be in
-- @'LimesSlicedTip' __i__ __s__ __p__ __t__ __n__ __m__ __c__@ then holds:
-- @'tip' ('universalCone' l) '==' 'slicePoint' i@.
data LimesSlicedTip i s p t n m c where
  LimesSlicedTip :: Sliced i c => i c -> Limes s p t n m c -> LimesSlicedTip i s p t n m c

instance Oriented c => Show (LimesSlicedTip i s p t n m c) where
  show (LimesSlicedTip i l) = "LimesSlicedTip[" ++ show1 i ++ "] (" ++ show l ++ ")"

instance (Oriented c, Validable (Limes s p t n m c))
  => Validable (LimesSlicedTip i s p t n m c) where
  valid (LimesSlicedTip i l) = Label "LimesSlicedTip" :<=>:
    And [ valid1 i
        , valid l
        , (tip (universalCone l) == slicePoint i)
            :?>Params ["i":=show1 i, "l":= show l]
        ]

--------------------------------------------------------------------------------
-- lstLimes -

-- | the underlying limes.
lstLimes :: LimesSlicedTip i s p t n m c -> Limes s p t n m c
lstLimes (LimesSlicedTip _ lim) = lim

--------------------------------------------------------------------------------
-- SliceFactorProjection -

-- | dropping a slice factor.
data SliceFactorDrop s x y where
  SliceFactorFromDrop
    :: (Multiplicative c, Sliced i c)
    => SliceFactorDrop From (SliceFactor From i c) c 
  SliceFactorToDrop
    :: (Multiplicative c, Sliced i c)
    => SliceFactorDrop To (SliceFactor To i c) c

--------------------------------------------------------------------------------
-- SliceFactorDrop - Entity -

deriving instance Show (SliceFactorDrop s x y)
instance Show2 (SliceFactorDrop s)

deriving instance Eq (SliceFactorDrop s x y)
instance Eq2 (SliceFactorDrop s)

instance Validable (SliceFactorDrop s x y) where
  valid SliceFactorFromDrop = SValid
  valid _                   = SValid
instance Validable2 (SliceFactorDrop s)

instance (Typeable s, Typeable x, Typeable y) => Entity (SliceFactorDrop s x y)
instance Typeable s => Entity2 (SliceFactorDrop s)

--------------------------------------------------------------------------------
-- SliceFactorDrop - Morphism -

instance Morphism (SliceFactorDrop s) where
  type ObjectClass (SliceFactorDrop s) = Mlt
  homomorphous SliceFactorFromDrop = Struct :>: Struct
  homomorphous SliceFactorToDrop   = Struct :>: Struct

--------------------------------------------------------------------------------
-- SliceFactorDrop - Hom Mlt -

instance Applicative (SliceFactorDrop s) where
  amap SliceFactorFromDrop = slfFactor
  amap SliceFactorToDrop   = slfFactor

instance HomOriented (SliceFactorDrop s) where
  pmap SliceFactorFromDrop (SliceFrom _ a) = end a
  pmap SliceFactorToDrop (SliceTo _ a)     = start a

instance HomMultiplicative (SliceFactorDrop s) where
  
--------------------------------------------------------------------------------
-- slfSliceIndex -

-- | the given attest for the slice index @__i__ __c__@ given by the diagram proxy.
slfSliceIndex :: Sliced i c => Diagram t n m (SliceFactor To i c) -> i c
slfSliceIndex _ = unit1

--------------------------------------------------------------------------------
-- dgSlfToSlicePoint -

-- | the diagram as a cone with its tip given by the 'slicePoint'.
dgSlfToSlicePoint :: (Multiplicative c, Sliced i c)
  => Diagram t n m (SliceFactor To i c) -> Cone Mlt Injective t n m c
dgSlfToSlicePoint d = ConeInjective d' t cs where
  d' = dgMap SliceFactorToDrop d
  t  = slicePoint $ slfSliceIndex d
  cs = amap1 slice $ dgPoints d

--------------------------------------------------------------------------------
-- slfLimesInjective -

-- | the induced 'Injective' limes for 'SliceFactor'. 
slfLimesInjective :: (Multiplicative c, Sliced i c)
  => Limits Limes Mlt Injective t n m c
  -> Diagram t n m (SliceFactor To i c)
  -> Limes Mlt Injective t n m (SliceFactor To i c)
slfLimesInjective l dgSlf = LimesInjective slfLim slfUniv where
  LimesInjective lLim lUniv = limes l (dgMap SliceFactorToDrop dgSlf)
  
  slfLim = ConeInjective dgSlf tSlf csSlf where
    tSlf = SliceTo (slfSliceIndex dgSlf) (lUniv (dgSlfToSlicePoint dgSlf))
    csSlf = amap1 (\(s,f) -> SliceFactor s tSlf f) (dgPoints dgSlf `zip` shell lLim)
    
  slfUniv slfCn = SliceFactor (tip slfLim) (tip slfCn) u where
    u = lUniv $ cnMap SliceFactorToDrop slfCn

--------------------------------------------------------------------------------
-- slfLimitsInjective -

-- | the induced 'Injective' 'Limits'.
slfLimitsInjective :: (Multiplicative c, Sliced i c)
  => Limits Limes Mlt Injective t n m c -> Limits Limes Mlt Injective t n m (SliceFactor To i c)
slfLimitsInjective lms = Limits $ slfLimesInjective lms

--------------------------------------------------------------------------------
-- xSliceTo -

-- | the induced random variable.
xSliceTo :: Sliced i c
  => XOrtSite To c -> i c -> X (Slice To i c)
xSliceTo (XEnd _ xTo) i = xTo (slicePoint i) >>= return . SliceTo i

--------------------------------------------------------------------------------
-- xSlicFrom -

-- | the induced random variable.
xSliceFrom :: Sliced i c
  => XOrtSite From c -> i c -> X (Slice From i c)
xSliceFrom (XStart _ xFrom) i = xFrom (slicePoint i) >>= return . SliceFrom i

--------------------------------------------------------------------------------
-- xosXOrtSiteToSliceFactorTo -

-- | the induced random variable.
xosXOrtSiteToSliceFactorTo :: (Multiplicative c, Sliced i c)
  => XOrtSite To c -> i c -> XOrtSite To (SliceFactor To i c)
xosXOrtSiteToSliceFactorTo xTo@(XEnd _ xTo') i = XEnd xp xsfTo where
  xp = xSliceTo xTo i
  xsfTo e@(SliceTo i a) = do
    f <- xTo' (start a)
    return (SliceFactor (SliceTo i (a*f)) e f)

--------------------------------------------------------------------------------
-- xosXOrtSiteFromSliceFactorFrom -

-- | the induced random variable.
xosXOrtSiteFromSliceFactorFrom :: (Multiplicative c, Sliced i c)
  => XOrtSite From c -> i c -> XOrtSite From (SliceFactor From i c)
xosXOrtSiteFromSliceFactorFrom xFrom@(XStart _ xFrom') i = XStart xp xsfFrom where
  xp = xSliceFrom xFrom i
  xsfFrom s@(SliceFrom i a) = do
    f <- xFrom' (end a)
    return (SliceFactor s (SliceFrom i (f*a)) f)

--------------------------------------------------------------------------------
-- SliceFactor - XStandardOrtStite From -

instance (Multiplicative c, Sliced i c, XStandardOrtSite From c)
  => XStandardOrtSite From (SliceFactor From i c) where
  xStandardOrtSite = xosXOrtSiteFromSliceFactorFrom xStandardOrtSite unit1

instance (Multiplicative c, Sliced i c, XStandardOrtSite From c)
  => XStandardOrtSiteFrom (SliceFactor From i c)

instance (Multiplicative c, Sliced i c, XStandardOrtSite From c)
  => XStandard (SliceFactor From i c) where
  xStandard = xosOrt ( xStandardOrtSite
                       :: (Multiplicative c, Sliced i c, XStandardOrtSite From c)
                       => XOrtSite From (SliceFactor From i c)
                     )

instance (Multiplicative c, Sliced i c, XStandardOrtSite From c)
  => XStandard (Slice From i c) where
  xStandard = xosPoint ( xStandardOrtSite
                         :: (Multiplicative c, Sliced i c, XStandardOrtSite From c)
                         => XOrtSite From (SliceFactor From i c)
                       )
instance (Multiplicative c, Sliced i c, XStandardOrtSite From c)
  => XStandardPoint (SliceFactor From i c)

--------------------------------------------------------------------------------
-- SliceFactor - XStandardOrtStite To -

instance (Multiplicative c, Sliced i c, XStandardOrtSite To c)
  => XStandardOrtSite To (SliceFactor To i c) where
  xStandardOrtSite = xosXOrtSiteToSliceFactorTo xStandardOrtSite unit1

instance (Multiplicative c, Sliced i c, XStandardOrtSite To c)
  => XStandardOrtSiteTo (SliceFactor To i c)

instance (Multiplicative c, Sliced i c, XStandardOrtSite To c)
  => XStandard (SliceFactor To i c) where
  xStandard = xosOrt ( xStandardOrtSite
                       :: (Multiplicative c, Sliced i c, XStandardOrtSite To c)
                       => XOrtSite To (SliceFactor To i c)
                     )

instance (Multiplicative c, Sliced i c, XStandardOrtSite To c)
  => XStandard (Slice To i c) where
  xStandard = xosPoint ( xStandardOrtSite
                         :: (Multiplicative c, Sliced i c, XStandardOrtSite To c)
                         => XOrtSite To (SliceFactor To i c)
                       )
instance (Multiplicative c, Sliced i c, XStandardOrtSite To c)
  => XStandardPoint (SliceFactor To i c)

--------------------------------------------------------------------------------

instance Sliced Proxy OS where
  slicePoint _ = P

instance XStandardOrtSite From (SliceFactor To Proxy OS) where
  xStandardOrtSite = XStart xp xFrom where
    xp = xStandard
    xFrom :: Slice To Proxy OS -> X (SliceFactor To Proxy OS)
    xFrom s@(SliceTo i (a:>p)) = do
      b <- xStandard
      return (SliceFactor s (SliceTo i (b:>p)) (a:>b))

instance XStandardOrtSiteFrom (SliceFactor To Proxy OS)

--------------------------------------------------------------------------------
-- xosAdjTerminal -

-- | adjoins a terminal point with the given probability to the random variable of the points of
-- the given @'XOrtSite' 'To'@ of the @'SliceFactor' 'To' __i__ __c__@. Such a terminal point is given
-- by @'one' s@ where @s@ is the slice point. 
xosAdjTerminal :: (Multiplicative c, Sliced i c)
  => Q -> XOrtSite To (SliceFactor To i c) -> XOrtSite To (SliceFactor To i c)
xosAdjTerminal w xos@(XEnd xp xf) = XEnd xp' xf where
  xp' = xOneOfXW [(w0,xp),(w,return s)]
  w0  = 1 - w
  i   = slfIndex xos
  s   = SliceTo i (one $ slicePoint i)


--------------------------------------------------------------------------------
-- Slice - Structure -

instance (Oriented c, Sliced i c, Typeable s) => Oriented (Slice s i c) where
  type Point (Slice s i c) = Point c
  orientation s = orientation $ slice s

instance (Sliced i c, Ord c) => Ord (Slice s i c) where
  compare (SliceFrom _ a ) (SliceFrom _ b) = compare a b
  compare (SliceTo _ a) (SliceTo _ b)      = compare a b
  
--------------------------------------------------------------------------------
-- Slice From - OrientedOpl -

instance Multiplicative c => Opl c (Slice From i c) where
  f *> (SliceFrom i c) = SliceFrom i (f*c)

instance (Multiplicative c, Sliced i c) => OrientedOpl c (Slice From i c)

instance (Distributive d, Sliced i d, Typeable s) => Fibred (Slice s i d) where
 type Root (Slice s i d) = Point d
 root (SliceFrom _ s) = end s
 root (SliceTo _ s)   = start s

instance (Distributive d, Sliced i d) => Additive (Slice From i d) where
  zero e = SliceFrom i (zero (slicePoint i :> e))
    where i = i' e
          i' :: Sliced i d => Point d -> i d
          i' _ = unit1


  SliceFrom i a + SliceFrom _ b = SliceFrom i (a+b)

  ntimes n (SliceFrom i a) = SliceFrom i (ntimes n a)
  
instance (Distributive d, Abelian d, Sliced i d) => Abelian (Slice From i d) where
  negate (SliceFrom i a) = SliceFrom i (negate a)

  SliceFrom i a - SliceFrom _ b = SliceFrom i (a-b)
  
  ztimes z (SliceFrom i a) = SliceFrom i (ztimes z a)

instance (Distributive d, Vectorial d, Sliced i d) => Vectorial (Slice From i d) where
  type Scalar (Slice From i d) = Scalar d
  x ! SliceFrom i a = SliceFrom i (x!a)

