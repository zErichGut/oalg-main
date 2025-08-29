
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

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
  , slMap, slMapCov, slMapCnt

    -- * Factor
  , SliceFactor(..), slfFactor, slfIndex
  , slfMap, slfMapCov, slfMapCnt
  
    -- * Duality
  , toDualOpOrtSld, toDualOpOrtSld'
  , toDualOpMltSld, toDualOpMltSld'
  
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

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Singleton
import OAlg.Data.Either

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
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.TerminalAndInitialPoint
import OAlg.Limes.ProductsAndSums
import OAlg.Limes.PullbacksAndPushouts

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding ((++))
import OAlg.Entity.Diagram
import OAlg.Entity.Slice.Sliced

--------------------------------------------------------------------------------
-- Slice -

-- | slice over __@x@__ by a given 'Site' and indexed by @__i__@.
data Slice s i x where
  SliceFrom :: i x -> x -> Slice From i x
  SliceTo :: i x -> x -> Slice To i x

instance (Show1 i, Show x) => Show (Slice s i x) where
  show (SliceFrom i x) = "SliceFrom[" ++ show1 i ++ "] (" ++ show x ++ ")"
  show (SliceTo i x)   = "SliceTo[" ++ show1 i ++ "] (" ++ show x ++ ")"
  
instance (Eq1 i, Eq x) => Eq (Slice s i x) where
  SliceFrom i f == SliceFrom j g = eq1 i j && f == g
  SliceTo i f == SliceTo j g     = eq1 i j && f == g

--------------------------------------------------------------------------------
-- slice -

-- | the underlying slice.
slice :: Slice s i x -> x
slice (SliceFrom _ p) = p
slice (SliceTo _ p)   = p

--------------------------------------------------------------------------------
-- slIndex -

-- | the underlying index.
slIndex :: Slice s i x -> i x
slIndex (SliceFrom i _) = i
slIndex (SliceTo i _)   = i

--------------------------------------------------------------------------------
-- slSiteType -

-- | the 'Site' type of a slice.
slSiteType :: Slice s i x -> Either (s :~: From) (s :~: To)
slSiteType (SliceFrom _ _ ) = Left Refl
slSiteType (SliceTo _ _)    = Right Refl

--------------------------------------------------------------------------------
-- slTypeRefl -

slTypeRefl :: Slice s i x -> s :~: Dual (Dual s)
slTypeRefl (SliceFrom _ _) = Refl
slTypeRefl (SliceTo _ _)   = Refl

--------------------------------------------------------------------------------
-- slMapCov -

-- | mapping of slices under a covariant homomorphism.
--
-- __Note__ As 'IsoOp' is generated only by 'isoToOpOpOrt' ans 'isoFromOpOpOrt' the 'slicePoint' is
-- invariant under these mappings and as such 'slMapCov' maps 'valid' slices to 'valid' slices.
slMapCov :: HomSlicedOriented i h
  => Variant2 Covariant h x y -> Slice s i x -> Slice s i y
slMapCov (Covariant2 h) s = case s of
  SliceFrom i x          -> SliceFrom (sliceIndexRange $ sldHom (q i) h) (amap h x)
  SliceTo i x            -> SliceTo (sliceIndexRange $ sldHom (q i) h) (amap h x)
  where q :: i x -> Proxy i
        q _ = Proxy

--------------------------------------------------------------------------------
-- slMapCnt -

-- | mapping of slices under a contravariant homomorphism.
slMapCnt :: HomSlicedOriented i h
  => Variant2 Contravariant h x y -> Slice s i x -> Slice (Dual s) i y
slMapCnt (Contravariant2 h) s = case s of
  SliceFrom i x              -> SliceTo (sliceIndexRange $ sldHom (q i) h) (amap h x)
  SliceTo i x                -> SliceFrom (sliceIndexRange $ sldHom (q i) h) (amap h x)
  where q :: i x -> Proxy i
        q _ = Proxy

--------------------------------------------------------------------------------
-- slMap -

-- | mapping of slices.
slMap :: (HomSlicedOriented i h, s ~ Dual (Dual s))
  => h x y -> SDualBi (Slice s i) x -> SDualBi (Slice s i) y
slMap = vmapBi slMapCov slMapCov slMapCnt slMapCnt

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (Slice s i) = Slice (Dual s) i

instance
  ( HomSlicedOriented i h
  , s ~ Dual (Dual s)
  )
  => ApplicativeG (SDualBi (Slice s i)) h (->) where
  amapG = slMap

instance
  ( HomSlicedOriented i h
  , FunctorialOriented h
  , s ~ Dual (Dual s)
  )
  => FunctorialG (SDualBi (Slice s i)) h (->)

--------------------------------------------------------------------------------
-- Slice - Validable -

-- | validity of a 'Slice'.
relValidSlice :: Sliced i x => Slice s i x -> Statement
relValidSlice s@(SliceFrom i f)
  = And [ valid1 i
        , valid f
        , let p = slicePoint i in
            (start f == p) :?> Params ["s":=show s]
        ]
    
relValidSlice s = case slTypeRefl s of
  Refl -> relValidSlice s' where
            Contravariant2 i = toDualOpOrtSld' (q s)
            SDualBi (Left1 s') = amapF i (SDualBi (Right1 s))
  where q :: Slice s i x -> Proxy i
        q _ = Proxy

instance Sliced i x => Validable (Slice s i x) where
  valid s = Label "Slice" :<=>: relValidSlice s

--------------------------------------------------------------------------------
-- SliceFactor -

-- | factor between two slices.
--
--  __Property__ Let @SliceFactor a b f@ be in
-- @'SliceFactor' __s i x__@ for a 'Multiplicative' structure __@x@__
-- constrained by @'Sliced' __i x__@ then holds:
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
data SliceFactor s i x = SliceFactor (Slice s i x) (Slice s i x) x
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- slfFactor -

-- | the underlying factor.
slfFactor :: SliceFactor s i x -> x       
slfFactor (SliceFactor _ _ f) = f

--------------------------------------------------------------------------------
-- slfIndex -

-- | the associated index.
slfIndex :: Sliced i x => f (SliceFactor To i x) -> i x
slfIndex _ = unit1

--------------------------------------------------------------------------------
-- slfTypeRefl -

-- | proof of being reflexive.
slfTypeRefl :: SliceFactor s i x -> s :~: Dual (Dual s)
slfTypeRefl (SliceFactor a _ _) = slTypeRefl a

--------------------------------------------------------------------------------
-- slfMapCov -

-- | mapping of slices factor under a covariant homomorphism.
slfMapCov :: HomSlicedMultiplicative i h
  => Variant2 Covariant h x y -> SliceFactor s i x -> SliceFactor s i y
slfMapCov h (SliceFactor a b f) = SliceFactor a' b' (amap h f) where
  a' = slMapCov h a
  b' = slMapCov h b
  
--------------------------------------------------------------------------------
-- slfMapCnt -

-- | mapping of slices factor under a contravariant homomorphism.
slfMapCnt :: HomSlicedMultiplicative i h
  => Variant2 Contravariant h x y -> SliceFactor s i x -> SliceFactor (Dual s) i y
slfMapCnt h@(Contravariant2 h') (SliceFactor a b f) = SliceFactor b' a' (amap h' f) where
  a' = slMapCnt h a
  b' = slMapCnt h b

--------------------------------------------------------------------------------
-- slfMap -

-- | mapping of slices factor.
slfMap :: (HomSlicedMultiplicative i h, s ~ Dual (Dual s))
  => h x y -> SDualBi (SliceFactor s i) x -> SDualBi (SliceFactor s i) y
slfMap = vmapBi slfMapCov slfMapCov slfMapCnt slfMapCnt

--------------------------------------------------------------------------------
-- SliceFactor - Duality -

type instance Dual1 (SliceFactor s i) = SliceFactor (Dual s) i

instance (HomSlicedMultiplicative i h, s ~ Dual (Dual s))
  => ApplicativeG (SDualBi (SliceFactor s i)) h (->) where
  amapG = slfMap

instance (HomSlicedMultiplicative i h, FunctorialOriented h, s ~ Dual (Dual s))
  => FunctorialG (SDualBi (SliceFactor s i)) h (->)

--------------------------------------------------------------------------------
-- SliceTransformatin - Entity -

-- | validity of a 'SliceFactor'.
relValidSliceFactor :: (Multiplicative x, Sliced i x) => SliceFactor s i x -> Statement
relValidSliceFactor (SliceFactor a@(SliceFrom _ a') b@(SliceFrom _ b') t)
  = And [ valid a
        , valid b
        , valid t
        , Label "1.1" :<=>: (orientation t == end a' :> end b')
            :?> prm
        , Label "1.2" :<=>: (b' == t*a') :?> prm
        ] where prm = Params ["(a,b,t)":=show (a,b,t)]
relValidSliceFactor t = case slfTypeRefl t of
  Refl -> relValidSliceFactor t' where
            Contravariant2 i = toDualOpMltSld' (q t)
            SDualBi (Left1 t') = amapF i (SDualBi (Right1 t))
  where
    q :: SliceFactor s i x -> Proxy i
    q _ = Proxy


instance (Multiplicative x, Sliced i x) => Validable (SliceFactor s i x) where
  valid t = Label "SliceFactor"
    :<=>: relValidSliceFactor t


--------------------------------------------------------------------------------
-- SliceFactor - Multiplicative -

type instance Point (SliceFactor s i x) = Slice s i x
instance (Show1 i, Show x) => ShowPoint (SliceFactor s i x)
instance (Eq1 i, Eq x) => EqPoint (SliceFactor s i x)
instance Sliced i x => ValidablePoint (SliceFactor s i x)
instance (Typeable i, Typeable x, Typeable s) => TypeablePoint (SliceFactor s i x)

instance (Multiplicative x, Sliced i x, Typeable s) => Oriented (SliceFactor s i x) where  
  orientation (SliceFactor a b _) = a :> b

instance (Multiplicative x, Sliced i x, Typeable s)
  => Multiplicative (SliceFactor s i x) where
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
slfTerminalPoint :: (Multiplicative x, Sliced i x) => TerminalPoint (SliceFactor To i x)
slfTerminalPoint = LimesProjective l u where
  o  :: (Multiplicative x, Sliced i x) => i x -> Slice To i x
  o i = SliceTo i (one (slicePoint i))

  l = ConeProjective DiagramEmpty (o unit1) Nil
  u (ConeProjective _ s@(SliceTo _ f) Nil) = SliceFactor s (tip l) f

--------------------------------------------------------------------------------
-- DiagramSlicedCenter -

-- | predicate for a @'Star' __t__@ diagram with center 'Point' given by the index type
-- @__i x__@.
--
-- __Property__ Let @'DiagramSlicedCenter' i d@ be in
-- @'DiagramSlicedCenter' __i t n m x__@ then holds:
-- @'slicePoint' i '==' 'dgCenter' d@.
data DiagramSlicedCenter i t n m x where
  DiagramSlicedCenter :: Sliced i x
    => i x
    -> Diagram (Star t) n m x
    -> DiagramSlicedCenter i t n m x

instance Oriented x => Show (DiagramSlicedCenter i t n m x) where
  show (DiagramSlicedCenter i d)
    = "DiagramSlicedCenter[" ++ show1 i ++ "] (" ++ show d ++ ")"

instance Oriented x => Validable (DiagramSlicedCenter i t n m x) where
  valid (DiagramSlicedCenter i d)
    = And [ valid1 i
          , valid d
          , (slicePoint i == dgCenter d)
              :?> Params["i":=show1 i,"d":=show d] 
          ]

--------------------------------------------------------------------------------
-- slfPullback -

-- | the induced pullback.
slfPullback :: Multiplicative x
  => Products n (SliceFactor To i x)
  -> DiagramSlicedCenter i To (n+1) n x -> Pullback n x
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
-- @'LimesSlicedTip' __i s p t n m x__@ then holds:
-- @'tip' ('universalCone' l) '==' 'slicePoint' i@.
data LimesSlicedTip i s p t n m x where
  LimesSlicedTip :: Sliced i x => i x -> Limes s p t n m x -> LimesSlicedTip i s p t n m x


instance Oriented x => Show (LimesSlicedTip i s p t n m x) where
  show (LimesSlicedTip i l) = "LimesSlicedTip[" ++ show1 i ++ "] (" ++ show l ++ ")"

instance
  ( Oriented x
  , XStandardEligibleCone s p t n m x
  , XStandardEligibleConeFactor s p t n m x
  , Typeable s, Typeable p, Typeable t, Typeable n, Typeable m
  )
  => Validable (LimesSlicedTip i s p t n m x) where
  valid (LimesSlicedTip i l) = Label "LimesSlicedTip" :<=>:
    And [ valid1 i
        , valid l
        , (tip (universalCone l) == slicePoint i)
            :?>Params ["i":=show1 i, "l":= show l]
        ]

--------------------------------------------------------------------------------
-- lstLimes -

-- | the underlying limes.
lstLimes :: LimesSlicedTip i s p t n m x -> Limes s p t n m x
lstLimes (LimesSlicedTip _ lim) = lim

--------------------------------------------------------------------------------
-- SliceFactorProjection -

-- | dropping a slice factor.
data SliceFactorDrop s x y where
  SliceFactorFromDrop
    :: (Multiplicative x, Sliced i x)
    => SliceFactorDrop From (SliceFactor From i x) x 
  SliceFactorToDrop
    :: (Multiplicative x, Sliced i x)
    => SliceFactorDrop To (SliceFactor To i x) x

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

--------------------------------------------------------------------------------
-- SliceFactorDrop - Morphism -

instance Morphism (SliceFactorDrop s) where
  type ObjectClass (SliceFactorDrop s) = Mlt
  homomorphous SliceFactorFromDrop = Struct :>: Struct
  homomorphous SliceFactorToDrop   = Struct :>: Struct

--------------------------------------------------------------------------------
-- SliceFactorDrop - HomMultiplicative -

instance ApplicativeG Id (SliceFactorDrop s) (->) where
  amapG SliceFactorFromDrop = toIdG slfFactor
  amapG SliceFactorToDrop   = toIdG slfFactor

instance ApplicativeG Pnt (SliceFactorDrop s) (->) where
  amapG SliceFactorFromDrop (Pnt (SliceFrom _ a)) = Pnt (end a)
  amapG SliceFactorToDrop (Pnt (SliceTo _ a))     = Pnt (start a)


instance HomOriented (SliceFactorDrop s)
instance HomMultiplicative (SliceFactorDrop s)

--------------------------------------------------------------------------------
-- slfSliceIndex -

-- | the given attest for the slice index @__i x__@ given by the diagram proxy.
slfSliceIndex :: Sliced i x => Diagram t n m (SliceFactor To i x) -> i x
slfSliceIndex _ = unit1

--------------------------------------------------------------------------------
-- dgSlfToSlicePoint -

-- | the diagram as a cone with its tip given by the 'slicePoint'.
dgSlfToSlicePoint :: (Multiplicative x, Sliced i x)
  => Diagram t n m (SliceFactor To i x) -> Cone Mlt Injective Diagram t n m x
dgSlfToSlicePoint d = ConeInjective d' t cs where
  d' = dgMap SliceFactorToDrop d
  t  = slicePoint $ slfSliceIndex d
  cs = amap1 slice $ dgPoints d

--------------------------------------------------------------------------------
-- slfLimesInjective -

-- | the induced 'Injective' limes for 'SliceFactor'. 
slfLimesInjective :: (Multiplicative x, Sliced i x)
  => Limits Mlt Injective t n m x
  -> Diagram t n m (SliceFactor To i x)
  -> Limes Mlt Injective t n m (SliceFactor To i x)
slfLimesInjective l dgSlf = LimesInjective slfLim slfUniv where
  LimesInjective lLim lUniv = limes l (dgMap SliceFactorToDrop dgSlf)
  
  slfLim = ConeInjective dgSlf tSlf csSlf where
    tSlf = SliceTo (slfSliceIndex dgSlf) (lUniv (dgSlfToSlicePoint dgSlf))
    csSlf = amap1 (\(s,f) -> SliceFactor s tSlf f) (dgPoints dgSlf `zip` shell lLim)

  slfUniv slfCn = case cnDiagramTypeRefl slfCn of
    Refl -> SliceFactor (tip slfLim) (tip slfCn) u where
              u = lUniv $ cnMap SliceFactorToDrop slfCn

--------------------------------------------------------------------------------
-- slfLimitsInjective -

-- | the induced 'Injective' 'Limits'.
slfLimitsInjective :: (Multiplicative x, Sliced i x)
  => Limits Mlt Injective t n m x -> Limits Mlt Injective t n m (SliceFactor To i x)
slfLimitsInjective lms = LimitsG $ slfLimesInjective lms


--------------------------------------------------------------------------------
-- xSliceTo -

-- | the induced random variable.
xSliceTo :: Sliced i x
  => XOrtSite To x -> i x -> X (Slice To i x)
xSliceTo (XEnd _ xTo) i = xTo (slicePoint i) >>= return . SliceTo i

--------------------------------------------------------------------------------
-- xSlicFrom -

-- | the induced random variable.
xSliceFrom :: Sliced i x
  => XOrtSite From x -> i x -> X (Slice From i x)
xSliceFrom (XStart _ xFrom) i = xFrom (slicePoint i) >>= return . SliceFrom i

--------------------------------------------------------------------------------
-- xosXOrtSiteToSliceFactorTo -

-- | the induced random variable.
xosXOrtSiteToSliceFactorTo :: (Multiplicative x, Sliced i x)
  => XOrtSite To x -> i x -> XOrtSite To (SliceFactor To i x)
xosXOrtSiteToSliceFactorTo xTo@(XEnd _ xTo') i = XEnd xp xsfTo where
  xp = xSliceTo xTo i
  xsfTo e@(SliceTo i a) = do
    f <- xTo' (start a)
    return (SliceFactor (SliceTo i (a*f)) e f)

--------------------------------------------------------------------------------
-- xosXOrtSiteFromSliceFactorFrom -

-- | the induced random variable.
xosXOrtSiteFromSliceFactorFrom :: (Multiplicative x, Sliced i x)
  => XOrtSite From x -> i x -> XOrtSite From (SliceFactor From i x)
xosXOrtSiteFromSliceFactorFrom xFrom@(XStart _ xFrom') i = XStart xp xsfFrom where
  xp = xSliceFrom xFrom i
  xsfFrom s@(SliceFrom i a) = do
    f <- xFrom' (end a)
    return (SliceFactor s (SliceFrom i (f*a)) f)

--------------------------------------------------------------------------------
-- SliceFactor - XStandardOrtStite From -

instance (Multiplicative x, Sliced i x, XStandardOrtSite From x)
  => XStandardOrtSite From (SliceFactor From i x) where
  xStandardOrtSite = xosXOrtSiteFromSliceFactorFrom xStandardOrtSite unit1

instance (Multiplicative x, Sliced i x, XStandardOrtSite From x)
  => XStandardOrtSiteFrom (SliceFactor From i x)

instance (Multiplicative x, Sliced i x, XStandardOrtSite From x)
  => XStandard (SliceFactor From i x) where
  xStandard = xosOrt ( xStandardOrtSite
                       :: (Multiplicative x, Sliced i x, XStandardOrtSite From x)
                       => XOrtSite From (SliceFactor From i x)
                     )

instance (Multiplicative x, Sliced i x, XStandardOrtSite From x)
  => XStandard (Slice From i x) where
  xStandard = xosPoint ( xStandardOrtSite
                         :: (Multiplicative x, Sliced i x, XStandardOrtSite From x)
                         => XOrtSite From (SliceFactor From i x)
                       )
instance (Multiplicative x, Sliced i x, XStandardOrtSite From x)
  => XStandardPoint (SliceFactor From i x)

--------------------------------------------------------------------------------
-- SliceFactor - XStandardOrtStite To -

instance (Multiplicative x, Sliced i x, XStandardOrtSite To x)
  => XStandardOrtSite To (SliceFactor To i x) where
  xStandardOrtSite = xosXOrtSiteToSliceFactorTo xStandardOrtSite unit1

instance (Multiplicative x, Sliced i x, XStandardOrtSite To x)
  => XStandardOrtSiteTo (SliceFactor To i x)

instance (Multiplicative x, Sliced i x, XStandardOrtSite To x)
  => XStandard (SliceFactor To i x) where
  xStandard = xosOrt ( xStandardOrtSite
                       :: (Multiplicative x, Sliced i x, XStandardOrtSite To x)
                       => XOrtSite To (SliceFactor To i x)
                     )

instance (Multiplicative x, Sliced i x, XStandardOrtSite To x)
  => XStandard (Slice To i x) where
  xStandard = xosPoint ( xStandardOrtSite
                         :: (Multiplicative x, Sliced i x, XStandardOrtSite To x)
                         => XOrtSite To (SliceFactor To i x)
                       )
instance (Multiplicative x, Sliced i x, XStandardOrtSite To x)
  => XStandardPoint (SliceFactor To i x)

--------------------------------------------------------------------------------

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
-- the given @'XOrtSite' 'To'@ of the @'SliceFactor' 'To' __i x__@. Such a terminal point is given
-- by @'one' s@ where @s@ is the slice point. 
xosAdjTerminal :: (Multiplicative x, Sliced i x)
  => Q -> XOrtSite To (SliceFactor To i x) -> XOrtSite To (SliceFactor To i x)
xosAdjTerminal w xos@(XEnd xp xf) = XEnd xp' xf where
  xp' = xOneOfXW [(w0,xp),(w,return s)]
  w0  = 1 - w
  i   = slfIndex xos
  s   = SliceTo i (one $ slicePoint i)


--------------------------------------------------------------------------------
-- Slice - Structure -

type instance Point (Slice s i x) = Point x

instance ShowPoint x => ShowPoint (Slice s i x)
instance EqPoint x => EqPoint (Slice s i x)
instance ValidablePoint x => ValidablePoint (Slice s i x)
instance TypeablePoint x => TypeablePoint (Slice s i x)

instance (Oriented x, Sliced i x, Typeable s) => Oriented (Slice s i x) where
  orientation s = orientation $ slice s

instance (Sliced i x, Ord x) => Ord (Slice s i x) where
  compare (SliceFrom _ a ) (SliceFrom _ b) = compare a b
  compare (SliceTo _ a) (SliceTo _ b)      = compare a b
  
--------------------------------------------------------------------------------
-- Slice From - OrientedOpl -

instance Multiplicative x => Opl x (Slice From i x) where
  f *> (SliceFrom i c) = SliceFrom i (f*c)

instance (Multiplicative x, Sliced i x) => OrientedOpl x (Slice From i x)

type instance Root (Slice s i x) = Point x

instance ShowPoint x => ShowRoot (Slice s i x)
instance EqPoint x => EqRoot (Slice s i x)
instance ValidablePoint x => ValidableRoot (Slice s i x)
instance TypeablePoint x => TypeableRoot (Slice s i x)

instance (Distributive x, Sliced i x, Typeable s) => Fibred (Slice s i x) where
 root (SliceFrom _ s) = end s
 root (SliceTo _ s)   = start s

instance (Distributive x, Sliced i x) => Additive (Slice From i x) where
  zero e = SliceFrom i (zero (slicePoint i :> e))
    where i = i' e
          i' :: Sliced i x => Point x -> i x
          i' _ = unit1

  SliceFrom i a + SliceFrom _ b = SliceFrom i (a+b)

  ntimes n (SliceFrom i a) = SliceFrom i (ntimes n a)
  
instance (Distributive x, Abelian x, Sliced i x) => Abelian (Slice From i x) where
  negate (SliceFrom i a) = SliceFrom i (negate a)

  SliceFrom i a - SliceFrom _ b = SliceFrom i (a-b)
  
  ztimes z (SliceFrom i a) = SliceFrom i (ztimes z a)

instance (Distributive x, Vectorial x, Sliced i x) => Vectorial (Slice From i x) where
  type Scalar (Slice From i x) = Scalar x
  x ! SliceFrom i a = SliceFrom i (x!a)


