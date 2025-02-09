
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Structure.Oriented.Definition
-- Description : definition of oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of 'Oriented' structures.
module OAlg.Structure.Oriented.Definition
  (
    -- * Oriented
    Oriented(..), Total, EntityPoint, OrdPoint, isEndo, isEndoAt
  , OS, Ort, structOrtOp, TransformableOrt

    -- * Transposable
  , TransposableOriented

    -- * Orientation
  , Orientation(..), opposite

    -- * Path
  , Path(..), pthLength, pthOne, pthMlt

    -- * X
    -- ** Site
  , XOrtSite(..), XStandardOrtSite(..)
  , XStandardOrtSiteTo, XStandardOrtSiteFrom
  , coXOrtSite, coXOrtSiteInv, xosFromOpOp
  , xosStart, xosEnd
  , xosPathMaxAt, xosPathMax

    -- ** Orientation
  , XOrtOrientation(..), xoOrientation, xoArrow, xoPoint
  , coXOrtOrientation
  , xoTo, xoFrom
  , xoTtl, xoOrnt
  , XStandardOrtOrientation(..)

    -- ** Orientation
  , XStandardPoint
  , xStartOrnt, xEndOrnt
  
  )
  where

import Control.Monad
import Control.Applicative ((<|>))
import Data.Typeable
import Data.Foldable
import Data.List (map,reverse,(++))

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Singleton
import OAlg.Data.Symbol

import OAlg.Category.Unify

import OAlg.Structure.Exception

--------------------------------------------------------------------------------
-- Orientation -
infix 5 :>
  
-- | orientation given by the start point as its first component and the end point as its
--   second.
--
--  __Property__ For all @o@ in __@'Orientation' p@__ holds:
--  @o '==' 'start' o ':>' 'end' o@.
--
--  __Note__ As 'Orientation's are instances of almost all algebraic structures
--  defined here, they serve as a /proof/ that this structures are instanceable.
data Orientation p = p :> p deriving (Show,Eq,Ord)

instance Validable p => Validable (Orientation p) where
  valid (s :> e) = And [valid s,valid e]

instance Entity p => Entity (Orientation p)

instance Singleton u => Singleton (Orientation u) where
  unit = unit :> unit

instance Functor Orientation where
  fmap f (a :> b) = f a :> f b

instance XStandard p => XStandard (Orientation p) where
  xStandard = xTupple2 xStandard xStandard >>= return . uncurry (:>)

--------------------------------------------------------------------------------
-- opposite -

-- | the opposite orientation.
opposite :: Orientation p -> Orientation p
opposite (s:>e) = e:>s

--------------------------------------------------------------------------------
-- OS -

-- | as @'Orientation' p@ is an instance of almost every structured class it
--   serves as a standard type for validating.
type OS = Orientation Symbol

--------------------------------------------------------------------------------
-- Oriented -

-- | types with a 'Oriented' structure. The values of an 'Oriented' structure will
-- be called __/arrows/__ and the values of the associated 'Point' type __/points/__. To each
-- arrow there is a __/'start'/__ and a __/'end'/__ point assigned.
--
-- __Property__ Let __@q@__ be a type instance of the class 'Oriented', then holds:
--
-- (1) #Ort1#For all @a@ in __@q@__ holds: @'orientation' a '==' 'start' a ':>' 'end' a@.
--
-- __Note__
--
-- (1) If the types @__q__@ and @'Point' __q__@ are interpreted as sets
-- @__A__@ and @__P__@ and 'start', 'end' as functions from @__A__@ to @__P__@
-- then this structure forms a __/quiver/__ with __/arrows/__ in @__A__@
-- and __/points/__ in @__P__@.
-- 
-- (2) 'Morphism's can be interpreted as 'Oriented' structures via 'SomeMorphism'.
-- The bad thing about this is that we lose the check for /composability/ of two
-- 'Morphism's given by the type checker, but we gain all the functionality of
-- 'Oriented' structures, i.e we can define homomorphisms,
-- limits etc on 'Morphism's.
class (Entity q, Entity (Point q)) => Oriented q where
  {-# MINIMAL orientation | (start,end) #-}
  
  -- | the associated type of points.
  type Point q
  
  -- | the orientation of an arrow.
  orientation :: q -> Orientation (Point q)
  orientation a = start a :> end a

  -- | the start point of an arrow.
  start :: q -> Point q
  start a = s where s :> _ = orientation a

  -- | the end point of an arrow.
  end :: q -> Point q
  end a = e where _ :> e = orientation a

--------------------------------------------------------------------------------
-- isEndo -

-- | check for being an endo.
--
--  __Definition__ Let @__q__@ be a 'Oriented' structure, then an arrow @a@ in @__q__@
--  is called __/endo/__ if and only if @'start' a '==' 'end' a@.
isEndo :: Oriented q => q -> Bool
isEndo a = start a == end a

--------------------------------------------------------------------------------
-- isEndoAt -

-- | check for being an endo at the given point.
isEndoAt :: Oriented a => Point a -> a -> Bool
isEndoAt p a = orientation a == p :> p

--------------------------------------------------------------------------------
-- Oriented - Instance -

instance Oriented () where
  type Point () = ()
  orientation _ = ():>()

instance Oriented Int where
  type Point Int = ()
  orientation _ = ():>()
  
instance Oriented Integer where
  type Point Integer = ()
  orientation _ = ():>()
  
instance Oriented N where
  type Point N = ()
  orientation _ = ():>()

instance Oriented Z where
  type Point Z = ()
  orientation _ = ():>()

instance Oriented Q where
  type Point Q = ()
  orientation _ = ():>()

instance Entity p => Oriented (Orientation p) where
  type Point (Orientation p) = p
  orientation = id

instance Oriented q => Oriented (Op q) where
  type Point (Op q) = Point q
  orientation (Op a) = opposite (orientation a)
  
instance (Morphism m, TransformableObjectClassTyp m, Entity2 m) => Oriented (SomeMorphism m) where
  type Point (SomeMorphism m) = SomeObjectClass m
  start (SomeMorphism f) = SomeObjectClass (domain f)
  end (SomeMorphism f) = SomeObjectClass (range f)
  
--------------------------------------------------------------------------------
-- TransposableOriented -

-- | transposable oriented structures.
--
--  __Property__ Let @__q__@ be a 'TransposableOriented' structure, then holds:
--  For all @a@ in @__q__@ holds:
--  @'orientation' ('transpose' a) '==' 'opposite' ('orientation' a)@.
class (Transposable q, Oriented q) => TransposableOriented q

instance Transposable (Orientation p) where
  transpose = opposite
instance Entity p => TransposableOriented (Orientation p)

instance TransposableOriented N
instance TransposableOriented Z
instance TransposableOriented Q
--------------------------------------------------------------------------------
-- Path -

-- | a path in a 'Oriented' structure @__q__@ starting at a given point.
--
-- __Definition__ Let @__q__@ be a 'Oriented' structure and @p = 'Path' s [a 0..a (n-1)]@ a
-- path in @__q__@, then @p@ is 'valid' if and only if
--
-- (1) @s@ is 'valid' and @a i@ are 'valid' for all @i = 0..n-1@.
--
-- (2) @'start' (a (n-1)) '==' s@ and @'start' (a i) '==' 'end' (a (n+1))@ for all @i = 0..n-2@.
--
-- furthermore @n@ is called the __/length/__ of @p@.
--
-- __Note__ Paths admit a canonical embedding in to 'OAlg.Entity.Product.Product'.
data Path q = Path (Point q) [q]

deriving instance Oriented q => Show (Path q)
deriving instance Oriented q => Eq (Path q)

instance Foldable Path where
  foldr op b (Path _ fs) = foldr op b fs 

instance Oriented q => Validable (Path q) where
  valid (Path s [])     = valid s
  valid (Path s (f:gs)) = valid s && valid f && vld s f gs where
    vld s f []     = start f .==. s
    vld s f (g:gs) = valid g && start f .==. end g && vld s g gs 

instance Oriented q => Entity (Path q)

instance Oriented q => Oriented (Path q) where
  type Point (Path q) = Point q
  orientation (Path s [])    = s:>s
  orientation (Path s (f:_)) = s:>end f
 
type instance Dual (Path q) = Path (Op q)

instance Oriented q => Dualisable (Path q) where
  toDual p@(Path _ fs)   = Path (end p) (reverse $ map Op fs)
  fromDual p@(Path _ fs) = Path (end p) (reverse $ map fromOp fs)

instance Reflexive (Path q) where
  toBidual (Path s fs) = Path s (map (Op . Op) fs)
  fromBidual (Path s fs) = Path s (map (fromOp . fromOp) fs)

instance Oriented q => Embeddable q (Path q) where
  inj f = Path (start f) [f]

--------------------------------------------------------------------------------
-- pthLength -

-- | the length of a path.
pthLength :: Path q -> N
pthLength (Path _ fs) = lgth fs where
  lgth []     = 0
  lgth (_:fs) = succ (lgth fs)
  
instance LengthN (Path q) where
  lengthN = pthLength

--------------------------------------------------------------------------------
-- pthOne -

-- | path of length 0 at the given point.
pthOne :: Point q -> Path q
pthOne s = Path s []

--------------------------------------------------------------------------------
-- pthMlt -

-- | composition of two paths.
pthMlt :: Oriented q => Path q -> Path q -> Path q
pthMlt (Path s fs) p@(Path t gs)
  | s == end p = Path t (fs++gs)
  | otherwise  = throw NotMultiplicable

--------------------------------------------------------------------------------
-- Total -

-- | structures where its associated 'Point' type is singleton. They yield
-- globally defiend algebraic operations.
class Singleton (Point x) => Total x

instance Total ()
instance Total Int
instance Total Integer
instance Total N
instance Total Z
instance Total Q
instance Total q => Total (Path q)
instance Total x => Total (Op x)

--------------------------------------------------------------------------------
-- EntityPoint -

-- | helper class to avoid undecidable instances.
class Entity (Point x) => EntityPoint x

instance EntityPoint ()
instance EntityPoint Int
instance EntityPoint Integer
instance EntityPoint N
instance EntityPoint Z
instance EntityPoint Q
instance EntityPoint q => EntityPoint (Path q)
instance EntityPoint x => EntityPoint (Op x)

--------------------------------------------------------------------------------
-- OrdPoint -

-- | helper class to circumvent undecidable instances.
class Ord (Point x) => OrdPoint x

instance OrdPoint ()
instance OrdPoint Int
instance OrdPoint Integer
instance OrdPoint N
instance OrdPoint Z
instance OrdPoint Q
instance OrdPoint q => OrdPoint (Path q)

--------------------------------------------------------------------------------
-- Ort -

-- | type representing the class of 'Oriented' structures.
data Ort

type instance Structure Ort x = Oriented x

instance Transformable Ort Typ where tau Struct = Struct
instance Transformable Ort Ent where tau Struct = Struct
instance Transformable1 Op Ort where tau1 Struct = Struct
instance TransformableOp Ort

--------------------------------------------------------------------------------
-- TransformableOrt -

-- | transformable to 'Oriented' structure.
class Transformable s Ort => TransformableOrt s

instance TransformableTyp Ort
instance TransformableOrt Ort

--------------------------------------------------------------------------------
-- structOrtOp -

-- | attest that if @__x__@ is 'Oriented' then also @'Op' __x__@ is 'Oriented'.
structOrtOp :: Struct Ort x -> Struct Ort (Op x)
structOrtOp Struct = Struct

--------------------------------------------------------------------------------
-- XOrtSite -

-- | random variables @'OAlg.Data.X.X' __q__@ and @'OAlg.Data.X.X' ('Point' __q__)@ for
-- 'Oriented' structure @__q__@.
--
-- __Properties__ Let @__q__@ be an instance of the class 'Oriented', then holds:
--
-- (1) Let @'XStart' xp xStart@ be in @'XOrtSite' 'From' __q__@, then holds:
-- For all @p@ in @'Point' __q__@ and @x@ in the range of @xStart p@ holds: @'start' x '==' p@.
--
-- (2) Let @'XEnd' xp xEnd@ be in @'XOrtSite' 'To' __q__@, then holds:
-- For all @p@ in @'Point' __q__@ and @x@ in the range of @xEnd p@ holds: @'end' x '==' p@.
--
-- __Note__ The random variables @xp@ should have a bias to non trivial random variables
-- @xp '>>=' xStart@ or @xp '>>=' xEnd@.
data XOrtSite s q where
  XStart :: X (Point q) -> (Point q -> X q) -> XOrtSite From q
  XEnd   :: X (Point q) -> (Point q -> X q) -> XOrtSite To q


--------------------------------------------------------------------------------
-- XOrtSite - Dualisable -

type instance Dual (XOrtSite s q) = XOrtSite (Dual s) (Op q)

--------------------------------------------------------------------------------
-- coXOrtSite -

-- | to the dual of a @'XOrtSite' __s__ __q__@, with inverse 'coXOrtSiteInv'.
coXOrtSite :: XOrtSite s q -> Dual (XOrtSite s q)
coXOrtSite (XStart xp xs) = XEnd xp xs' where xs' p = fmap Op (xs p)
coXOrtSite (XEnd xp xe)   = XStart xp xe' where xe' p = fmap Op (xe p)

-- | from the bidual.
xosFromOpOp :: XOrtSite s (Op (Op q)) -> XOrtSite s q
xosFromOpOp (XStart xp xs) = XStart xp xs' where xs' p = fmap fromOpOp (xs p)
xosFromOpOp (XEnd xp xe)   = XEnd xp xe' where xe' p = fmap fromOpOp (xe p)

-- | from the dual of a @'Dual' ('XOrtSite' __s__ __q__)@, with inverse 'coXOrtSite'.
coXOrtSiteInv :: Dual (Dual s) :~: s -> Dual (XOrtSite s q) -> XOrtSite s q
coXOrtSiteInv Refl = xosFromOpOp . coXOrtSite

instance Dualisable (XOrtSite To q) where
  toDual = coXOrtSite
  fromDual = coXOrtSiteInv Refl

--------------------------------------------------------------------------------
-- XOrtSite - Validable -

instance Oriented q => Validable (XOrtSite s q) where
  valid (XStart xp xq)
    = Forall xp
        (\p
         ->    valid p                  
            && Forall (xq p)
                 (\x
                  ->    valid x
                     && (start x == p) :?> Params ["p":=show p,"x":=show x]
                 )
        )
  valid xe@(XEnd _ _) = valid (toDual xe)

--------------------------------------------------------------------------------
-- xosStart -

-- | the random variable of arrows in @__q__@ having all as 'start' the given point.
xosStart :: XOrtSite From q -> Point q -> X q
xosStart (XStart _ xs) = xs

--------------------------------------------------------------------------------
-- xosEnd -

-- | the random variable of arrows in @__q__@ having all as 'end' the given point.
xosEnd :: XOrtSite To q -> Point q -> X q
xosEnd (XEnd _ xe) = xe


--------------------------------------------------------------------------------
-- xosPathMaxAt -

-- | tries to make a path at the given point with maximal length of the given length.
--
-- __Properties__ Let @xPath = 'xosPathMaxAt' xos n x@, then holds:
--
-- (1) If @xos@ matches @'XStart' _ xq@ then for all @p@ in the range of @xPath@ holds:
--
--     (1) @'start' p '==' x@.
--
--     (2) If @'pthLength' p '<' n@ then @xq ('end' p)@ matches 'XEmpty'.
--
-- (2) If @xos@ matches @'XEnd' _ xq@ then for all @p@ in the range of @xPath@ holds:
--
--     (1) @'end' p '==' x@.
--
--     (2) If @'pthLength' p '<' n@ then @xq ('start' p)@ matches 'XEmpty'.
xosPathMaxAt :: Oriented q => XOrtSite s q -> N -> Point q -> X (Path q)
xosPathMaxAt (XStart _ xq) n s = pth n s (pthOne s) where

  (*) = pthMlt
  
  pth 0 _ fs = return fs  
  pth n s fs = case xq s of
    XEmpty -> return fs
    xf     -> xf >>= \f -> pth (pred n) (end f) (inj f * fs)

  inj f = Path (start f) [f]
xosPathMaxAt xe@(XEnd _ _) n e = fmap fromDual $ xosPathMaxAt (toDual xe) n e

--------------------------------------------------------------------------------
-- xosPathMax -

-- | random variable of paths with maximal length of the given length.
xosPathMax :: Oriented q => XOrtSite s q -> N -> X (Path q)
xosPathMax xs@(XStart xp _) n = xp >>= xosPathMaxAt xs n
xosPathMax xe@(XEnd _ _) n    = fmap fromDual $ xosPathMax (toDual xe) n

--------------------------------------------------------------------------------
-- xStartOrnt -

-- | the @'XOrtSite' 'From'@ for @'Orientation' __p__@ of the given random variable.
xStartOrnt :: X p -> XOrtSite From (Orientation p)
xStartOrnt xp = XStart xp xq where xq s = xp >>= return . (s:>)

--------------------------------------------------------------------------------
-- xEndOrnt -

-- | the @'XOrtSite' 'To'@ of @'Orientation' __p__@ of the given random variable.
xEndOrnt :: X p -> XOrtSite To (Orientation p)
xEndOrnt xp = XEnd xp xq where xq e = xp >>= return . (:>e)

--------------------------------------------------------------------------------
-- XStandardOrtSite -

-- | standard random variable for 'XOrtSite'.
class XStandardOrtSite s a where
  xStandardOrtSite :: XOrtSite s a

instance XStandard p => XStandardOrtSite To (Orientation p) where
  xStandardOrtSite = xEndOrnt xStandard

instance XStandard p => XStandardOrtSite From (Orientation p) where
  xStandardOrtSite = xStartOrnt xStandard

instance XStandardOrtSite From a => XStandardOrtSite To (Op a) where
  xStandardOrtSite = co xStandardOrtSite where
    co :: XOrtSite From a -> XOrtSite To (Op a)
    co = coXOrtSite

--------------------------------------------------------------------------------
-- XStandardOrtSiteTo -

-- | standard random variable for @'XOrtSite' 'To'@, helper class to avoid undecidable instances.
class XStandardOrtSite To a => XStandardOrtSiteTo a

instance XStandard p => XStandardOrtSiteTo (Orientation p)

--------------------------------------------------------------------------------
-- XStandardOrtSiteFrom -

-- | standard random variable for @'XOrtSite' 'From'@, helper class to avoid undecidable instances.
class XStandardOrtSite From a => XStandardOrtSiteFrom a

instance XStandard p => XStandardOrtSiteFrom (Orientation p)

--------------------------------------------------------------------------------
-- XStandardPoint -

-- | standard random variable of 'Point's of @__a__@.
class XStandard (Point a) => XStandardPoint a

instance XStandardPoint N
instance XStandardPoint Z
instance XStandardPoint Q
instance XStandard p => XStandardPoint (Orientation p)

--------------------------------------------------------------------------------
-- XOrtOrientation -

-- | random variable of arrows given by an orientation.
--
-- __Properties__ Let @'XOrtOrientation' xo xArrow@ be in @'XOrtOrientation' __q__@ for a
-- 'Oriented' structure @__q__@, then holds: For all @o@ in @'Orientation' __q__@ and @x@ in the
-- range of @xArrow o@ holds: @'orientation' x '==' o@.
--
-- __Note__ The random variable @xo@ should have a bias to non trivial random variables
-- @xo '>>=' xArrow@ and as such the range of @xo@ should be included in one connection component
-- of @__q__@.
data XOrtOrientation q
  = XOrtOrientation (X (Orientation (Point q))) (Orientation (Point q) -> X q)

instance Oriented q => Validable (XOrtOrientation q) where
  valid x@(XOrtOrientation xo xq) = Label (show $ typeOf x) :<=>:
    And [ valid xo
        , Forall xo
            (\o -> Forall (xq o)
              (\q -> And [ valid q
                         , (orientation q == o):?>Params ["o":=show o,"q":=show q]
                         ]
              )
            )
        ]

--------------------------------------------------------------------------------
-- XOrtOrientation - Dual -

type instance Dual (XOrtOrientation q) = XOrtOrientation (Op q)

-- | to the dual.
coXOrtOrientation :: XOrtOrientation q -> Dual (XOrtOrientation q)
coXOrtOrientation (XOrtOrientation xo xq) = XOrtOrientation xo' xq' where
  xo' = amap1 opposite xo
  xq' o' = amap1 Op (xq (opposite o'))

--------------------------------------------------------------------------------
-- xoOrientation -

-- | the underlying random variable of orientations.
xoOrientation :: XOrtOrientation q -> X (Orientation (Point q))
xoOrientation (XOrtOrientation xo _) = xo

--------------------------------------------------------------------------------
-- xoArrow -

-- | the underlying random variable of arrow given by the orientation.
xoArrow :: XOrtOrientation q -> Orientation (Point q) -> X q
xoArrow (XOrtOrientation _ xq) = xq

--------------------------------------------------------------------------------
-- xoPoint -

-- | the underlying random variable of points, i.e. the union of the induced 'start' and 'end'
-- random variable of 'xoOrientation'.
xoPoint :: Oriented q => XOrtOrientation q -> X (Point q)
xoPoint (XOrtOrientation xo _) = amap1 start xo <|> amap1 end xo

--------------------------------------------------------------------------------
-- xoTo -

-- | the induced @'XOrtSite' 'To'@
xoTo :: Oriented q => XOrtOrientation q -> XOrtSite To q
xoTo (XOrtOrientation xo xq) = XEnd xp xTo where
  xp    = amap1 end xo
  xTo e = amap1 start xo >>= xq . (:>e)

--------------------------------------------------------------------------------
-- xoFrom -

-- | the induced @'XOrtSite' 'From'@.
xoFrom :: Oriented q => XOrtOrientation q -> XOrtSite From q
xoFrom xo = coXOrtSiteInv Refl $ xoTo $ coXOrtOrientation xo 

--------------------------------------------------------------------------------
-- xoTtl -

-- | random variable of @'XOrtOrientation' __q__@ for a total @__q__@.
xoTtl :: Total q => X q -> XOrtOrientation q
xoTtl xx = XOrtOrientation xo xq where
  xo = return (unit :> unit)
  xq = const xx

--------------------------------------------------------------------------------
-- xoOrnt -

-- | the induced random variable of @'Orientation' __q__@.
xoOrnt :: X p -> XOrtOrientation (Orientation p)
xoOrnt xp = XOrtOrientation xo xq where
  xo = amap1 (uncurry (:>)) $ xTupple2 xp xp
  xq = return

--------------------------------------------------------------------------------
-- XStandardOrtOrientation -

-- | standard random variable for 'XOrtOrientation'.
class XStandardOrtOrientation q where
  xStandardOrtOrientation :: XOrtOrientation q

instance XStandard p => XStandardOrtOrientation (Orientation p) where
  xStandardOrtOrientation = xoOrnt xStandard

instance XStandardOrtOrientation Z where
  xStandardOrtOrientation = XOrtOrientation (return (():>())) (const xStandard)

