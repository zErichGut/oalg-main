
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Structure.Oriented.X
-- Description : random variables for oriented structures.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- random variables for 'Oriented' structures.
module OAlg.Structure.Oriented.X
  (

    -- * Site
    XOrtSite(..), OrtSiteX, XStandardOrtSite(..)
  , XStandardOrtSiteTo, XStandardOrtSiteFrom
  , coXOrtSite, coXOrtSiteInv, xosFromOpOp
  , xosStart, xosEnd
  , xosPathMaxAt, xosPathMax

    -- * Orientation
  , XOrtOrientation(..), xoOrientation, xoArrow, xoPoint
  , coXOrtOrientation
  , xoTo, xoFrom
  , xoTtl, xoOrnt
  , XStandardOrtOrientation(..)

    -- * Orientation
  , xStartOrnt, xEndOrnt
  )
  where

import Control.Monad as M
import Control.Applicative ((<|>))

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Oriented.Opposite
import OAlg.Structure.Oriented.Path


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
-- XStandardOrtSite t U -

xosUFrom :: X x -> XOrtSite From (U x)
xosUFrom xx = XStart (return ()) (const (amap1 U xx))

xosUTo :: X x -> XOrtSite To (U x)
xosUTo xx = XEnd (return ()) (const (amap1 U xx))

instance XStandard x => XStandardOrtSite To (U x) where
  xStandardOrtSite = xosUTo xStandard

instance XStandard x => XStandardOrtSite From (U x) where
  xStandardOrtSite = xosUFrom xStandard
  
instance XStandard x => XStandardOrtSiteTo (U x)
instance XStandard x => XStandardOrtSiteFrom (U x)

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

instance XStandardOrtSite To a => XStandardOrtSite From (Op a) where
  xStandardOrtSite = co xStandardOrtSite where
    co :: XOrtSite To a -> XOrtSite From (Op a)
    co = coXOrtSite

--------------------------------------------------------------------------------
-- XStandardOrtSiteTo -

-- | standard random variable for @'XOrtSite' 'To'@, helper class to avoid undecidable instances.
class XStandardOrtSite To a => XStandardOrtSiteTo a

instance XStandard p => XStandardOrtSiteTo (Orientation p)
instance XStandardOrtSiteFrom x => XStandardOrtSiteTo (Op x)

--------------------------------------------------------------------------------
-- XStandardOrtSiteFrom -

-- | standard random variable for @'XOrtSite' 'From'@, helper class to avoid undecidable instances.
class XStandardOrtSite From a => XStandardOrtSiteFrom a

instance XStandard p => XStandardOrtSiteFrom (Orientation p)
instance XStandardOrtSiteTo x => XStandardOrtSiteFrom (Op x)

--------------------------------------------------------------------------------
-- OrtSiteX -

-- | type for 'Oriented' structures admitting 'XStandardOrtSiteTo' and 'XStandardOrtSiteFrom'.
--
-- __Note__ The main point is that @'TransformableG' 'Op' 'OrtSiteX' 'OrtSiteX'@ holds!
data OrtSiteX

type instance Structure OrtSiteX x
  = ( Oriented x
    , XStandardOrtSiteTo x
    , XStandardOrtSiteFrom x
    )

instance Transformable OrtSiteX Ort where tau Struct = Struct
instance TransformableOrt OrtSiteX

instance Transformable OrtSiteX Typ where tau Struct = Struct

instance TransformableG Op OrtSiteX OrtSiteX where
  tauG Struct = Struct
instance TransformableOp OrtSiteX

instance Transformable OrtSiteX Type where tau _ = Struct
instance TransformableType OrtSiteX

instance TransformableGRefl Op OrtSiteX

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

instance XStandardOrtOrientation x => XStandardOrtOrientation (Op x) where
  xStandardOrtOrientation = XOrtOrientation xo' xq' where
    XOrtOrientation xo xq = xStandardOrtOrientation
    xo'   = amap1 opposite xo
    xq' o = xq (opposite o) >>= return . Op

instance XStandard x => XStandardOrtOrientation (U x) where
  xStandardOrtOrientation = XOrtOrientation xo xq where
    xo = return (():>())
    xq _ = amap1 U xStandard
    


