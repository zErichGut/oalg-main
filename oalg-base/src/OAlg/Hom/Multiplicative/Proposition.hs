
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving, DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Hom.Multiplicative.Proposition
-- Description : propositions on homomorphisms between multiplicative structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on homomorphisms between 'Multiplicative' structures.
module OAlg.Hom.Multiplicative.Proposition
  (
    -- * Proposition
    prpHomOpMlt

    -- * Multiplicative
  , prpHomMlt, XHomMlt(..), coXHomMlt, coXHomMltInv
  , SomeApplPnt(..), coSomeApplPnt, coSomeApplPntInv
  , SomeApplMltp2(..), coSomeApplMltp2, coSomeApplMltp2Inv
  , prpHomMlt1, prpHomMlt2

    -- * X
  , xHomMlt, xHomMlt', xSomeApplPnt, xSomeApplMltp2
  )
  where

import Control.Monad

import OAlg.Prelude

import OAlg.Data.Symbol

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative.Definition

--------------------------------------------------------------------------------
-- SomeApplPnt -

-- | some application on a point.
data SomeApplPnt h where
  SomeApplPnt :: h a b -> Point a -> SomeApplPnt h

--------------------------------------------------------------------------------
-- SomeApplPnt - Duality -

type instance Dual (SomeApplPnt h) = SomeApplPnt (OpHom h)

-- | to the dual of @'SomeApplPnt' __h__@ with its inverse 'coSomeApplPntInv'.
coSomeApplPnt :: Transformable1 Op (ObjectClass h) => SomeApplPnt h -> Dual (SomeApplPnt h)
coSomeApplPnt (SomeApplPnt h p) = SomeApplPnt (OpHom h) p

-- | from the dual of @'Dual' ('SomeApplPnt' __h__)@ with its inverse 'coSomeApplPnt'.
coSomeApplPntInv :: Dual (SomeApplPnt h) -> SomeApplPnt h
coSomeApplPntInv (SomeApplPnt (OpHom h) p) = SomeApplPnt h p

--------------------------------------------------------------------------------
-- prpHomMlt1 -

relHomMlt1Homomorphous :: Hom Mlt h => Homomorphous Mlt a b -> h a b -> Point a -> Statement
relHomMlt1Homomorphous (Struct:>:Struct) f p
  = (amap f (one p) == one (pmap f p)) :?> Params ["p":=show p] 

-- | validity according to "OAlg.Hom.Multiplicative#HomMlt1".
prpHomMlt1 :: Hom Mlt h => h a b -> Point a -> Statement
prpHomMlt1 f p = Prp "HomMlt1"
  :<=>: relHomMlt1Homomorphous (tauHom (homomorphous f)) f p

--------------------------------------------------------------------------------
-- prpHomMlt2 -

relHomMlt2Homomorphous :: Hom Mlt h => Homomorphous Mlt a b -> h a b -> Mltp2 a -> Statement
relHomMlt2Homomorphous (Struct:>:Struct) f (Mltp2 x y)
  = (amap f (x * y) == amap f x * amap f y)
      :?> Params ["x":=show x,"y":=show y]

-- | validity according to "OAlg.Hom.Multiplicative#HomMlt2".
prpHomMlt2 :: Hom Mlt h => h a b -> Mltp2 a -> Statement
prpHomMlt2 f m2 = Prp "HomMlt2"
  :<=>: relHomMlt2Homomorphous (tauHom (homomorphous f)) f m2

--------------------------------------------------------------------------------
-- SomeApplMltp2 -

-- | some application on multiplicable factors.
data SomeApplMltp2 h where
  SomeApplMltp2 :: h a b -> Mltp2 a -> SomeApplMltp2 h

--------------------------------------------------------------------------------
-- SomeApplMltp2 - Duality -

type instance Dual (SomeApplMltp2 h) = SomeApplMltp2 (OpHom h)

-- | to the dual of @'SomeApplMltp2' __h__@ with its inverse 'coSomeApplMltp2Inv'.
coSomeApplMltp2 :: HomMultiplicative h => SomeApplMltp2 h -> Dual (SomeApplMltp2 h)
coSomeApplMltp2 (SomeApplMltp2 h m2) = SomeApplMltp2 h' m2' where
  h' = OpHom h
  m2' = toDualStruct (tau (domain h)) m2
  
  toDualStruct :: Struct Ort a -> Mltp2 a -> Mltp2 (Op a)
  toDualStruct Struct = toDual

-- | from the dual of @'Dual' ('SomeApplMltp2' __h__)@ with its inverse 'coSomeApplMltp2'.
coSomeApplMltp2Inv :: HomMultiplicative h => Dual (SomeApplMltp2 h) -> SomeApplMltp2 h
coSomeApplMltp2Inv (SomeApplMltp2 (OpHom h) m2') = SomeApplMltp2 h m2 where
  m2 = fromDualStruct (tau (domain h)) m2'

  fromDualStruct :: Struct Ort a -> Mltp2 (Op a) -> Mltp2 a
  fromDualStruct Struct = fromDual

--------------------------------------------------------------------------------
-- XHomMlt -

-- | random variable for validating a type family @__h__@ according to 'HomMultiplicative'.
data XHomMlt h
  = XHomMlt (X (SomeApplPnt h)) (X (SomeApplMltp2 h))

--------------------------------------------------------------------------------
-- XHomMlt - Duality -

type instance Dual (XHomMlt h) = XHomMlt (OpHom h)

-- | to the dual of @'XHomMlt' __h__@ with its inverse 'coXHomMltInv'.
coXHomMlt :: HomMultiplicative h => XHomMlt h -> Dual (XHomMlt h)
coXHomMlt (XHomMlt xsap xsam2)
  = XHomMlt (amap1 coSomeApplPnt xsap) (amap1 coSomeApplMltp2 xsam2)

-- | from the dual of @'Dual' ('XHomMlt' __h__)@ with its inverse 'coXHomMlt'.
coXHomMltInv :: HomMultiplicative h
  => Dual (XHomMlt h) -> XHomMlt h
coXHomMltInv (XHomMlt xsap' xsam2')
  = XHomMlt (amap1 coSomeApplPntInv xsap') (amap1 coSomeApplMltp2Inv xsam2')

--------------------------------------------------------------------------------
-- prpHomMult -

-- | validity of homomorphisms between 'Multiplicative' structures according to
--   "OAlg.Hom.Multiplicative#HomMlt".
prpHomMlt :: Hom Mlt h => XHomMlt h -> Statement
prpHomMlt (XHomMlt xsap xsam2) = Prp "HomMlt"
  :<=>: And [ Forall xsap (\(SomeApplPnt f p) -> prpHomMlt1 f p)
            , Forall xsam2 (\(SomeApplMltp2 f m2) -> prpHomMlt2 f m2)
            ]

--------------------------------------------------------------------------------
-- SomeApplMlt -

-- | some application on 'Oriented' 'Site'.
data SomeApplMlt d h where
  SomeApplMlt :: h a b -> XOrtSite d a -> SomeApplMlt d h

--------------------------------------------------------------------------------
-- SomeApplMlt - Dualisable -

type instance Dual (SomeApplMlt To h) = SomeApplMlt From (OpHom h)

-- | to the dual of @'SomeApplMlt' 'To' __h__@.
coSomeApplMltTo :: Transformable1 Op (ObjectClass h)
  => SomeApplMlt To h -> Dual (SomeApplMlt To h)
coSomeApplMltTo (SomeApplMlt h xe@(XEnd _ _)) = SomeApplMlt h' xs' where
    h'  = OpHom h
    xs' = toDual xe

--------------------------------------------------------------------------------
-- xSomeApplPnt -

-- | random variable for some application on a point given by a 'SomeApplMlt'.
xSomeApplPnt :: SomeApplMlt d h -> X (SomeApplPnt h)
xSomeApplPnt (SomeApplMlt h (XStart xp _))
  = xp >>= return . SomeApplPnt h
xSomeApplPnt (SomeApplMlt h (XEnd xp _))
  = xp >>= return . SomeApplPnt h


--------------------------------------------------------------------------------
-- xSomeApplMltp2 -

-- | random variable for some application on multiplicable factors given by a 'SomeApplMlt'.
xSomeApplMltp2 :: Hom Mlt h => SomeApplMlt d h -> X (SomeApplMltp2 h)
xSomeApplMltp2 (SomeApplMlt h xs@(XStart _ _))
  = xSam2Start xs (tau (domain h)) h where
  
      xSam2Start :: XOrtSite From a -> Struct Mlt a
        -> h a b -> X (SomeApplMltp2 h)
      xSam2Start xs Struct h = xMltp2 xs >>= return . SomeApplMltp2 h
      
xSomeApplMltp2 sa@(SomeApplMlt _ (XEnd _ _))
  = amap1 coSomeApplMltp2Inv $ xSomeApplMltp2 $ coSomeApplMltTo sa

--------------------------------------------------------------------------------
-- xHomMlt -

-- | the induced random variable of 'XHomMlt', given by 'SomeApplMlt'.
xHomMlt :: Hom Mlt h => SomeApplMlt d h -> XHomMlt h
xHomMlt sams = XHomMlt xsap xsam2 where
  xsap  = xSomeApplPnt sams
  xsam2 = xSomeApplMltp2 sams

--------------------------------------------------------------------------------
-- xHomMlt' -

-- | the induced random variable of 'XHomMlt'.
xHomMlt' :: h a b -> XMlt a -> XHomMlt h
xHomMlt' h (XMlt _ xp _ _ xa2 _) = XHomMlt xsp xsa2 where
  xsp = amap1 (SomeApplPnt h) xp
  xsa2 = amap1 (SomeApplMltp2 h) xa2

--------------------------------------------------------------------------------
-- prpHomOpMlt -

-- | validity of @'HomOp' 'Mlt'@ to be a family of 'Multiplicative' homomorphisms.
prpHomOpMlt :: Statement
prpHomOpMlt = Prp "HomOpMlt"
  :<=>: And [ prpHomMlt xsaToOpOp
            , prpHomMlt xsaOpposite
            , prpHomMlt xsaOpPathInv
            ] where

    xeo :: XOrtSite To (Orientation Symbol)
    xeo = xEndOrnt xSymbol

    xsp' :: XOrtSite From (Path (Op (Orientation Symbol)))
    xsp' = xosXOrtSitePath (toDual xeo) 10
    
    xsaOpposite :: XHomMlt (HomOp Mlt)
    xsaOpposite = xHomMlt (SomeApplMlt Opposite $ toDual xeo)

    xsaOpPathInv :: XHomMlt (HomOp Mlt)
    xsaOpPathInv = xHomMlt (SomeApplMlt OpPathInv $ xsp')

    xsaToOpOp :: XHomMlt (HomOp Mlt)
    xsaToOpOp = xHomMlt (SomeApplMlt ToOpOp xeo)
