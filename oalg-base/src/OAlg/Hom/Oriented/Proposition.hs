
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Hom.Oriented.Proposition
-- Description : propositions on homomorphisms between oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions on homomorphisms between 'Oriented' structures.
module OAlg.Hom.Oriented.Proposition
  (
    -- * Proposition
    prpIdHomOrt, prpHomOpOrt

  , prpIsoOpOrtCategory, prpIsoOpOrtFunctorial

    -- * Oriented
  , prpHomOrt, XHomOrt
  , prpHomOrt'
  , prpHomOrt1
  , relHomOrtHomomorphous

    -- * X
  , xIsoOpOrtFrom
  )
  where

import Control.Monad
import Control.Applicative

import Data.Type.Equality

import OAlg.Prelude

import OAlg.Data.Constructable

import OAlg.Category.Path as C
import OAlg.Category.Unify

import OAlg.Data.Symbol

import OAlg.Structure.Oriented as O
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition


--------------------------------------------------------------------------------
-- XHomOrt -

-- | random variable to validate homomorphisms between 'Oriented' structures.
type XHomOrt h = XAppl h

--------------------------------------------------------------------------------
-- prpHomOrt -

-- | validity of homomorphisms between 'Oriented' for a given value in the domain.
relHomOrtHomomorphous :: (Hom Ort h, Show2 h)
  => Homomorphous Ort a b -> h a b -> a -> Statement
relHomOrtHomomorphous (Struct:>:Struct) f x
  = And [ (start fx == pmap f (start x)) :?> prms
        , (end fx == pmap f (end x)) :?> prms
        ]
  where prms = Params ["f":=show2 f,"x":=show x]
        fx = amap f x

--------------------------------------------------------------------------------
-- prpHomOrt1 -

-- | validity of homomorphisms between 'Oriented' structures based on the given values.
prpHomOrt1 :: (Hom Ort h, Show2 h) => h a b -> a -> Statement
prpHomOrt1 f x = Prp "HomOrt1" :<=>: relHomOrtHomomorphous (tauHom (homomorphous f)) f x



-- | validity of homomorphisms between 'Oriented' structures based on the given
-- random variable.
prpHomOrt :: (Hom Ort h, Show2 h) => XHomOrt h -> Statement
prpHomOrt xfx = Prp "HomOrt"
  :<=>: Forall xfx (\(SomeApplication f x)
                    -> relHomOrtHomomorphous (tauHom (homomorphous f)) f x
                   )
-- | validity of homomorphisms between 'Oriented' structures based on the given
-- random variable.
prpHomOrt' :: (Hom Ort h, Show2 h) => h a b -> XOrt a -> Statement
prpHomOrt' f xa = Label "prpHomOrt'" :<=>:
  Forall xa (relHomOrtHomomorphous (tauHom (homomorphous f)) f)
  
--------------------------------------------------------------------------------
-- prpIdHomOrt -

-- | validity of @'IdHom' 'Ort'@ to be a family of 'Oriented' homomorphisms between
-- @'Orientation' 'Symbol'@ and t'Z'.
prpIdHomOrt :: Statement
prpIdHomOrt = Prp "IdHomOrt"
  :<=>: prpHomOrt xa where
  
    xa :: XHomOrt (IdHom Ort)
    xa = join $ xOneOf [ xsaIdHomOrnt
                       , fmap (SomeApplication IdHom) xZ
                       ]

    xsaIdHomOrnt :: X (SomeApplication (IdHom Ort))
    xsaIdHomOrnt = fmap (SomeApplication IdHom) $ xOrtOrnt xSymbol

--------------------------------------------------------------------------------
-- prpHomOpOrt -

-- | validity of @'HomOp' 'Ort'@ according to 'HomOriented' on @'Orientation' 'Symbol'@.
prpHomOpOrt :: Statement
prpHomOpOrt = Prp "HomOpOrt"
  :<=>: prpHomOrt xa where

    xo = xOrtOrnt xSymbol
    xs = xStartOrnt xSymbol

    xpth n = xNB 0 n >>= xosPath xs
    
    xa :: XHomOrt (HomOp Ort)
    xa = join $ xOneOf [ fmap (SomeApplication FromOpOp . Op . Op) xo 
                       , fmap (SomeApplication OpPath . Op) $ xpth 10
                       , fmap (SomeApplication Opposite . Op) xo
                       ]
         

--------------------------------------------------------------------------------
-- prpIsoOpOrtCategory -

-- | validity of @'IsoOp' 'Ort'@ according to 'Category' on @'Orientation' 'Symbol'@.
prpIsoOpOrtCategory :: Statement
prpIsoOpOrtCategory = Prp "IsoOpOrtCategory"
  :<=>: prpCategory (xCat $ xMrphSite xIsoOpOrtFrom)

--------------------------------------------------------------------------------
-- prpIsoOpOrtFunctorial -

-- | validity of @'IsoOp' 'Ort'@ according 'Functorial'. 
prpIsoOpOrtFunctorial :: Statement
prpIsoOpOrtFunctorial = Prp "IsoOpOrtFunctorial"
  :<=>: prpFunctorial (xFnct xIsoOpOrtFrom)

--------------------------------------------------------------------------------
-- xIsoOpOrtFrom -

-- | random variale of @'IsoOp' 'Ort'@.
xIsoOpOrtFrom :: XFnctMrphSite From (IsoOp Ort)
xIsoOpOrtFrom = XFnctMrphSite (XDomain xss xsdm) xox where
  
  domOpPath :: Struct Ort (Op (O.Path OS))
  domOpPath = Struct

  domOpPathInv :: Struct Ort (O.Path (Op OS))
  domOpPathInv = Struct

  domOpOS :: Struct Ort (Op OS)
  domOpOS = Struct

  domOpOpOS :: Struct Ort (Op (Op OS))
  domOpOpOS = Struct
  
  domOS :: Struct Ort OS
  domOS = Struct

  xOS = xOrtOrnt xSymbol
  
  xox d =     xdomOS d <|> xdomOpOS d
          <|> xdomOpPath d <|> xdomOpPathInv d
          <|> xdomOpOpOS d

  xdomOS :: Struct Ort x -> X x
  xdomOS d = case testEquality d domOS of
    Just Refl -> xOS
    Nothing   -> XEmpty

  xdomOpOS :: Struct Ort x -> X x
  xdomOpOS d = case testEquality d domOpOS of
    Just Refl -> fmap Op xOS
    Nothing   -> XEmpty

  xdomOpPath :: Struct Ort x -> X x
  xdomOpPath d = case testEquality d domOpPath of
    Just Refl -> fmap Op (xNB 0 10 >>= xosPath (xStartOrnt xSymbol))
    Nothing   -> XEmpty

  xdomOpPathInv :: Struct Ort x -> X x
  xdomOpPathInv d = case testEquality d domOpPathInv of
    Just Refl -> fmap toDual (xNB 0 10 >>= xosPath (xStartOrnt xSymbol))
    Nothing   -> XEmpty

  xdomOpOpOS :: Struct Ort x -> X x
  xdomOpOpOS d = case testEquality d domOpOpOS of
    Just Refl -> fmap (Op . Op) xOS
    Nothing   -> XEmpty
  
  xss = xOneOf [ SomeObjectClass domOS
               , SomeObjectClass domOpPath
               , SomeObjectClass domOpPathInv
               , SomeObjectClass domOpOS
               , SomeObjectClass domOpOpOS
               ]

  xsdm d =    xsdmFromOpOp d <|> xsdmToOpOp d
          <|> xsdmOpPath d <|> xsdmOpPathInv d
          <|> xsdmOpposite d <|> xsdmOppositeInv d
          
  xsdmFromOpOp :: Struct Ort x -> X (SomeMorphismSite From (IsoOp Ort) x)
  xsdmFromOpOp d = case testEquality d domOpOpOS of
    Just Refl -> return $ SomeMorphismDomain (f d)
    _         -> XEmpty

  xsdmToOpOp :: Struct Ort x -> X (SomeMorphismSite From (IsoOp Ort) x)
  xsdmToOpOp d = case testEquality d domOS of
    Just Refl -> return $ SomeMorphismDomain (f' d)
    _         -> XEmpty

  xsdmOpPath :: Struct Ort x -> X (SomeMorphismSite From (IsoOp Ort) x)
  xsdmOpPath d = case testEquality d domOpPath of
    Just Refl -> return $ SomeMorphismDomain (p d)
    _         -> XEmpty

  xsdmOpPathInv :: Struct Ort x -> X (SomeMorphismSite From (IsoOp Ort) x)
  xsdmOpPathInv d = case testEquality d domOpPathInv of
    Just Refl -> return $ SomeMorphismDomain (p' d)
    _         -> XEmpty

  xsdmOpposite :: Struct Ort x -> X (SomeMorphismSite From (IsoOp Ort) x)
  xsdmOpposite d = case testEquality d domOpOS of
    Just Refl -> return $ SomeMorphismDomain (o d)
    _         -> XEmpty

  xsdmOppositeInv :: Struct Ort x -> X (SomeMorphismSite From (IsoOp Ort) x)
  xsdmOppositeInv d = case testEquality d domOS of
    Just Refl -> return $ SomeMorphismDomain (o' d)
    _         -> XEmpty


  f' :: Struct Ort a -> IsoOp Ort a (Op (Op a))
  f' Struct = invert2 isoFromOpOpOrt

  f :: a ~ OS => Struct Ort (Op (Op a)) -> IsoOp Ort (Op (Op a)) a
  f Struct = isoFromOpOpOrt

  p :: a ~ OS => Struct Ort (Op (O.Path a)) -> IsoOp Ort (Op (O.Path a)) (O.Path (Op a))
  p Struct = make (OpPath :. IdPath Struct)

  p' :: a ~ OS => Struct Ort (O.Path (Op a)) -> IsoOp Ort (O.Path (Op a)) (Op (O.Path a))
  p' Struct = make (OpPathInv :. IdPath Struct)

  o :: a ~ OS => Struct Ort (Op a) -> IsoOp Ort (Op a) a
  o Struct = make (Opposite :. IdPath Struct)

  o' :: a ~ OS => Struct Ort a -> IsoOp Ort a (Op a)
  o' Struct = make (OppositeInv :. IdPath Struct)


