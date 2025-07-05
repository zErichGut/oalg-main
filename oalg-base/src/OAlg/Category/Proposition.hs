
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Category.Proposition
-- Description : properties on categories
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on categories.
module OAlg.Category.Proposition
  (
    -- * Category
    prpCategory, XCat(..)
  , prpCategory1
  , prpCategory2, SomeCmpb3(..), SomeCmpb2(..)

    -- * Application
  , XAppl

    -- * Functorial
  , prpFunctorial, XFnct(..)
  , prpFunctorial1
  , prpFunctorial2, SomeCmpbAppl(..)
  , prpFunctorialG

    -- * Cayleyan2
  , prpCayleyan2

    -- * X
    -- ** Categroy
  , xCat, XMrphSite(..), xSomePathSiteMax, xSomePathMax
  , xSomePathSite, xSomePath

    -- ** Functorial
  , xFnct, xMrphSite, XFnctMrphSite(..)

    -- * Inv2
  , relInvEq2
  
  )
  where

import Control.Monad
import Control.Exception
import Data.Kind


import OAlg.Control.Exception

import OAlg.Category.Applicative
import OAlg.Category.Definition
import OAlg.Structure.Definition

import OAlg.Category.Path
import OAlg.Category.Unify

import OAlg.Data.Identity
import OAlg.Data.Proxy
import OAlg.Data.EqualExtensional
import OAlg.Data.Logical
import OAlg.Data.X
import OAlg.Data.Number
import OAlg.Data.Dualisable
import OAlg.Data.Statement
import OAlg.Data.Show
import OAlg.Data.Equal

import OAlg.Entity.Definition

--------------------------------------------------------------------------------
-- XMorphismException -

-- | arithmetic exceptions which are sub exceptions from 'SomeOAlgException'.
data XMorphismException
  = NoSuchEntity
  deriving (Eq,Show)

instance Exception XMorphismException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- XAppl -

-- | random variable for some application.
type XAppl h = X (SomeApplication h)

--------------------------------------------------------------------------------
-- prpCategory1 -

-- | validity according to "OAlg.Category.Category#Cat1".
prpCategory1 :: (Category c, Show2 c, Eq2 c) => X (SomeMorphism c) -> Statement
prpCategory1 xsm = Prp "Category1"
  :<=>: Forall xsm (\(SomeMorphism f)
                    -> let (==) = eq2
                           prm  = Params ["f":=show2 f]
                        in And [ ((cOne (range f) . f) == f) :?> prm
                               , (f == (f . cOne (domain f))) :?> prm
                               ]
                   )

--------------------------------------------------------------------------------
-- SomeCmpb2 -

-- | some composable morphisms.
data SomeCmpb2 c where
  SomeCmpb2 :: c y z -> c x y -> SomeCmpb2 c
  
--------------------------------------------------------------------------------
-- SomeCmpb3 -

-- | some composable morphisms.
data SomeCmpb3 c where
  SomeCmpb3 :: c x w -> c y x ->  c z y -> SomeCmpb3 c

--------------------------------------------------------------------------------
-- prpCategory2

relCategory2 :: (Category c, Show2 c, Eq2 c) => c x w -> c y x ->  c z y -> Statement
relCategory2 f g h
  = (((f . g) . h) == (f . (g . h))) :?> Params ["f":=show2 f,"g":=show2 g,"h":=show2 h]
  where (==) = eq2

relCategory2Path :: (Category c, Show2 c, Eq2 c) => Path c x y -> Statement
relCategory2Path (f :. g :. h :. pth)
  = relCategory2 f g h && relCategory2Path (g :. h :. pth) 
relCategory2Path _  = SValid

-- | validity according to "OAlg.Category.Category#Cat2".
prpCategory2 :: (Category c, Show2 c, Eq2 c) => X (SomeCmpb3 c) -> Statement
prpCategory2 xpth = Prp "Category2"
  :<=>: Forall xpth (\(SomeCmpb3 f g h) -> relCategory2 f g h)

--------------------------------------------------------------------------------
-- XCat -

-- | random variable for validating 'Category'.
data XCat c
  = XCat
  { xcSomeMrph  :: X (SomeMorphism c)
  , xcSomeCmpb3 :: X (SomeCmpb3 c)
  }

--------------------------------------------------------------------------------
-- prpCategory -

-- | validity of a 'Category'.
prpCategory :: (Category c, Eq2 c, Show2 c) => XCat c -> Statement
prpCategory (XCat xm xc3) = Prp "Category"
  :<=>: And [ prpCategory1 xm
            , prpCategory2 xc3
            ]

--------------------------------------------------------------------------------
-- prpFunctorial1 -

-- | validity according to "OAlg.Category.Category#Fnc1".
prpFunctorial1 :: (Functorial c, Show2 c) => X (SomeEntity c) -> Statement
prpFunctorial1 xid = Prp "Functorial1"
  :<=>: Forall xid (\(SomeEntity d x)
                    -> let od = cOne' (p xid) d
                        in (amap od x == x) :?> Params ["od":=show2 od,"x":=show x]
                   )
  where p :: X (SomeEntity c) -> Proxy c
        p _ = Proxy

--------------------------------------------------------------------------------
-- SomeCmpbAppl -

-- | some composable morphisms with an applicable value.
data SomeCmpbAppl c where
  SomeCmpbAppl :: (Entity x, Eq z) => c y z -> c x y -> x -> SomeCmpbAppl c

--------------------------------------------------------------------------------
-- prpFunctorial2 -

-- | validity according to "OAlg.Category.Category#Fnc2".
prpFunctorial2 :: (Functorial c, Show2 c)
  => X (SomeCmpbAppl c) -> Statement
prpFunctorial2 xca = Prp "Functorial2"
  :<=>: Forall xca (\(SomeCmpbAppl f g x)
                    -> (amap (f . g) x == (amap f . amap g) x)
                        :?> Params ["f":=show2 f,"g":=show2 g,"x":=show x]
                   )

--------------------------------------------------------------------------------
-- XFnct - 

-- | random variable for 'Functorial' categories.
data XFnct c where
  XFnct :: X (SomeEntity c) -> X (SomeCmpbAppl c) -> XFnct c

--------------------------------------------------------------------------------
-- prpFunctorial -

-- | validity of a 'Functorial' category.
prpFunctorial :: (Functorial c, Show2 c) => XFnct c -> Statement
prpFunctorial (XFnct xd xca) = Prp "Functorial"
  :<=>: And [ prpFunctorial1 xd
            , prpFunctorial2 xca
            ]

--------------------------------------------------------------------------------
-- prpCayleyan2 -

-- | validity of 'Cayleyan2'.
prpCayleyan2 :: (Cayleyan2 c, Show2 c) => X (SomeMorphism c) -> Statement
prpCayleyan2 xmp = Prp "Cayleyan2"
  :<=>: Forall xmp (\(SomeMorphism f)
                    -> let prm  = Params ["f":=show2 f]
                           (==) = eq2
                           f'   = invert2 f
                        in And [ ((f' . f) == cOne (domain f)) :?> prm
                               , ((f . f') == cOne (range f)) :?> prm
                               ]
                   )

--------------------------------------------------------------------------------
-- relInvEq2 -

-- | validity according to 'Inv2'.
relInvEq2 :: (Category c, Eq2 c, Show2 c) => Inv2 c x y -> Statement
relInvEq2 (Inv2 f g)
  = And [ Label "g . f" :<=>: ((g . f) .=. cOne (domain f)) :?> prms
        , Label "f . g" :<=>: ((f . g) .=. cOne (domain g)) :?> prms
        ]
    where (.=.) = eq2
          prms  = Params ["f":=show2 f, "g":=show2 g]

--------------------------------------------------------------------------------
-- XMrphSite -

-- | random variable of 'SomeObjectClass' and 'SomeMorphismSite' with:
--
--   __Note__
--
--   (1) The random variable @'X' ('SomeObjectClass' m)@ should have a bias towards non
--   terminal respectively initial object classes. For an implementation see
--   'OAlg.Proposition.Homomorphism.Oriented.xIsoOpOrtFrom'.
--
--   (1) It is the analogue to 'OAlg.Proposition.Structure.Oriented.XStart' at the level
--   of 'Category's.
data XMrphSite (s :: Site) m where
  XDomain ::
       X (SomeObjectClass m)
    -> (forall x . Struct (ObjectClass m) x -> X (SomeMorphismSite From m x))
    -> XMrphSite From m
  XRange ::
       X (SomeObjectClass m)
    -> (forall y . Struct (ObjectClass m) y -> X (SomeMorphismSite To m y))
    -> XMrphSite To m

type instance Dual (XMrphSite s m) = XMrphSite (Dual s) (Op2 m)

instance Dualisable (XMrphSite To m) where
  toDual xmt@(XRange xo _) = XDomain (fmap toDual xo) (xsm' xmt) where
    xsm' :: XMrphSite To m
        -> Struct (ObjectClass (Op2 m)) x -> X (SomeMorphismSite From (Op2 m) x)
    xsm' (XRange _ xsm) xo' = fmap toDual $ xsm xo'

  fromDual xmf@(XDomain xo' _) = XRange (fmap fromDual xo') (xsm xmf) where
    xsm :: XMrphSite From (Op2 m)
        -> Struct (ObjectClass m) y -> X (SomeMorphismSite To m y)
    xsm (XDomain _ xsm') xo = fmap fromDual $ xsm' xo

--------------------------------------------------------------------------------
-- xSomeObjectClass -

-- | the underlying random variable for some object class.
xSomeObjectClass :: XMrphSite s m -> X (SomeObjectClass m)
xSomeObjectClass (XDomain xso _) = xso
xSomeObjectClass (XRange xso _) = xso

--------------------------------------------------------------------------------
-- xSomePathSiteMax -

-- | random variable of paths of 'Morphism's having maximal the given length. If during
--   the randomly build path no terminal respectively initial object class has reached
--   then the resulting path will have the given length.
--
--   It is the analogue to 'OAlg.Proposition.Structure.Oriented.xStartPathOrt' at the
--   level of 'Category's.
xSomePathSiteMax :: Morphism m
  => XMrphSite s m -> N -> Struct (ObjectClass m) x -> X (SomePathSite s m x)
xSomePathSiteMax xmf@(XDomain _ _) n d = pth xmf n d d (cOne d) where
  pth :: Morphism m
      => XMrphSite From m
      -> N -> Struct (ObjectClass m) x -> Struct (ObjectClass m) y
      -> Path m x y -> X (SomePathSite From m x)
  pth _ 0 _ _ fs                      = return $ SomePathDomain fs
  pth xd@(XDomain _ xmf) n d r fs = case xmf r of
    XEmpty -> return $ SomePathDomain fs
    xf     -> xf >>= \(SomeMorphismDomain f) -> pth xd (pred n) d (range f) (f :. fs)

xSomePathSiteMax xmt@(XRange _ _) n d
  = fmap fromDual $ xSomePathSiteMax (toDual xmt) n d

--------------------------------------------------------------------------------
-- xSomePathMax -

-- | derived random variable for some paths.
xSomePathMax :: Morphism m => XMrphSite s m -> N -> X (SomePath m)
xSomePathMax xmf@(XDomain xo _) n = do
  SomeObjectClass o <- xo
  pth <- xSomePathSiteMax xmf n o
  return $ somePath pth
xSomePathMax xmt@(XRange _ _) n = fmap fromDual $ xSomePathMax (toDual xmt) n

--------------------------------------------------------------------------------
-- adjOne -

-- | adjoining 'cOne' for empty random variables.
adjOne :: Category c => XMrphSite s c -> XMrphSite s c
adjOne xmf@(XDomain xo _) = XDomain xo (xsm' xmf) where
  xsm' :: Category c
       => XMrphSite From c
       -> Struct (ObjectClass c) x -> X (SomeMorphismSite From c x)
  xsm' (XDomain _ xsm) o = case xsm o of
    XEmpty -> return $ SomeMorphismDomain $ cOne o
    xm     -> xm
adjOne xmt@(XRange _ _) = fromDual $ adjOne $ toDual xmt

--------------------------------------------------------------------------------
-- xSomePathSite -

-- | constructing random variable for some path site.
xSomePathSite :: Category c
  => XMrphSite s c -> N -> Struct (ObjectClass c) x -> X (SomePathSite s c x)
xSomePathSite xm = xSomePathSiteMax (adjOne xm)

--------------------------------------------------------------------------------
-- xSomePath -

-- | constructing random variable for some path.
xSomePath :: Category c => XMrphSite s c -> N -> X (SomePath c)
xSomePath xm = xSomePathMax (adjOne xm)

--------------------------------------------------------------------------------
-- xCat -

-- | random variable for validating 'Category'.
xCat :: Category c => XMrphSite s c -> XCat c
xCat xm = XCat (xsm xm) (xsm3 xm) where
  xsm xm = do
    SomePath (f :. _) <- xSomePath xm 1
    return $ SomeMorphism f
    
  xsm3 xm = do
    SomePath (f :. g :. h :. _) <- xSomePath xm 3
    return $ SomeCmpb3 f g h

--------------------------------------------------------------------------------
-- XFnctMrphSite -

-- | random variable for 'Functorial' 'Category's.
data XFnctMrphSite s m where
  XFnctMrphSite ::
        XMrphSite s m
    -> (forall x . Struct (ObjectClass m) x -> X x)
    -> XFnctMrphSite s m

--------------------------------------------------------------------------------
-- xMrphSite -

-- | random variable for 'Morphism's for a given 'Site'.
xMrphSite :: XFnctMrphSite s m -> XMrphSite s m
xMrphSite (XFnctMrphSite xmd _) = xmd

--------------------------------------------------------------------------------
-- xFnct -

-- | random variable for 'Functorial' 'Category's.
xFnct :: (Category c, Transformable (ObjectClass c) Ent)
  => XFnctMrphSite s c -> XFnct c
xFnct xfd@(XFnctMrphSite xmd xox) = XFnct xse xsca where
  
  xse = do
    SomeObjectClass so <- xSomeObjectClass xmd
    xse' xfd xox (tau so) so
  xsca = do
    SomePath (f:.g:._) <- xSomePath xmd 2
    xsca' f g xox (tau (range f)) (tau (domain g)) (domain g)

  xse' :: p c
       -> (forall x . Struct (ObjectClass c) x -> X x)
       -> Struct Ent x
       -> Struct (ObjectClass c) x -> X (SomeEntity c)
  xse' _ xox Struct so = xox so >>= return . SomeEntity so

  xsca' :: c y z -> c x y
        -> (forall x . Struct (ObjectClass c) x -> X x)
        -> Struct Ent z -> Struct Ent x
        -> Struct (ObjectClass c) x -> X (SomeCmpbAppl c)
  xsca' f g xox Struct Struct so = xox so >>= return . SomeCmpbAppl f g 

--------------------------------------------------------------------------------
-- relFunctorialGOne -

relFunctorialGOne :: (FunctorialG t a b, EqExt b) => q t a b -> Struct (ObjectClass a) x -> Statement
relFunctorialGOne q s = amapG (cOne' (qa q) s) .=. cOne' (qb q) (tauG' (qt q) s) where

  qa :: forall q (t :: Type -> Type) (a :: Type -> Type -> Type) (b :: Type -> Type -> Type)
      . q t a b -> Proxy a
  qa _ = Proxy

  qb :: forall q (t :: Type -> Type) (a :: Type -> Type -> Type) (b :: Type -> Type -> Type)
      . q t a b -> Proxy b
  qb _ = Proxy

  qt :: forall q (t :: Type -> Type) (a :: Type -> Type -> Type) (b :: Type -> Type -> Type)
      . q t a b -> Proxy t
  qt _ = Proxy

--------------------------------------------------------------------------------
-- relFunctorialGCmp -

relFunctorialGCmp :: (FunctorialG t a b, EqExt b) => q t a b -> a y z -> a x y -> Statement
relFunctorialGCmp q f g = amapG' q (f . g) .=. (amapG' q f . amapG' q g)

--------------------------------------------------------------------------------
-- prpFunctorialG -

-- | validity according to 'FunctorialG'.
prpFunctorialG :: (FunctorialG t a b, EqExt b)
  => q t a b -> X (SomeObjectClass a) -> X (SomeCmpb2 a) -> Statement
prpFunctorialG q xo xfg = Prp "FunctorialG" :<=>:
  And [ Label "cOne" :<=>: Forall xo (\(SomeObjectClass s) -> relFunctorialGOne q s)
      , Label "." :<=>: Forall xfg (\(SomeCmpb2 f g) -> relFunctorialGCmp q f g)
      ] 
