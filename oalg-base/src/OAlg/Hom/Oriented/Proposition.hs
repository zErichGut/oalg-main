
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

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
    -- * Disjunctive Homomorphism
    prpHomDisjunctiveOriented
  , prpHomDisjOrtDual
  , prpHomDisjOrtVariant

    -- * Duality
  , prpSDualisableOriented

    -- * HomOrt
  , prpHomOrtOpEmpty
  )
  where

import Control.Monad

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Identity
import OAlg.Data.Proxy
import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented as O

import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- prpSDualisableOriented -

-- | validity according to 'SDualisableOriented'.
relSDualisableOriented :: SDualisableOriented s o
  => q o -> Struct s x -> Struct Ort x -> Struct Ort (o x) -> XOrt x -> Statement
relSDualisableOriented q s Struct Struct xx = Forall xx
    (\x -> And [ Label "1" :<=>: ((start $ tArw x) == (tPnt $ end x)) :?> Params ["x":=show x]
               , Label "2" :<=>: ((end $ tArw x) == (tPnt $ start x)) :?> Params ["x":=show x]
               ]
    )
  where
    tArw = sdlToDualArw q s
    tPnt = sdlToDualPnt q s


-- | validity according to 'SDualisableOriented'.
prpSDualisableOriented :: SDualisableOriented s o
  => q o -> Struct s x -> XOrt x -> Statement
prpSDualisableOriented q s xx = Prp "SDualisableOriented" :<=>:
  relSDualisableOriented q s sOrt (tau1 sOrt) xx where sOrt = tauOrt s


--------------------------------------------------------------------------------
-- prpHomDisjOrtDual -

relHomDisjOrtDual :: (HomDisjunctiveOriented s o h, Eq2 h)
  => q o h -> Struct s x -> Statement
relHomDisjOrtDual q s
  = And [ Label "1" :<=>: eq2 (fromDual . toDual) (cOne s) :?> Params []
        , Label "2" :<=>: eq2 (toDual . fromDual) (cOne (tau1 s)) :?> Params []
        ]
  where Contravariant2 toDual   = homOrtToDual' q s
        Contravariant2 fromDual = homOrtFromDual' q s

-- | validity according to 'HomDisjunctiveOriented' for (1.1) and (1.2).
prpHomDisjOrtDual :: (HomDisjunctiveOriented s o h, Eq2 h)
  => q s o h -> X (SomeObjectClass h) -> Statement
prpHomDisjOrtDual q xso = Prp "HomDisjOrtDual" :<=>: Forall xso
  (\(SomeObjectClass s) -> relHomDisjOrtDual (q' q) s
  )
  where q' :: forall q s (o :: Type -> Type) (h :: Type -> Type -> Type) . q s o h -> Proxy2 o h
        q' _ = Proxy2
        
--------------------------------------------------------------------------------
-- prpHomDisjOrtVariant -

relHomDisjOrtCovariant :: (HomDisjunctiveOriented s o h, Show2 h)
  => q o -> Struct s x -> Homomorphous Ort x y -> HomVariant Covariant h x y  -> x -> Statement
relHomDisjOrtCovariant _ _ (Struct:>:Struct) h  x = Label "Covariant" :<=>:
  And [ Label "1" :<=>: (start (amap h x) == pmap h (start x)) :?> Params ["h":= show2 h, "x":=show x]
      , Label "2" :<=>: (end (amap h x) == pmap h (end x)) :?> Params ["h":= show2 h, "x":=show x]
      ]

relHomDisjOrtVariant :: (HomDisjunctiveOriented s o h, Show2 h)
  => q o -> Either2 (HomVariant Contravariant h) (HomVariant Covariant h) x y
  -> Struct s x -> x -> Statement
relHomDisjOrtVariant q h s x = case h of
  Right2 hCov -> Label "Covariant" :<=>: relHomDisjOrtCovariant q s (tauHom (homomorphous h)) hCov x
  Left2 hCnt  -> Label "Contravariant" :<=>:
                   relHomDisjOrtVariant q (Right2 (homOrtToCovariant (q' q hCnt) s hCnt)) s x
  where q' :: forall q f (h :: Type -> Type -> Type) (o :: Type -> Type) x y
            . q o -> f h x y -> Proxy2 o h
        q' _ _ = Proxy2

-- | validity according to 'HomDisjunctiveOriented' for (2.1) and (2.2).
prpHomDisjOrtVariant :: (HomDisjunctiveOriented s o h, Show2 h)
  => q s o -> X (SomeApplication h) -> Statement
prpHomDisjOrtVariant q xsa = Prp "HomDisjOrtVariant" :<=>: Forall xsa
  (\(SomeApplication h x) -> relHomDisjOrtVariant q (toVariant2 h) (domain h) x
  )
  
--------------------------------------------------------------------------------
-- prpHomDisjunctiveOriented -

-- | validity according to 'HomDisjunctiveOriented'.
prpHomDisjunctiveOriented :: (HomDisjunctiveOriented s o h, Show2 h, Eq2 h)
  => q s o -> X (SomeObjectClass h) -> X (SomeApplication h) -> Statement
prpHomDisjunctiveOriented q xso xsa = Prp "HomDisjunctiveOriented" :<=>:
  And [ prpHomDisjOrtDual (q' q xso) xso
      , prpHomDisjOrtVariant q xsa
      ]
  where q' :: forall q s (o :: Type -> Type) h . q s o -> X (SomeObjectClass h) -> Proxy3 s o h
        q' _ _ = Proxy3

--------------------------------------------------------------------------------
--

{-
gg :: Id x -> Id (Op (Op x))
gg = error "nxi"

ff :: Struct OrtX x -> EqualExt (Id x) (Id (Op (Op x)))
ff Struct = EqualExt gg
-}

aa :: Struct Typ x -> Inv2 (->) (Id x) (Id (Op (Op x)))
aa = sdlRefl

bb :: Homomorphous s x y -> c x y -> Sub s c x y
bb (Struct:>:Struct) = Sub

cc :: Struct OrtX x -> Homomorphous OrtX (Id x) (Id (Op (Op x)))
cc = error "nyi"

dd :: Struct OrtX x -> Inv2 (->) (Id x) (Id (Op (Op x)))
dd s = aa (tau s)

ff :: Struct OrtX x -> Inv2 (Sub OrtX (->)) (Id x) (Id (Op (Op x)))
ff s = error "nyi" -- bb (cc s) $ aa (tau s)

hh :: Inv2 (Sub OrtX (->)) x y -> Inv2 EqualExt x y
hh = error "nyi"


instance SReflexiveG EqualExt OrtX Op Id where
  sdlRefl s = hh $ ff s

    
instance SDualisableG EqualExt OrtX Op Id where

instance TransformableGObjectClassRange Id OrtX EqualExt


instance SReflexiveG EqualExt OrtX Op Pnt
instance SDualisableG EqualExt OrtX Op Pnt

instance TransformableGObjectClassRange Pnt OrtX EqualExt
--------------------------------------------------------------------------------
-- prpHomOrtOpEmpty -

-- | validity of @'HomOrtOpEmpty' 'Ort'´@.
prpHomOrtOpEmpty :: Statement
prpHomOrtOpEmpty
  = And [ prpCategoryDisjunctive xo xfg
        , prpFunctorialG qId xo xfg
        , prpFunctorialG qPt xo xfg
        , prpHomDisjunctiveOriented qso xo xsa
        ] where
  
  qso = Proxy2 :: Proxy2 OrtX Op
  qId = Proxy3 :: Proxy3 Id (HomOrt OrtX Op (HomEmpty OrtX)) EqualExt
  qPt = Proxy3 :: Proxy3 Pnt (HomOrt OrtX Op (HomEmpty OrtX)) EqualExt
  
  xoSct :: X (SomeObjectClass (SDualityCategory OrtX Op (HomEmpty OrtX)))
  xoSct = xOneOf [ SomeObjectClass (Struct :: Struct OrtX OS)
                 , SomeObjectClass (Struct :: Struct OrtX N)
                 ]

  xo :: X (SomeObjectClass (HomOrt OrtX Op (HomEmpty OrtX)))
  xo = amap1 (\(SomeObjectClass s) -> SomeObjectClass s) xoSct

  xfg :: X (SomeCmpb2 (HomOrt OrtX Op (HomEmpty OrtX)))
  xfg = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (HomOrt f) (HomOrt g)) $ xSctSomeCmpb2 10 xoSct XEmpty

  xsa :: X (SomeApplication (HomOrt OrtX Op (HomEmpty OrtX)))
  xsa = join
      $ amap1
          (  (\(SomeMorphism m) -> xSomeAppl m)
           . (\(SomeCmpb2 f g) -> SomeMorphism (f . g))
          )
      $ xfg




{-
--------------------------------------------------------------------------------
-- XHomOrt -

-- | random variable to validate homomorphisms between 'Oriented' structures.
type XHomOrt h = XAppl h

--------------------------------------------------------------------------------
-- prpHomOrt -

-- | validity of homomorphisms between 'Oriented' for a given value in the domain.
relHomOrientedCovariant :: (HomOrientedCovariant h, Show2 h)
  => Homomorphous Ort x y -> h x y -> x -> Statement
relHomOrientedCovariant (Struct:>:Struct) h x
  = And [ Label "1" :<=>: (start (amap h x) == pmap h (start x)) :?> Params ["h":=show2 h,"x":=show x]
        , Label "2" :<=>: (end (amap h x) == pmap h (end x)) :?> Params ["h":=show2 h,"x":=show x]
        ]
-}





{-

--------------------------------------------------------------------------------
-- prpHomOrt1 -

-- | validity of homomorphisms between 'Oriented' structures based on the given values.
prpHomOrt1 :: (HomOrientedCovariant h, Show2 h) => h a b -> a -> Statement
prpHomOrt1 f x = Prp "HomOrt1" :<=>: relHomOrientedCovariant (tauHom (homomorphous f)) f x



-- | validity of homomorphisms between 'Oriented' structures based on the given
-- random variable.
prpHomOrt :: (Hom Ort h, Show2 h) => XHomOrt h -> Statement
prpHomOrt xfx = Prp "HomOrt"
  :<=>: Forall xfx (\(SomeApplication f x)
                    -> relHomOrientedCovariant (tauHom (homomorphous f)) f x
                   )

-- | validity of homomorphisms between 'Oriented' structures based on the given
-- random variable.
prpHomOrt' :: (Hom Ort h, Show2 h) => h a b -> XOrt a -> Statement
prpHomOrt' f xa = Label "prpHomOrt'" :<=>:
  Forall xa (relHomOrientedCovariant (tauHom (homomorphous f)) f)
  
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
-- prpSDualityOriented -

-- | validdity according to 'SDualityOriented'.
prpSDualityOriented :: SDualityOriented d s i o
  => d i o -> Struct s x
  -> X x -> X (o x)
  -> X (Point x) -> X (Point (o (o x)))
  -> Statement
prpSDualityOriented d s xx xx' xp xp'' = Prp "SDualityOriented" :<=>:
  And [ Label "5" :<=>: case (tauOrt s, tauOrt (sdlTau d s)) of
          (Struct,Struct) -> And [ Label "start" :<=>:
                                     ((start . sdlToDual d s) .=. (sdlToDualPnt d s . end))
                                 , Label "end" :<=>:
                                     ((end . sdlToDual d s) .=. (sdlToDualPnt d s . start))
                                 ]
            where (.=.) = prpExtensionalEqual xx
      , Label "6" :<=>: case (tauOrt s, tauOrt (sdlTau d s)) of
          (Struct,Struct) -> And [ Label "start" :<=>:
                                     ((start . sdlFromDual d s) .=. (sdlFromDualPnt d s . end))
                                 , Label "end" :<=>:
                                     ((end . sdlFromDual d s) .=. (sdlFromDualPnt d s . start))
                                 ] 
            where (.=.) = prpExtensionalEqual xx'
      , Label "3" :<=>: case (tauOrt s,tauOrt s''') of
          (Struct,Struct) -> ((sdlToDualPnt d s'' . pmap r) .=. (pmap r'' . sdlToDualPnt d s))
            where (.=.) = prpExtensionalEqual xp
      , Label "2" :<=>: case (tauOrt s, tauOrt s'') of
          (Struct,Struct) -> ((sdlToDualPnt d s' . sdlToDualPnt d s) .=. pmap r)
            where (.=.) = prpExtensionalEqual xp
      , Label "1" :<=>: case tauOrt s of
          Struct -> ((sdlFromDualPnt d s . sdlToDualPnt d s) .=. id)
            where (.=.) = prpExtensionalEqual xp
      , Label "4" :<=>: case (tauOrt s, tauOrt s'') of
          (Struct,Struct) -> ((sdlFromDualPnt d s . sdlFromDualPnt d s') .=. pmap r')
            where (.=.) = prpExtensionalEqual xp''
      ]
  where s'         = sdlTau d s
        s''        = sdlTau d s'
        s'''       = sdlTau d s''
        Inv2 r r' = sdlRefl d s
        Inv2 r'' _ = sdlRefl d s'
        
--------------------------------------------------------------------------------
-- prpHomOpOrt -

-- | validity of @'HomOp' 'Ort'@ according to 'HomOriented' on @'Orientation' 'Symbol'@.
prpHomOpOrt :: Statement
prpHomOpOrt = Prp "HomOpOrt"
  :<=>: prpHomOrt xa where

    xo = xOrtOrnt xSymbol
    -- xs = xStartOrnt xSymbol

    -- xpth n = xNB 0 n >>= xosPath xs
    
    xa :: XHomOrt (HomOp Ort)
    xa = join $ xOneOf [ fmap (SomeApplication FromOpOp . Op . Op) xo 
                       -- , fmap (SomeApplication OpPath . Op) $ xpth 10
                       -- , fmap (SomeApplication Opposite . Op) xo
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
-- prpOpDualityOrtOS -

-- | validity of 'OpDuality' according to 'SDuality' and 'SDualityOriented' on 'OS'.
prpOpDualityOrtOS :: Statement
prpOpDualityOrtOS = Prp "OpDualityOrtOS" :<=>:
  And [ prpSDuality dOp sOrt xos xos''
      , prpSDualityOriented dOp sOrt xos xos' xs xs''
      ]
  where dOp   = OpDuality :: OpDuality (IsoOp Ort) Op
        sOrt  = Struct :: Struct Ort OS
        xs    = xSymbol
        xs''  = xs
        xos   = xOrtOrnt xs
        xos'  = amap1 Op xos
        xos'' = amap1 Op xos'
  
--------------------------------------------------------------------------------
-- xIsoOpOrtFrom -

-- | random variale of @'IsoOp' 'Ort'@.
xIsoOpOrtFrom :: XFnctMrphSite From (IsoOp Ort)
xIsoOpOrtFrom = XFnctMrphSite (XDomain xss xsdm) xox where
{-  
  domOpPath :: Struct Ort (Op (O.Path OS))
  domOpPath = Struct

  domOpPathInv :: Struct Ort (O.Path (Op OS))
  domOpPathInv = Struct

  domOpOS :: Struct Ort (Op OS)
  domOpOS = Struct
-}
  domOpOpOS :: Struct Ort (Op (Op OS))
  domOpOpOS = Struct
  
  domOS :: Struct Ort OS
  domOS = Struct

  xOS = xOrtOrnt xSymbol
  
  xox d =     xdomOS d -- <|> xdomOpOS d
          -- <|> xdomOpPath d <|> xdomOpPathInv d
          <|> xdomOpOpOS d

  xdomOS :: Struct Ort x -> X x
  xdomOS d = case testEquality d domOS of
    Just Refl -> xOS
    Nothing   -> XEmpty
{-
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
-}
  xdomOpOpOS :: Struct Ort x -> X x
  xdomOpOpOS d = case testEquality d domOpOpOS of
    Just Refl -> fmap (Op . Op) xOS
    Nothing   -> XEmpty
  
  xss = xOneOf [ SomeObjectClass domOS
               -- , SomeObjectClass domOpPath
               -- , SomeObjectClass domOpPathInv
               -- , SomeObjectClass domOpOS
               , SomeObjectClass domOpOpOS
               ]

  xsdm d =    xsdmFromOpOp d <|> xsdmToOpOp d
          -- <|> xsdmOpPath d <|> xsdmOpPathInv d
          -- <|> xsdmOpposite d <|> xsdmOppositeInv d
          
  xsdmFromOpOp :: Struct Ort x -> X (SomeMorphismSite From (IsoOp Ort) x)
  xsdmFromOpOp d = case testEquality d domOpOpOS of
    Just Refl -> return $ SomeMorphismDomain (f d)
    _         -> XEmpty

  xsdmToOpOp :: Struct Ort x -> X (SomeMorphismSite From (IsoOp Ort) x)
  xsdmToOpOp d = case testEquality d domOS of
    Just Refl -> return $ SomeMorphismDomain (f' d)
    _         -> XEmpty
{-
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
-}

  f' :: Struct Ort a -> IsoOp Ort a (Op (Op a))
  f' Struct = invert2 isoFromOpOpOrt

  f :: a ~ OS => Struct Ort (Op (Op a)) -> IsoOp Ort (Op (Op a)) a
  f Struct = isoFromOpOpOrt
{-
  p :: a ~ OS => Struct Ort (Op (O.Path a)) -> IsoOp Ort (Op (O.Path a)) (O.Path (Op a))
  p Struct = make (OpPath :. IdPath Struct)

  p' :: a ~ OS => Struct Ort (O.Path (Op a)) -> IsoOp Ort (O.Path (Op a)) (Op (O.Path a))
  p' Struct = make (OpPathInv :. IdPath Struct)

  o :: a ~ OS => Struct Ort (Op a) -> IsoOp Ort (Op a) a
  o Struct = make (Opposite :. IdPath Struct)

  o' :: a ~ OS => Struct Ort a -> IsoOp Ort a (Op a)
  o' Struct = make (OppositeInv :. IdPath Struct)
-}



-}
