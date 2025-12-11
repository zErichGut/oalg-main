
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      : OAlg.Structure.Oriented.Proposition
-- Description : propositions on multiplicative structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Propositions on 'Multiplicative' structures.
module OAlg.Structure.Multiplicative.Proposition
  (
    -- * Multiplicative
    prpMlt, XMlt(..)
  , Endo(..), Mltp2(..), Mltp3(..)
  , prpMlt1, prpMlt2, prpMlt2_1, prpMlt2_2, prpMlt3, prpMlt4, prpMlt5

    -- * Duality
  , coXMlt

    -- * X
  , MltX
  , XStandardMlt(..)
  , xMlt, xMltp2, xMltp3
  , xoMlt
  
    -- * Oriented Direction
  -- , xodMlt, xodEndo, xodMltp2, xodMltp3
  
    -- ** Total
  , xMltTtl

    -- ** Orientation
  , xMltOrnt
  
  )
  where

import Control.Monad
import Control.Applicative

import Data.Kind

import OAlg.Prelude

import OAlg.Data.Singleton
import OAlg.Data.Symbol

import OAlg.Structure.Exception
import OAlg.Structure.Oriented

import OAlg.Structure.Multiplicative.Definition

--------------------------------------------------------------------------------
-- Endo -

-- | predicate for endos.
newtype Endo q = Endo q deriving (Show,Eq,Ord)

instance Oriented q => Validable (Endo q) where
  valid (Endo a) = valid a && (start a .==. end a)

--------------------------------------------------------------------------------
-- fromEndo -

-- | deconstruction of a 'Endo'.
fromEndo :: Endo q -> q
fromEndo (Endo f) = f

--------------------------------------------------------------------------------
-- Mltp2 -

-- | predicate for two multiplicable factors.
data Mltp2 c = Mltp2 c c deriving (Show,Eq,Ord)

pthMltp2 :: Oriented c => Mltp2 c -> Path c
pthMltp2 (Mltp2 f g) = Path (start g) [f,g]

instance Oriented c => Validable (Mltp2 c) where
  valid = valid . pthMltp2

type instance Dual (Mltp2 c) = Mltp2 (Op c)

instance Oriented c => Dualisable (Mltp2 c) where
  toDual fg = Mltp2 f' g' where Path _ [f',g'] = toDual (pthMltp2 fg)
  fromDual fg' = Mltp2 f g where Path _ [f,g] = fromDual (pthMltp2 fg')
  
--------------------------------------------------------------------------------
-- Mltp3 -

-- | predicate for three multiplicable factors.
data Mltp3 c = Mltp3 c c c deriving (Show,Eq,Ord)

pthMltp3 :: Oriented c => Mltp3 c -> Path c
pthMltp3 (Mltp3 f g h) = Path (start h) [f,g,h]

instance Oriented c => Validable (Mltp3 c) where
  valid = valid . pthMltp3
  
type instance Dual (Mltp3 c) = Mltp3 (Op c)

instance Oriented c => Dualisable (Mltp3 c) where
  toDual fgh    = Mltp3 f' g' h' where Path _ [f',g',h'] = toDual (pthMltp3 fgh)      
  fromDual fgh' = Mltp3 f g h where Path _ [f,g,h] = fromDual (pthMltp3 fgh')


--------------------------------------------------------------------------------
-- prpMlt1 -

-- | validity of 'one' according to "OAlg.Structure.Multiplicative.Definition#Mlt1".
prpMlt1 :: Multiplicative c => p c -> X (Point c) -> Statement
prpMlt1 s xp = Prp "Mlt1"
  :<=>: Forall xp (\p -> (orientation (one' s p) == p :> p) :?> Params ["p" := show p])

--------------------------------------------------------------------------------
-- prpMlt2_1 -

-- | validity of '*' for two multiplicable factors according to
--   "OAlg.Structure.Multiplicative.Definition#Mlt2_1".
prpMlt2_1 :: Multiplicative c => Mltp2 c -> Statement
prpMlt2_1 m@(Mltp2 f g) = Prp "Mlt2_1"
  :<=>: And [ valid fg
            , Label "start" :<=>: (start fg == start g) :?> prms
            , Label "end" :<=>: (end fg == end f) :?> prms
            ]
  where fg = f*g
        prms = Params ["m":=show m]

--------------------------------------------------------------------------------
-- prpMlt2_2 -

-- | validity of '*' for two not multiplicable factors according to
--   "OAlg.Structure.Multiplicative.Definition#Mlt2_2".
prpMlt2_2 :: Multiplicative c => c -> c -> Statement
prpMlt2_2 f g = Prp "Mlt2_2"
  :<=>: And [ Not vfg `Catch` someException SValid 
            , vfg `Catch` nmp
            ]
  where vfg = valid (f*g)
        nmp NotMultiplicable = SValid
        nmp _                = SInvalid
        
--------------------------------------------------------------------------------
-- prpMlt2 -

-- | validity of '*' according to "OAlg.Structure.Multiplicative.Definition#Mlt2".
prpMlt2 :: Multiplicative c => X (c,c) -> Statement
prpMlt2 xfg = Prp "Mlt2"
  :<=>:  Forall xfg (\(f,g)
                     -> let fg = Mltp2 f g
                         in And [ valid fg       |~> prpMlt2_1 fg
                                , Not (valid fg) |~> prpMlt2_2 f g
                                ]
                    )

--------------------------------------------------------------------------------
-- prpMlt3 -

-- | validity according to "OAlg.Structure.Multiplicative.Definition#Mlt3".
prpMlt3 :: Multiplicative c => X c -> Statement
prpMlt3 xa = Prp "Mlt3"
  :<=>: Forall xa (\f -> And [ (one (end f) * f == f) :?> prm f
                             , (f * one (start f) == f) :?> prm f
                             ]
                  )
  where prm f = Params ["f":=show f]

--------------------------------------------------------------------------------
-- prpMlt4 -

-- | validity according to "OAlg.Structure.Multiplicative.Definition#Mlt4".
prpMlt4 :: Multiplicative c => X (Mltp3 c) -> Statement
prpMlt4 xfgh = Prp "Mlt4"
  :<=>: Forall xfgh
          (\m@(Mltp3 f g h ) -> ((f * g) * h == f * (g * h)) :?> Params ["m":=show m])


--------------------------------------------------------------------------------
-- prpMlt5 -

-- | validity of 'npower' according to "OAlg.Structure.Multiplicative.Definition#Mlt5".
--
-- __Note__ As the multiplication can by very costly the random variable for @t'X' t'N'@
-- - which serves to check "OAlg.Structure.Multiplicative.Definition#Mlt5_2" - has to be chosen
-- carefully.
prpMlt5 :: Multiplicative c => X N -> X c -> X (Endo c) -> Statement
prpMlt5 xn xf xfe = Prp "Mlt5"
  :<=>: Forall xnf (\(n,f) ->
                      And [ Label "5.1"
                            :<=>: (npower f 1 == f) :?> Params ["f":=show f]
                          , Label "5.2"
                            :<=>: isEndo f :?> MInvalid
                              |~> And [ (npower f 0 == one (start f))
                                        :?> Params ["f":=show f]
                                      , (npower f (succ n) == f * npower f n)
                                        :?> Params ["f":=show f,"n":=show n]
                                      ]
                          ]
                   )
  where xf' = join $ xOneOfW [(10,fmap fromEndo xfe),(1,xf)]
        xnf = xTupple2 xn xf'

--------------------------------------------------------------------------------
-- XMlt -

-- | random variable for 'Multiplicative' structures.
--
--   __Note__ As the multiplication could by costly, it is recommended to
--   use a bounded random variable for 'xMltN' which serves to validate
--   'npower'.
data XMlt c = XMlt
  { xMltN      :: X N
  , xMltPoint  :: X (Point c)
  , xMltFactor :: X c
  , xMltEndo   :: X (Endo c)
  , xMltMltp2  :: X (Mltp2 c)
  , xMltMltp3  :: X (Mltp3 c)
  }

--------------------------------------------------------------------------------
-- XMlt - Validable -

instance Oriented c => Validable (XMlt c) where
  valid (XMlt xn xp xc xe xc2 xc3)
    = And [ valid xn
          , valid xp
          , valid xc
          , valid xe
          , valid xc2
          , valid xc3
          ]

--------------------------------------------------------------------------------
-- XMlt - Dualisable -

type instance Dual (XMlt c) = XMlt (Op c)

-- | the dual random variable with inverse 'coXMltInv'.
coXMlt :: XMlt c -> Dual (XMlt c)
coXMlt (XMlt xn xp xf xe xf2 xf3) = XMlt xn xp xf' xe' xf2' xf3' where
  xf'  = fmap Op xf
  xe'  = fmap (\(Endo e) -> Endo (Op e)) xe
  xf2' = fmap (\(Mltp2 f g) -> Mltp2 (Op g) (Op f)) xf2
  xf3' = fmap (\(Mltp3 f g h) -> Mltp3 (Op h) (Op g) (Op f)) xf3


-- | from the bidual.
xMltFromOpOp :: XMlt (Op (Op c)) -> XMlt c
xMltFromOpOp (XMlt xn xp xf xe xf2 xf3) = XMlt xn xp xf' xe' xf2' xf3' where
  xf'  = fmap fromOpOp xf
  xe'  = fmap (\(Endo e) -> Endo $ fromOpOp e) xe
  xf2' = fmap (\(Mltp2 f g) -> Mltp2 (fromOpOp f) (fromOpOp g)) xf2
  xf3' = fmap (\(Mltp3 f g h) -> Mltp3 (fromOpOp f) (fromOpOp g) (fromOpOp h)) xf3

-- | from the dual with inverse 'coXMlt'.
coXMltInv :: Dual (XMlt c) -> XMlt c
coXMltInv = xMltFromOpOp . coXMlt

--------------------------------------------------------------------------------
-- MltX -

-- | index for 'Multiplicative' structures with a 'XStandardMlt'.
data MltX

type instance Structure MltX x = (Multiplicative x, XStandardMlt x)

instance TransformableG Op MltX MltX where tauG Struct = Struct
instance TransformableOp MltX

instance XStandardMlt x => XStandardMlt (Op x) where
  xStandardMlt = coXMlt xStandardMlt

instance Transformable MltX Ort where tau Struct = Struct
instance TransformableOrt MltX

instance Transformable MltX Mlt where tau Struct = Struct
instance TransformableMlt MltX

instance Transformable MltX Typ where tau Struct = Struct

instance Transformable MltX Type where tau _ = Struct
instance TransformableType MltX

instance XStandardMlt c => XStandardMlt (Id c) where
  xStandardMlt = XMlt xn xp x' xe' x2' x3' where
    XMlt xn xp x xe x2 x3 = xStandardMlt
    x'  = amap1 Id x
    xe' = amap1 (\(Endo f) -> Endo (Id f)) xe
    x2' = amap1 (\(Mltp2 f g) -> Mltp2 (Id f) (Id g)) x2
    x3' = amap1 (\(Mltp3 f g h) -> Mltp3 (Id f) (Id g) (Id h)) x3

--------------------------------------------------------------------------------
-- XStandarMlt -

-- | standard random variable for 'Multiplicative' structures.
class XStandardMlt c where
  xStandardMlt :: XMlt c
  
--------------------------------------------------------------------------------
-- prpMlt -

-- | validity of the 'Multiplicative' structure of @__c__@.
prpMlt :: Multiplicative c => XMlt c -> Statement
prpMlt (XMlt xn xp xf xfe xf2 xf3) = Prp "Mlt"
  :<=>: And [ prpMlt1 xf xp
            , prpMlt2 xfg
            , prpMlt3 xf
            , prpMlt4 xf3
            , prpMlt5 xn xf xfe
            ]
  where xfg = xTupple2 xf xf <|> fmap (\(Mltp2 f g) -> (f,g)) xf2

--------------------------------------------------------------------------------
-- xMltTtl -

-- | random variable for total 'Multiplicative' structures.
xMltTtl :: Singleton (Point c) => X N -> X c -> XMlt c
xMltTtl xn xf = XMlt xn (return unit) xf xfe xf2 xf3
  where xfe = fmap Endo xf -- as the multiplication is total.
        xf2 = fmap (uncurry Mltp2) (xTupple2 xf xf)
        xf3 = fmap (uncurry3 Mltp3) (xTupple3 xf xf xf)

instance XStandardMlt N where
  xStandardMlt = xMltTtl xn xStandard where
    xn = xNB 0 20

instance XStandardMlt Z where
  xStandardMlt = xMltTtl xn xStandard where
    xn = xNB 0 20

instance XStandardMlt Q where
  xStandardMlt = xMltTtl xn xStandard where
    xn = xNB 0 20

--------------------------------------------------------------------------------
-- xMltp2 -

-- | random variable of two multiplicable factors.
xMltp2 :: Multiplicative c => XOrtSite d c -> X (Mltp2 c)
xMltp2 xa = do
  Path _ [f,g] <- xosPath xa 2
  return (Mltp2 f g)

--------------------------------------------------------------------------------
-- xMltp3 -

-- | random variable of three multiplicable factors.
xMltp3 :: Multiplicative c => XOrtSite d c -> X (Mltp3 c)
xMltp3 xa = do
  Path _ [f,g,h] <- xosPath xa 3
  return (Mltp3 f g h)

--------------------------------------------------------------------------------
-- xMlt -

-- | random variable for 'Multiplicative' structures.
xMlt :: Multiplicative c => XOrtSite d c -> X N -> X (Endo c) -> XMlt c
xMlt xs xn xfe = XMlt xn xp xf xfe xf2 xf3 where
  xp  = xosPoint xs
  xf  = xosOrt xs
  xf2 = xMltp2 xs
  xf3 = xMltp3 xs

--------------------------------------------------------------------------------
-- xoMlt -

-- | the induced random variable for multiplicable structures.
xoMlt :: Multiplicative c => X N -> XOrtOrientation c -> XMlt c
xoMlt xn xo = xMlt (xoFrom xo) xn xe where
  xe = do
    p <- xoPoint xo
    e <- xoArrow xo (p:>p)
    return (Endo e)

--------------------------------------------------------------------------------
-- xMltOrnt -

-- | random variable for the 'Multiplicative' structure of @'Orientation' p@.
xMltOrnt :: Entity p => X N -> X p -> XMlt (Orientation p)
xMltOrnt xn xp = xoMlt xn (xoOrnt xp)

dst :: Int -> IO ()
dst n = getOmega >>= putDistribution n xx where
  xo = xMltOrnt (xNB 0 10) xSymbol
  xx = xMltMltp3 xo

instance (Entity p, XStandard p) => XStandardMlt (Orientation p) where
  xStandardMlt = xMltOrnt xn xStandard where
    xn = xNB 0 1000
