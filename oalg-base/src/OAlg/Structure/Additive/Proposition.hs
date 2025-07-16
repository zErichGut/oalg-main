
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : OAlg.Structure.Additive.Proposition
-- Description : propositions on additive structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions on 'Additive' structures.
module OAlg.Structure.Additive.Proposition
  (
    -- * Additive
    relIsZero
  , prpAdd
  , prpAdd1, prpAdd2, prpAdd2_1, prpAdd2_2
  , prpAdd3, prpAdd4, prpAdd5, prpAdd6

    -- * Abelian
  , prpAbl, prpAbl1, prpAbl2
  , prpAbl3, prpAbl3_1, prpAbl3_2
  , prpAbl4, prpAbl5

    -- * X
    -- ** Additive
  , XAdd(..), Adbl2(..), Adbl3(..)
  , XStandardAdd(..)

    -- ** Abelian
  , XAbl(..)

    -- ** Total
  , xAddTtl

    -- ** Direction
  , xoAdd, xoRoot, xoAdbl2, xoAdbl3
  , xoAbl, xoFbr

    -- ** Orientation
  , xAddOrnt

     -- ** Stalk
  , xAddStalk, xStalkAdbl2, xStalkAdbl3

  )
  where

import Control.Monad
import Control.Applicative

import OAlg.Prelude

import OAlg.Data.Singleton
import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Fibred.Oriented

import OAlg.Structure.Additive.Definition

--------------------------------------------------------------------------------
-- relIsZero -

-- | relation of 'isZero'.
relIsZero :: Additive a => a -> Statement
relIsZero a = Label "isZero" :<=>: isZero a :?> Params ["a":=show a]

--------------------------------------------------------------------------------
-- prpAdd1 -

-- | validtiy of 'root' according to "OAlg.Structure.Additive.Definition#Add1".
prpAdd1 :: Additive a => p a -> X (Root a) -> Statement
prpAdd1 s xr = Prp "Add1"
  :<=>: Forall xr (\r -> (root (zero' s r) == r) :?> Params [])

--------------------------------------------------------------------------------
-- Adbl2 -

-- | predicate for two addable summands.
data Adbl2 a = Adbl2 a a deriving (Show,Eq,Ord)

shfAdbl2 :: Fibred a => Adbl2 a -> Sheaf a
shfAdbl2 (Adbl2 a b) = Sheaf (root a) [a,b]

instance Fibred a => Validable (Adbl2 a) where
  valid = valid . shfAdbl2

type instance Dual (Adbl2 a) = Adbl2 (Op a)

instance FibredOriented a => Dualisable (Adbl2 a) where
  toDual ab = case toDual (shfAdbl2 ab) of
    Sheaf _ [a',b'] -> Adbl2 a' b'
    _               -> error implementation

  fromDual ab' = case fromDual (shfAdbl2 ab') of
    Sheaf _ [a,b] -> Adbl2 a b
    _             -> error implementation
  

--------------------------------------------------------------------------------
-- Adbl3 -

-- | predicate for three addable summands.
data Adbl3 a = Adbl3 a a a deriving (Show,Eq,Ord)

shfAdbl3 :: Fibred a => Adbl3 a -> Sheaf a
shfAdbl3 (Adbl3 a b c) = Sheaf (root a) [a,b,c]

instance Fibred a => Validable (Adbl3 a) where
  valid = valid . shfAdbl3

type instance Dual (Adbl3 a) = Adbl3 (Op a)

instance FibredOriented a => Dualisable (Adbl3 a) where
  toDual abc = case toDual (shfAdbl3 abc) of
    Sheaf _ [a',b',c'] -> Adbl3 a' b' c'
    _                  -> error implementation
  fromDual abc' = case fromDual (shfAdbl3 abc') of
    Sheaf _ [a,b,c] -> Adbl3 a b c
    _               -> error implementation

--------------------------------------------------------------------------------
-- prpAdd2_1 -

-- | validity of '+' for two addable summands according to
--   "OAlg.Structure.Additive.Definition#Add2_1".
prpAdd2_1 :: Additive a => Adbl2 a -> Statement
prpAdd2_1 a@(Adbl2 f g) = Prp "Add2_1"
  :<=>: And [ valid fg
            , (root fg == root f):?>Params ["a":=show a]
            ]
  where fg = f + g


--------------------------------------------------------------------------------
-- prpAdd2_2 -

-- | validity of '+' for two not addable summands according to
--   "OAlg.Structure.Additive.Definition#Add2_2".
prpAdd2_2 :: Additive a => a -> a -> Statement
prpAdd2_2 f g = Prp "Add2_2"
  :<=>: And [ Not vfg `Catch` someException SValid
            , vfg `Catch` nab
            ]
  where vfg = valid (f + g)
        nab NotAddable = SValid
        nab _          = SInvalid
        
--------------------------------------------------------------------------------
-- prpAdd2 -

-- | validtiy of two summands according to "OAlg.Structure.Additive.Definition#Add2".
prpAdd2 :: Additive a => X (a,a) -> Statement
prpAdd2 xfg = Prp "Add2"
  :<=>: Forall xfg (\(f,g)
                    -> let fg = Adbl2 f g
                        in And [ valid fg       |~> prpAdd2_1 fg
                               , Not (valid fg) |~> prpAdd2_2 f g
                               ]
                   )

--------------------------------------------------------------------------------
-- prpAdd3 -

-- | validtiy of two adable summands according to "OAlg.Structure.Additive.Definition#Add3".
prpAdd3 :: Additive a => X (Adbl2 a) -> Statement
prpAdd3 xfg = Prp "Add3"
  :<=>: Forall xfg (\a@(Adbl2 f g) -> (f + g == g + f):?> Params ["a":=show a])

--------------------------------------------------------------------------------
-- prpAdd4 -

-- | validtiy according to "OAlg.Structure.Additive.Definition#Add4".
prpAdd4 :: Additive a => X a -> Statement
prpAdd4 xa = Prp "Add4"
  :<=>: Forall xa (\f -> (f + zero (root f) == f):?>Params ["f":=show f])

--------------------------------------------------------------------------------
-- prpAdd5 -

-- | validtiy of three adable summands according to "OAlg.Structure.Additive.Definition#Add5".
prpAdd5 :: Additive a => X (Adbl3 a) -> Statement
prpAdd5 xfgh = Prp "Add5"
  :<=>: Forall xfgh (\a@(Adbl3 f g h)
                     -> ((f + g) + h == f + (g + h))
                        :?> Params ["a":=show a]
                    )

--------------------------------------------------------------------------------
-- prpAdd6 -

-- | validity of 'ntimes' according to "OAlg.Structure.Additive.Definition#Add6".
prpAdd6 :: Additive a => X N -> X a -> Statement
prpAdd6 xn xa = Prp "Add6"
  :<=>: Forall xnf (\(n,f)
                    -> And [ (ntimes 0 f == zero (root f)):?> Params ["f":=show f]
                           , (ntimes (n+1) f == f + ntimes n f)
                             :?> Params ["n":=show n,"f":=show f]
                           ]
                   )
  where xnf = xTupple2 xn xa

--------------------------------------------------------------------------------
-- XAdd -

-- | random variable for validating 'Additive' structures.
data XAdd a = XAdd (X N) (X (Root a)) (X a) (X (Adbl2 a)) (X (Adbl3 a))

instance Additive a => Validable (XAdd a) where
  valid (XAdd xn xr xa xa2 xa3)
    = And [ valid xn
          , valid xr
          , valid xa
          , valid xa2
          , valid xa3
          ]

--------------------------------------------------------------------------------
-- XStandardAdd -

-- | standard random variable for 'Additive' structures.
class XStandardAdd a where
  xStandardAdd :: XAdd a

instance (FibredOriented x, XStandardAdd x) => XStandardAdd (Op x) where
  xStandardAdd = XAdd xn xr' xa' xa2' xa3' where
    XAdd xn xr xa xa2 xa3 = xStandardAdd
    xr' = xr
    xa'  = amap1 Op xa
    xa2' = amap1 (\(Adbl2 a b) -> Adbl2 (Op a) (Op b)) xa2
    xa3' = amap1 (\(Adbl3 a b c) -> Adbl3 (Op a) (Op b) (Op c)) xa3
  

--------------------------------------------------------------------------------
-- prpAdd -

-- | validity of the 'Additive' structure of @__a__@.
--
-- __Note__ For a good choice of @'X' 'N'@ see the note of 'prpAdd6'.
prpAdd :: Additive a => XAdd a -> Statement
prpAdd (XAdd xn xr xa xa2 xa3) = Prp "Add"
  :<=>: And [ prpAdd1 xa xr
            , prpAdd2 xfg
            , prpAdd3 xa2
            , prpAdd4 xa
            , prpAdd5 xa3
            , prpAdd6 xn xa
            ]
  where xfg = xTupple2 xa xa <|> fmap (\(Adbl2 f g) -> (f,g)) xa2


--------------------------------------------------------------------------------
-- xAddTtl -

-- | random variable for total 'Additive' structures.
xAddTtl :: Singleton (Root a) => X N -> X a -> XAdd a
xAddTtl xn xa = XAdd xn xr xa xa2 xa3 where
  xr  = return unit
  xa2 = fmap (uncurry Adbl2) $ xTupple2 xa xa
  xa3 = fmap (uncurry3 Adbl3) $ xTupple3 xa xa xa

instance XStandardAdd N where
  xStandardAdd = xAddTtl xn xStandard where
    xn = xNB 0 1000

instance XStandardAdd Z where
  xStandardAdd = xAddTtl xn xStandard where
    xn = xNB 0 1000

instance XStandardAdd Q where
  xStandardAdd = xAddTtl xn xStandard where
    xn = xNB 0 1000

--------------------------------------------------------------------------------
-- xStalkAdbl2 -

-- | random variable of two addable summands rooted at the given root.
xStalkAdbl2 :: Additive a => XStalk a -> Root a -> X (Adbl2 a)
xStalkAdbl2 xs r = do
  Sheaf _ [a,b] <- xSheafRoot xs 2 r
  return $ Adbl2 a b

--------------------------------------------------------------------------------
-- xStalkAdbl3 -

-- | random variable of three addable summands rooted in the given root.
xStalkAdbl3 :: Additive a => XStalk a -> Root a -> X (Adbl3 a)
xStalkAdbl3 xs r = do
  Sheaf _ [a,b,c] <- xSheafRoot xs 3 r
  return $ Adbl3 a b c

--------------------------------------------------------------------------------
-- xAddStalk -

-- | random variable for 'Additive' structure.
xAddStalk :: Additive a => XStalk a -> X N -> XAdd a
xAddStalk xs@(XStalk xr _) xn = XAdd xn xr xa xa2 xa3 where
  xa  = do
    Sheaf _ [s] <- xSheaf xs 1
    return s
  xa2 = xr >>= xStalkAdbl2 xs
  xa3 = xr >>= xStalkAdbl3 xs


--------------------------------------------------------------------------------
-- xAddOrnt -

-- | random variable for the 'Additive' structure of @'Orientation' __p__@.
xAddOrnt :: Entity p => X N -> X p -> XAdd (Orientation p)
xAddOrnt xn xp = xAddStalk (xStalkOrnt xp) xn

instance (Entity p, XStandard p) => XStandardAdd (Orientation p) where
  xStandardAdd = xAddOrnt xn xStandard where
    xn = xNB 0 1000

--------------------------------------------------------------------------------
-- prpAbl1 -

-- | validity according to "OAlg.Structure.Additive.Definition#Abl1".
prpAbl1 :: Abelian a => X a -> Statement
prpAbl1 xf = Prp "Abl1"
  :<=>: Forall xf (\f -> (root (negate f) == root f) :?> Params ["f":=show f]) 

--------------------------------------------------------------------------------
-- prpAbl2 -

-- | validity according to "OAlg.Structure.Additive.Definition#Abl2".
prpAbl2 :: Abelian a => X a -> Statement
prpAbl2 xf = Prp "Abl2"
  :<=>: Forall xf (\f -> (f + negate f == zero (root f)):?> Params ["f":=show f])

--------------------------------------------------------------------------------
-- prpAbl3_1 -

-- | validity of '-' for two addable summands according to
--   "OAlg.Structure.Additive.Definition#Abl3_1".
prpAbl3_1 :: Abelian a => Adbl2 a -> Statement
prpAbl3_1 a@(Adbl2 f g) = Prp "Adbl3_1"
  :<=>: And [ valid fg
            , (root fg == root f):?> Params ["a":=show a]
            ]
  where fg = f - g

--------------------------------------------------------------------------------
-- prpAbl3_2 -

-- | validity of '-' for two not addable summands according to
--   "OAlg.Structure.Additive.Definition#Abl3_2".
prpAbl3_2 :: Abelian a => a -> a -> Statement
prpAbl3_2 f g = Prp "Abl3_2"
  :<=>: And [ Not vfg `Catch` someException SValid
            , vfg `Catch` nab
            ]
  where vfg = valid (f - g)
        nab NotAddable = SValid
        nab _          = SInvalid

--------------------------------------------------------------------------------
-- prpAbl3 -

-- | validity of two summands according to "OAlg.Structure.Additive.Definition#Abl3".
prpAbl3 :: Abelian a => X (a,a) -> Statement
prpAbl3 xfg = Prp "Abl3"
  :<=>: Forall xfg (\(f,g)
                    -> let fg = Adbl2 f g
                       in And [ valid fg       |~> prpAbl3_1 fg
                              , Not (valid fg) |~> prpAbl3_2 f g
                              ]
                   )

--------------------------------------------------------------------------------
-- prpAbl4 -

-- | validity of two summands according to "OAlg.Structure.Additive.Definition#Abl4".
prpAbl4 :: Abelian a => X (Adbl2 a) -> Statement
prpAbl4 xfg = Prp "Abl4"
  :<=>: Forall xfg (\a@(Adbl2 f g)
                    -> (f - g == f + negate g):?> Params ["a":=show a]
                   )

--------------------------------------------------------------------------------
-- prpAbl5 -

-- | validity of two summands according to "OAlg.Structure.Additive.Definition#Abl5".
prpAbl5 :: Abelian a => X Z -> X a -> Statement
prpAbl5 xz xf = Prp "Abl5"
  :<=>: Forall xzf (\zf@(z,f)
                    -> ( ztimes z f == if 0 <= z
                                         then ntimes (prj z) f
                                         else negate (ntimes (prj z) f)
                       ):?> Params ["(z,f)":=show zf]
                   )
  where xzf = xTupple2 xz xf

--------------------------------------------------------------------------------
-- XAbl -

-- | random variable for validating 'Abelian' structures. 
data XAbl a = XAbl (X Z) (X a) (X (Adbl2 a))

instance Additive a => Validable (XAbl a) where
  valid (XAbl xz xa xa2)
    = Label "XAbl" :<=>: valid xz && valid xa && valid xa2

--------------------------------------------------------------------------------
-- prpAbl -

-- | validity of the 'Abelian' structure of __@a@__.
prpAbl :: Abelian a => XAbl a -> Statement
prpAbl (XAbl xz xf xa2) = Prp "Abl"
  :<=>: And [ prpAbl1 xf
            , prpAbl2 xf
            , prpAbl3 xfg
            , prpAbl4 xa2
            , prpAbl5 xz xf
            ]
  where xfg = xTupple2 xf xf <|> fmap (\(Adbl2 f g) -> (f,g)) xa2


--------------------------------------------------------------------------------
-- xoRoot -

-- | the induced random variables for roots.
xoRoot :: FibredOriented a => XOrtOrientation a -> X (Root a)
xoRoot = xoOrientation

--------------------------------------------------------------------------------
-- xoAdbl2 -

-- | the induced random variable for two addable summands.
xoAdbl2 :: FibredOriented a => XOrtOrientation a -> X (Adbl2 a)
xoAdbl2 xo = do
  r <- xoRoot xo
  a <- xoArrow xo r
  b <- xoArrow xo r
  return (Adbl2 a b)

--------------------------------------------------------------------------------
-- xoAdbl3 -

-- | the induced random variable for three addable summands.
xoAdbl3 :: FibredOriented a => XOrtOrientation a -> X (Adbl3 a)
xoAdbl3 xo = do
  r <- xoRoot xo
  a <- xoArrow xo r
  b <- xoArrow xo r
  c <- xoArrow xo r
  return (Adbl3 a b c)

--------------------------------------------------------------------------------
-- xoAdd -

-- | the induced random variable for 'Additive' structures with the given random variable to
-- validate 'ntimes'.
xoAdd :: FibredOriented a => X N -> XOrtOrientation a -> XAdd a
xoAdd xn xo = XAdd xn xr xa xa2 xa3 where
  xr = xoRoot xo
  xa = xoFbr xo
  xa2 = xoAdbl2 xo
  xa3 = xoAdbl3 xo

--------------------------------------------------------------------------------
-- xodAbl -

-- | the induced random variable for 'Abelian' structures with the given random variable to
-- validate 'ztimes'.
xoAbl :: FibredOriented a => X Z -> XOrtOrientation a -> XAbl a
xoAbl xz xo = XAbl xz xa xa2 where
  xa = xoFbr xo
  xa2 = xoAdbl2 xo

