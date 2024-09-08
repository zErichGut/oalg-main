
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.AbelianGroup.ZMod
-- Description : homomorphisms between cyclic groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Homomorphisms between cyclic groups.
--
-- A group is called __/cyclic/__ if it is generated by one element.
-- Such a group @G@ is obviously abelian and isomorphic to @'Z'/n'Z'@ for some @n :: 'N'@,
-- which is called its __/order/__. The group homomorphisms between cyclic groups form a
-- 'Z'-algebraic structure which is presented here.
module OAlg.AbelianGroup.ZMod
  (
    
    -- * Cyclic Group
    ZMod(..), zmOrd

    -- * Homomorphism
  , ZModHom(), toZ, fromZ
  , zmh, zmhEligible
  , zmhGenOrd, zmhGenerator
  
    -- * X
    -- | Since the algebraic structure of 'ZModHom' is not balanced - which means that
    -- between any two cyclic groups there may be no nontrivial homomorphisms - it is
    -- appropriate to work with t'XOrtSite' instead of t'XOrtOrientation' for
    -- random variables with values in 'ZModHom'.
  , xZModHom, xZModHomTo, xZModHomFrom
  , xZModTo, xZModFrom

    -- * Proposition
  , prpZModHom

    -- * Exception
  , ZModException(..)  
  )
  where

import Control.Monad
import Control.Exception

import Data.List ((++),foldl)

import OAlg.Prelude

import OAlg.Control.Solver

import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Distributive
import OAlg.Structure.Algebraic

import OAlg.AbelianGroup.Euclid
import OAlg.Entity.Product

--------------------------------------------------------------------------------
-- ZModException -

-- | exceptions for cyclic groups which are sub exceptions from 'SomeOAlgException'.
data ZModException
  = NotEligible String
  deriving (Eq,Show)

instance Exception ZModException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException


--------------------------------------------------------------------------------
-- ZMod -

-- | cyclic group @'Z'\/n@, i.e. the quotient group of 'Z' /divided/
--   by @n'Z'@.
newtype ZMod = ZMod N deriving (Eq,Ord,Validable,Entity)

instance Show ZMod where
  show (ZMod n) = case n of
    0 -> "Z"
    _ -> "Z/" ++ show n


--------------------------------------------------------------------------------
-- zm -

zm0, zm1 :: ZMod
zm0 = ZMod 0
zm1 = ZMod 1

--------------------------------------------------------------------------------
-- zmOrd -

-- | order of the cyclic group.
zmOrd :: ZMod -> N
zmOrd (ZMod n) = n

--------------------------------------------------------------------------------
-- ZModHom -

-- | additive homomorphisms between cyclic groups 'ZMod' constructable via 'zmh'.
--
-- __Note__ The homomorphisms between two cyclic groups @a@ and @b@ form again a cyclic
-- group which will be denoted by @'ZModHom' (a':>'b)@ (see 'zmhGenOrd').
data ZModHom = ZModHom !ZMod !ZMod !Z deriving (Eq,Ord)

instance Show ZModHom where
  show (ZModHom (ZMod 0) (ZMod 0) z) = show z
  show (ZModHom _ _ z)               = "{" ++ show z ++ "}"

--------------------------------------------------------------------------------
-- toZ -

-- | the underlying integer.
toZ :: ZModHom -> Z
toZ (ZModHom _ _ r) = r

--------------------------------------------------------------------------------
-- fromZ -

-- | the endomorphism in @'ZMod' 0@ given by the integer, i.e. the inverse of 'toZ'.
fromZ :: Z -> ZModHom
fromZ r = ZModHom zm0 zm0 r

--------------------------------------------------------------------------------
-- zmhEligible -

-- | predicate to determine the eligibility of a value in 'Z' to induce a homomorphism
-- between the given cyclic groups.
--
-- __Property__ Let @a = 'ZMod' a'@, @b = 'ZMod' b'@ be in 'ZMod' and @r@ in 'Z',
-- then holds: @'zmhEligible' a b r@ is true if and only if
-- @'mod0' (r '*' 'inj' a') b' '==' 0@.
zmhEligible :: ZMod -> ZMod -> Z -> Bool
zmhEligible (ZMod a) (ZMod b) r = mod0 (r * inj a) b == 0

instance Validable ZModHom where
  valid (ZModHom a b r) = Label "ZModHom" :<=>:
    And [ valid (a,b,r)
        , zmhEligible a b r :?> Params ["(a,b,r)":= show (a,b,r)]
        ]

instance Entity ZModHom

--------------------------------------------------------------------------------
-- zmhMod -

-- | reduction to normal form.
zmhMod :: ZModHom -> ZModHom
zmhMod (ZModHom a b r) = ZModHom a b (mod0 r (zmOrd b))

-------------------------------------------------------------------------------
-- zmh -

-- | the induced homomorphism.
--
-- __Property__ Let @a@, @b@ be in 'ZMod' and @r@ in 'Z' then holds:
--
-- (1) @'zmh' a b r@ is 'valid' if and only if @'zmhEligible' a b r@ is true.
--
-- (2) If @'zmhEligible' a b r@ is false then the evaluation of @'zmh' a b r@ will
-- end up by throwing a 'NotEligible'-exception.
zmh :: Orientation ZMod -> Z -> ZModHom
zmh o@(a :> b) r | zmhEligible a b r = zmhMod (ZModHom a b r)
                 | otherwise         = throw $ NotEligible $ show (o,r)

--------------------------------------------------------------------------------
-- ZModHom - Algebraic -

instance Oriented ZModHom where
  type Point ZModHom = ZMod
  orientation (ZModHom a b _) = a:>b

instance Multiplicative ZModHom where
  one a = zmhMod (ZModHom a a 1)
  ZModHom b' c f * ZModHom a b g | b' == b   = zmhMod (ZModHom a c (f*g))
                                 | otherwise = throw NotMultiplicable

  npower h 1 = h
  npower (ZModHom a b r) n | a == b    = zmhMod (ZModHom a a (npower r n))
                           | otherwise = throw NotExponential 

instance Commutative ZModHom

instance Invertible ZModHom where
  tryToInvert (ZModHom a b r)
    | a /= b    = failure NotInvertible
    | g == 1    = return $ zmhMod $ ZModHom a a s
    | otherwise = failure NotInvertible
    where (g,s,_) = euclid r (inj $ zmOrd a)

instance Fibred ZModHom where
  type Root ZModHom = Orientation ZMod

instance FibredOriented ZModHom

instance Additive ZModHom where
  zero (a :> b) = ZModHom a b 0  
  f@(ZModHom a b r) + g@(ZModHom _ _ s)
    | root f == root g = zmhMod (ZModHom a b (r+s))
    | otherwise        = throw NotAddable
    -- note: if r and r' are eligible then r+r' is also eligible!
    
  ntimes n (ZModHom a b r) = zmhMod (ZModHom a b (ntimes n r))
  
instance Abelian ZModHom where
  negate (ZModHom a b r) = zmhMod (ZModHom a b (negate r))
  f@(ZModHom a b r) - g@(ZModHom _ _ s)
    | root f == root g = zmhMod (ZModHom a b (r-s))
    | otherwise        = throw NotAddable
  ztimes z (ZModHom a b r) = zmhMod (ZModHom a b (ztimes z r))
  
instance Vectorial ZModHom where
  type Scalar ZModHom = Z
  (!) = ztimes

instance Distributive ZModHom

instance Algebraic ZModHom

instance OrdPoint ZModHom
--------------------------------------------------------------------------------
-- zmhGenOrd -

-- | @zmhGenOrd (a':>'b) = (r,o)@ where @r@ is a generator for @'ZModHom'(a':>'b)@
-- with order @o@.
--
-- __Note__ It follows that @'inj' o '!' r '==' 'zero' (a':>'b)@ and @'ZModHom'(a':>'b)@
-- is isomorphic to @'Z'\/o@ which is represented by @'ZMod' o@.
zmhGenOrd :: Orientation ZMod -> (ZModHom,N)
zmhGenOrd ab@(a:>b) = go (zmOrd a) (zmOrd b) where
  go :: N -> N -> (ZModHom,N)
  go 0 1   = (zero ab,1) 
  go 0 b'  = (ZModHom a b 1,b')                -- ZModHom(a:>b) ~ Z/b = ZMod (zmOrd b)
  go _ 0   = (zero ab,1)                       -- ZModHom(a:>b) ~ Z/1 = ZMod 1
  go a' b' = (zmhMod (ZModHom a b r),g) where  -- ZModHom(a:>b) ~ Z/gcd a b
    g = gcd a' b'
    r = inj b' // g

--------------------------------------------------------------------------------
-- zmhGenerator -

-- | @zmhGenerator (a:>b) = h@ is a generator for the abelian group @'ZModHom'(a':>'b)@.
zmhGenerator :: Orientation ZMod -> ZModHom
zmhGenerator = fst . zmhGenOrd

--------------------------------------------------------------------------------
-- ZMod - XStandard -

-- | the maximal order of cyclic groups for the standard random variable of type @'X' 'ZMod'@.
--
-- __Property__ @0 < 'stdMaxOrder'@.
stdMaxOrder :: N
stdMaxOrder = 1000

instance XStandard ZMod where
  xStandard = amap1 ZMod $ join $ xn where
    xn = xOneOfW [ (10,return 0)
                 , ( 1,return 1)
                 , (21,xNB 2 stdMaxOrder)
                 ]

--------------------------------------------------------------------------------
-- xZModTo -

-- | random variable of cyclic groups admitting nontrivial homomorphisms to the given group.
xZModTo :: N -> ZMod -> X ZMod
xZModTo 0 z          = return z 
xZModTo _ z@(ZMod 0) = return z
xZModTo _ (ZMod 1)   = xStandard
xZModTo i (ZMod n)   = xTakeB 1 (e+i) (xOneOf dvs) >>= return . ZMod . foldl (*) 1
  where ps = fromWord $ nFactorize n
        e  = foldl (+) 0 $ amap1 snd ps
        dvs = amap1 fst ps 

dstXZModTo :: Int -> N -> ZMod -> IO ()
dstXZModTo n i z = getOmega >>= putDistribution n (xZModTo i z)

--------------------------------------------------------------------------------
-- xZModFrom -

-- | random variable of cyclic groups admitting non trivial homomorphisms from the given one.
xZModFrom :: N -> ZMod -> X ZMod
xZModFrom _ (ZMod 0) = xStandard
xZModFrom _ (ZMod 1) = xStandard
xZModFrom i z        = xZModTo i z

--------------------------------------------------------------------------------
-- xZModHom -

-- | random variable for homomorphisms for the given orientation of 'ZMod'.
xZModHom :: X Z -> Orientation ZMod -> X ZModHom
xZModHom xz (ZMod 0 :> ZMod 0) = xz >>= return . ZModHom zm0 zm0
xZModHom _ (a :> ZMod 1)       = return (ZModHom a zm1 0)
xZModHom _ (ZMod 1 :> b)       = return (ZModHom zm1 b 0)
xZModHom xz ab                 = xh (zmhGenOrd ab) where
  xh (h,0) = xz >>= return . (! h)
  xh (h,1) = return h
  xh (h,o) = do
    n <- xNB 1 (pred o)
    return (ntimes n h)
  

--------------------------------------------------------------------------------
-- xZModHomTo -

-- | random variable for homomorphisms based on 'xZModTo'.
xZModHomTo :: N -> X Z -> X ZMod -> XOrtSite To ZModHom
xZModHomTo i xz xm = XEnd xm xh where
  xh t = do
    f <- xZModTo i t
    xZModHom xz (f:>t)

dstZModHomTo :: Int -> N -> X Z -> X ZMod -> IO ()
dstZModHomTo n i xz xm = getOmega >>= putDistribution n xHomOrt where
  XEnd xt xh = xZModHomTo i xz xm
  xHomOrt = do
    ZModHom _ _ r <- xt >>= xh
    return (if r == 0 then 0 else lengthN $ show r)

instance XStandardOrtSite To ZModHom where
  xStandardOrtSite = xZModHomTo 5 xStandard xStandard

--------------------------------------------------------------------------------
-- xZModHomFrom -

-- | random variable for homomorphisms based on 'xZModFrom'.
xZModHomFrom :: N -> X Z -> X ZMod -> XOrtSite From ZModHom
xZModHomFrom i xz xm = XStart xm xh where
  xh f = do
    t <- xZModFrom i f
    xZModHom xz (f:>t)
  
dstZModHomFrom :: Int -> N -> X Z -> X ZMod -> IO ()
dstZModHomFrom n i xz xm = getOmega >>= putDistribution n xHomOrt where
  XStart xt xh = xZModHomFrom i xz xm
  xHomOrt = do
    ZModHom _ _ r <- xt >>= xh
    return (if r == 0 then 0 else lengthN $ show r)

instance XStandardOrtSite From ZModHom where
  xStandardOrtSite = xZModHomFrom 5 xStandard xStandard
  
--------------------------------------------------------------------------------
-- prpZModHom -

-- | validity of the 'Z'-algebraic structure of 'ZModHom'.
prpZModHom :: Statement
prpZModHom = Prp "ZModHom" :<=>:
  And [ prpOrt xOrt
      , prpMlt xMlt
      , prpFbr xFbr
      , prpAdd xAdd
      , prpAbl xAbl
      , prpDst xDst
      ] where

  xz     = xStandard
  xMod   = xStandard 
  xHomTo = xStandardOrtSite :: XOrtSite To ZModHom 
  
  xOrt = xosOrt xHomTo
  
  xMlt = XMlt xn xMod xOrt xe xh2 xh3 where
    xn = xNB 0 100
    xe = do
      c <- xMod
      h <- xZModHom xz (c:>c)
      return $ Endo $ h
      
    xh2 = xMltp2 xHomTo
    xh3 = xMltp3 xHomTo
  
  xFbr = xOrt

  xRoot  = do
    t <- xMod
    f <- xZModTo 5 t
    return (f:>t)

  xStalk = XStalk xRoot (xZModHom xz)
  xAdd = xAddStalk xStalk (xNB 0 1000)
  xAbl = XAbl xStandard xFbr xa2 where
    xa2 = xRoot >>= xStalkAdbl2 xStalk

    
  xHomFrom = xStandardOrtSite :: XOrtSite From ZModHom
  xDst = xDstStalkStartEnd xStalk xHomFrom xHomTo
  
{-
--------------------------------------------------------------------------------
-- ZModHomForm -

-- | form of a group homomorphism between cyclic groups.
--
--  __Property__ Let @'ZModHomForm' ('ZMod' a) ('ZMod' b) r@ be in t'ZModHomForm' then holds:
--  @'mod0' (r' '*' 'inj' a) b '==' 0@.
data ZModHomForm = ZModHomForm ZMod ZMod Z deriving (Eq,Ord,Show)

--------------------------------------------------------------------------------
-- cyhfz -

-- | the underlying integer.
cyhfz :: ZModHomForm -> Z
cyhfz (ZModHomForm _ _ r) = r

cy0 :: ZMod
cy0 = ZMod 0

zcyhf :: Z -> ZModHomForm
zcyhf r = ZModHomForm cy0 cy0 r

--------------------------------------------------------------------------------
-- ZModHom - Entity -


instance Oriented ZModHomForm where
  type Point ZModHomForm = ZMod
  orientation (ZModHomForm a b _) = a:>b

instance Fibred ZModHomForm where
  type Root ZModHomForm = Orientation ZMod

instance FibredOriented ZModHomForm

cyhfMlt :: ZModHomForm -> ZModHomForm -> ZModHomForm
cyhfMlt (ZModHomForm _ d f) (ZModHomForm a _ g) = ZModHomForm a d (f*g)

cyhfNPower :: ZModHomForm -> N -> ZModHomForm
cyhfNPower (ZModHomForm a b f) n = ZModHomForm a b (npower f n)

cyhfAdd :: ZModHomForm -> ZModHomForm -> ZModHomForm
cyhfAdd (ZModHomForm a b f) (ZModHomForm _ _ g) = ZModHomForm a b (f+g)

cyhfNTimes :: N -> ZModHomForm -> ZModHomForm
cyhfNTimes n (ZModHomForm a b f) = ZModHomForm a b (ntimes n f)

cyhfNeg :: ZModHomForm -> ZModHomForm
cyhfNeg (ZModHomForm a b f) = ZModHomForm a b (negate f)

cyhfSub :: ZModHomForm -> ZModHomForm -> ZModHomForm
cyhfSub (ZModHomForm a b f) (ZModHomForm _ _ g) = ZModHomForm a b (f-g)

cyhfZTimes :: Z -> ZModHomForm -> ZModHomForm
cyhfZTimes z (ZModHomForm a b f) = ZModHomForm a b (ztimes z f)

--------------------------------------------------------------------------------
-- ZModHomForm - Reduzible -

instance Reducible ZModHomForm where
  reduce (ZModHomForm a b r) = ZModHomForm a b (mod0 r (zmOrd b))

--------------------------------------------------------------------------------
-- ZModHom -

-- | representation of a group homomorphism between cyclic groups. They are
--   constructed via 'ZModHomForm'\'s.
newtype ZModHom = ZModHom ZModHomForm deriving (Eq,Ord,Validable,Entity)

instance Show ZModHom where
  show (ZModHom (ZModHomForm _ b r))
    | b == ZMod 0 = show r
    | otherwise = "{"++show r++"}"

--------------------------------------------------------------------------------
-- cyHom -

cyHom :: ZMod -> ZMod -> Z -> ZModHom
cyHom a b z = error "nyi"

--------------------------------------------------------------------------------
-- cyGenerator -

-- | generating homomorphism of the cyclic group, i.e the epimorphism with
--  @'start' '==' 'ZMod' 0@ and induced by @1@.
--
-- @
--           cyGenerator c
--    ZMod 0 ---------------->> c
--
-- @
cyGenerator :: ZMod -> ZModHom
cyGenerator c = make (ZModHomForm (ZMod 0) c 1) 

--------------------------------------------------------------------------------
-- cyhLift

-- | lifting a homomorphism between cyclic groups to its canonical homormorphism
-- between @'ZMod' 0@.
cyhLift :: ZModHom -> ZModHom
cyhLift (ZModHom (ZModHomForm _ _ r)) = ZModHom (ZModHomForm z z r) where z = ZMod 0

--------------------------------------------------------------------------------
-- ZModHom - Constructabel -

instance Exposable ZModHom where
  type Form ZModHom = ZModHomForm
  form (ZModHom f) = f

instance Constructable ZModHom where
  make = ZModHom . reduce

--------------------------------------------------------------------------------
-- ZModHom - Algebraic -

instance Oriented ZModHom where
  type Point ZModHom = ZMod
  orientation = restrict orientation

instance Multiplicative ZModHom where
  one a = make (ZModHomForm a a 1)
  ZModHom f * ZModHom g = if start f == end g
    then make (f `cyhfMlt` g)
    else throw NotMultiplicable
  npower f 1                          = f
  npower f _         | not (isEndo f) = throw NotExponential
  npower (ZModHom f) n                  = make (cyhfNPower f n)

instance Commutative ZModHom

instance Invertible ZModHom where
  tryToInvert (ZModHom (ZModHomForm a b r))
    | a /= b    = failure NotInvertible
    | g == 1    = return $ ZModHom $ ZModHomForm a a (mod0 s (zmOrd a))
    | otherwise = failure NotInvertible
    where (g,s,_) = euclid r (inj $ zmOrd a)

instance Fibred ZModHom where
  type Root ZModHom = Orientation ZMod

instance FibredOriented ZModHom

instance Additive ZModHom where
  zero (a :> b) = ZModHom (ZModHomForm a b 0)
  ZModHom f + ZModHom g = if root f == root g
    then make (f `cyhfAdd` g)
    else throw NotAddable
    -- note: if r and r' are eligible then r+r' is also eligible!
  ntimes n (ZModHom f) = make (cyhfNTimes n f)
  
instance Abelian ZModHom where
  negate (ZModHom f) = make (cyhfNeg f)
  ZModHom f - ZModHom g = if root f == root g
    then make (f `cyhfSub` g)
    else throw NotAddable
  ztimes z (ZModHom f) = make (cyhfZTimes z f)
  
instance Vectorial ZModHom where
  type Scalar ZModHom = Z
  z ! ZModHom f = make (cyhfZTimes z f)

instance Distributive ZModHom

instance Algebraic ZModHom

--------------------------------------------------------------------------------
-- cyGenHomOrd -

-- | @cyGenHomOrd (a':>'b) = (r,o)@ where @r@ is a generator for @'ZModHom'(a':>'b)@ with
--   order @o@.
--
--   __Note__
--
--   (1) It follows that @'inj' o '!' r '==' 'zero' (a':>'b)@ and @'ZModHom'(a':>'b)@
--   is isomorphic to @'Z'\/o@ which is represented by @'ZMod' o@.
--
--   (1) In the case that @a '==' 'ZMod' 0@ then @o '==' 'zmOrd' b@.
--
--   (1) In the case that @a '/=' 'ZMod' 0@ and @b '==' 'ZMod' 0@ then @o '==' 1@.
--
--   (1) In the case that @a '/=' 'ZMod' 0@ and @b '/=' 'ZMod' 0@ then @o '==' b' '//' g@
--   where @g = 'gcd' a' b'@, @a' = 'inj' '$' 'zmOrd' a@ and @b' = 'inj' '$' 'zmOrd' b@. 
cyGenHomOrd :: Orientation ZMod -> (ZModHom,N)
cyGenHomOrd (a:>b) = go (zmOrd a) (zmOrd b) where
  go :: N -> N -> (ZModHom,N)
  go 0 _   = (make (ZModHomForm a b 1),zmOrd b)  -- ZModHom(a:>b) ~ Z/b = ZMod (zmOrd b)
  go _  0  = (make (ZModHomForm a b 0),1)        -- ZModHom(a:>b) ~ Z/1 = ZMod 1
  go a' b' = (make (ZModHomForm a b r),g) where  -- ZModHom(a:>b) ~ Z/gcd a b
    g = gcd a' b'
    r = inj b' // g

--------------------------------------------------------------------------------
-- cyGenHom -

-- | @cyGenHom (a:>b) = h@ is a generater for the abelian group @'ZModHom'(a':>'b)@.
cyGenHom :: Orientation ZMod -> ZModHom
cyGenHom = fst . cyGenHomOrd

--------------------------------------------------------------------------------
-- xodZModHom -

xodZModHom :: X Z -> X ZMod -> XOrtDirection LeftToRight ZModHom
xodZModHom xz xcy = XOrtLeftToRight xcy xh where
    xh a b = zs o >>= return . (! h) where
      (h,o) = cyGenHomOrd (a:>b)
      zs :: N -> X Z
      zs 0 = xz
      zs 1 = return 0
      zs o = amap1 inj $ xNB 1 (pred o)
  
--------------------------------------------------------------------------------
-- ZModHom - XStandardOrtDirection -

instance XStandardOrtDirection LeftToRight ZModHom where
  xStandardOrtDirection = xodZModHom xStandard (amap1 ZMod xStandard)
  
instance XStandardOrtDirectionLR ZModHom

dst :: Int -> IO ()
dst n = getOmega >>= putDistribution n (amap1 shw xc) where
  xc :: X (Orientation ZMod,ZModHom)
  xc = do
    h <- xodOrt (xStandardOrtDirection :: XOrtDirection LeftToRight ZModHom)
    return (orientation h,h)

  shw (o,h) = join $ tween ":" [shwo o,shwh h] 

  shwc v (ZMod n) = if 1 < n then v else show n

  shwo (a:>b) = join $ tween "->" $ if a == b
    then [shwc "n" a,shwc "n" a]
    else [shwc "n" a,shwc "m" b]
  
  shwh h = if isZero h then "0" else "h"

-}
