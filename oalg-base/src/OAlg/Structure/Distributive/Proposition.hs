
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Structure.Distributive.Proposition
-- Description : propositions on distributive structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions about 'Distributive' structure.
module OAlg.Structure.Distributive.Proposition
  (

    -- * Distributive
    prpDst, XDst(..)
  , prpDst1, prpDst2, prpDst3, prpDst4
  , DstRootSide(..), DstSide(..)


    -- * X
  , XStandardDst(..)
  , xDstStalkStartEnd
  
    -- ** Total
  , xDstTtl
    -- ** Orientation
  , xDstOrnt

    -- ** Oriented Direction
  , xoDst
    -- * Tools
  , dstDst

  )
  where

import Control.Monad

import OAlg.Prelude

import OAlg.Data.Singleton

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive.Definition

--------------------------------------------------------------------------------
-- DstRootSide -

-- | predicate for a root and a factor at the root.
--
-- __Properties__ Let @p@ be in @'DstRootSide' __s__ __d__@ for a 'Distributive' structure @__d__@,
-- then holds:
--
-- (1) If @p@ matches @'LDstRoot' r f@ then holds: @'start' r '==' 'end' f@.
--
-- (2) If @p@ matches @'RDstRoot' f r@ then holds: @'start' f '==' 'end' r@.
data DstRootSide (s :: Side) d where
  LDstRoot :: Root d -> d -> DstRootSide LeftSide d
  RDstRoot :: d -> Root d -> DstRootSide RightSide d

deriving instance Distributive d => Show (DstRootSide s d)

--------------------------------------------------------------------------------
-- DstRootSide - Dualisable -

type instance Dual (DstRootSide s d) = DstRootSide (Dual s) (Op d)

instance Distributive d => Dualisable (DstRootSide RightSide d) where
  toDual (RDstRoot f r)         = LDstRoot (transpose r) (Op f)
  fromDual (LDstRoot r' (Op f)) = RDstRoot f (transpose r')
  
--------------------------------------------------------------------------------
-- DstRootSide - Validable -

instance Distributive d => Validable (DstRootSide s d) where
  valid (LDstRoot r f)    = valid (r,f) && (start r .==. end f )
  valid rd@(RDstRoot _ _) = valid (toDual rd)


--------------------------------------------------------------------------------
-- prpDst1 -

-- | validity according to "OAlg.Structure.Distributive#Dst1".
prpDst1 :: Distributive d => X (DstRootSide LeftSide d) -> Statement
prpDst1 xrg = Prp "Dst1"
  :<=>: Forall xrg (\rg@(LDstRoot r g)
                    -> (zero r * g == zero (start g :> end r))
                       :?> Params ["rg":=show rg]
                   )

--------------------------------------------------------------------------------
-- prpDst3 -

-- | validity according to "OAlg.Structure.Distributive#Dst3".
prpDst3 :: Distributive d => X (DstRootSide RightSide d) -> Statement
prpDst3 xfr = Prp "Dst3" :<=>: prpDst1 (fmap toDual xfr)

--------------------------------------------------------------------------------
-- DstSide -

-- | predicate for two addable summands together with a matching factor.
--
-- __Properties__ Let @p@ be in @'DstSide' __s__ __d__@ for a 'Distributive' structure, then holds:
--
-- (1) If @p@ matches @'LDst' (a,b) g@ then holds:
--
--     (1) @'root' a '==' 'root' b@.
--
--     (2) @'start' a '==' 'end' g@.
--
-- (2) If @p@ matches @'RDst' f (a,b)@ then holds:
--
--     (1) @'root' a '==' 'root' b@.
--
--     (2) @'start' f '==' 'end' a@.
data DstSide (s :: Side) d where
  LDst :: (d,d) -> d -> DstSide LeftSide d
  RDst :: d -> (d,d) -> DstSide RightSide d

deriving instance Distributive d => Show (DstSide s d)

--------------------------------------------------------------------------------
-- DstSide - Dualisable -

type instance Dual (DstSide s d) = DstSide (Dual s) (Op d)

instance Distributive d => Dualisable (DstSide RightSide d) where
  toDual (RDst f (a,b)) = LDst (Op a,Op b) (Op f)
  fromDual (LDst (Op a,Op b) (Op f)) = RDst f (a,b)

--------------------------------------------------------------------------------
-- DstSide - Validable -

instance Distributive d => Validable (DstSide s d) where
  valid (LDst (a,b) g) = valid (Adbl2 a b) && valid (Mltp2 a g)
  valid rd@(RDst _ _)  = valid (toDual rd)
  
--------------------------------------------------------------------------------
-- prpDst2 -

-- | validity according to "OAlg.Structure.Distributive#Dst2".
prpDst2 :: Distributive d => X (DstSide LeftSide d) -> Statement
prpDst2 xabg = Prp "Dst2"
  :<=>: Forall xabg
          (\abg@(LDst (a,b) g)
           -> ((a + b) * g == a*g + b*g) :?> Params ["abg":=show abg]
          )
          
--------------------------------------------------------------------------------
-- prpDst4 -

-- | validity according to "OAlg.Structure.Distributive#Dst4".
prpDst4 :: Distributive d => X (DstSide RightSide d) -> Statement
prpDst4 xfab = Prp "Dst4" :<=>: prpDst2 (fmap toDual xfab) 
                               

--------------------------------------------------------------------------------
-- XDst -

-- | random variable for validating 'Distributive' structures.
data XDst d = XDst (X (DstRootSide LeftSide d))  (X (DstSide LeftSide d))
                   (X (DstRootSide RightSide d)) (X (DstSide RightSide d))

--------------------------------------------------------------------------------
-- XStandardDst -

-- | standard random variable for 'Distributive' structures.
class XStandardDst d where
  xStandardDst :: XDst d
  
--------------------------------------------------------------------------------
-- prpDst -

-- | validity for the 'Distributive' structure of the type @a@.
prpDst :: Distributive d => XDst d -> Statement
prpDst (XDst xrg xabg xfr xfab) = Prp "Dst"
  :<=>: And [ prpDst1 xrg
            , prpDst2 xabg
            , prpDst3 xfr
            , prpDst4 xfab
            ]

--------------------------------------------------------------------------------
-- xDstTtl -

-- | random variable to validate 'Total' 'Distributive' structures.
xDstTtl :: Singleton (Root m) => X m -> XDst m
xDstTtl xm = XDst xrg xabg xfr xfab where
  xrg = do
    g <- xm
    return $ LDstRoot unit g
  xabg = do
    a <- xm
    b <- xm
    g <- xm
    return $ LDst (a,b) g
  xfr  = do
    f <- xm
    return $ RDstRoot f unit
  xfab = do
    f <- xm
    a <- xm
    b <- xm
    return $ RDst f (a,b)

instance XStandardDst N where
  xStandardDst = xDstTtl xStandard
  
instance XStandardDst Z where
  xStandardDst = xDstTtl xStandard
  
instance XStandardDst Q where
  xStandardDst = xDstTtl xStandard
  
--------------------------------------------------------------------------------
-- xDstStalkStartEnd -

-- | the induced random variable for 'Distributive' structures.
xDstStalkStartEnd :: Distributive m
     => XStalk m
     -> XOrtSite From m
     -> XOrtSite To m
     -> XDst m
xDstStalkStartEnd xa xs xe = XDst xrg xabg xfr xfab where
  xrg = do
    r          <- xRoot xa
    Path _ [g] <- xosPathAt xe 1 (start r)
    return $ LDstRoot r g
  xabg = do
    r          <- xRoot xa
    Adbl2 a b  <- xStalkAdbl2 xa r
    Path _ [g] <- xosPathAt xe 1 (start r)
    return $ LDst (a,b) g
  xfr = do
    r          <- xRoot xa
    Path _ [f] <- xosPathAt xs 1 (end r)
    return $ RDstRoot f r
    
  xfab = do
    r          <- xRoot xa
    Path _ [f] <- xosPathAt xs 1 (end r)
    Adbl2 a b  <- xStalkAdbl2 xa r
    return $ RDst f (a,b)

--------------------------------------------------------------------------------
-- xDstOrnt -

-- | random variable for the 'Distributive' structure of @'Orientation' __p__@.
xDstOrnt :: Entity p => X p -> XDst (Orientation p)
xDstOrnt xp = xDstStalkStartEnd xa xs xe where
  xa = xStalkOrnt xp
  xs = xStartOrnt xp
  xe = xEndOrnt xp
  
instance (Entity p, XStandard p) => XStandardDst (Orientation p) where
  xStandardDst = xDstOrnt xStandard
  
--------------------------------------------------------------------------------
-- dstDst -

-- | distribution of @'XDst' __d__@.
dstDst :: Distributive d => Int -> XDst d -> IO ()
dstDst n (XDst xrg xabg xfr xfab) = do
  o <- getOmega
  putStrLn "xrg"
  putDistribution n (fmap show xrg) o
  putStrLn "xabg"
  putDistribution n (fmap show xabg) o
  putStrLn "xfr"
  putDistribution n (fmap show xfr) o
  putStrLn "xfab"
  putDistribution n (fmap show xfab) o

--------------------------------------------------------------------------------
-- xoDstRootSideL -

-- | the induced random variable for @'DstRootSide' 'LeftSide' __d__'@.
xoDstRootSideL :: Distributive d
  => XOrtOrientation d -> XOrtSite To d -> X (DstRootSide LeftSide d)
xoDstRootSideL xo xt = do
  r <- xoRoot xo
  f <- xosEnd xt (start r)
  return (LDstRoot r f)

--------------------------------------------------------------------------------
-- xoDstRootSideR -

-- | the induced random variable for @'DstRootSide' 'RightSide' __d__'@.
xoDstRootSideR :: Distributive d
  => XOrtOrientation d -> XOrtSite From d -> X (DstRootSide RightSide d)
xoDstRootSideR xo xs
  = amap1 fromDual $ xoDstRootSideL (coXOrtOrientation xo) (coXOrtSite xs)

--------------------------------------------------------------------------------
-- xoDstSideL -

-- | the induced random variable for @'DstSide' 'LeftSide' __d__'@.
xoDstSideL :: Distributive d
  => XOrtOrientation d -> XOrtSite To d -> X (DstSide LeftSide d)
xoDstSideL xo xt = do
  Adbl2 a b <- xoAdbl2 xo
  f <- xosEnd xt (start a)
  return (LDst (a,b) f)

--------------------------------------------------------------------------------
-- xoDstSideR -

-- | the induced random variable for @'DstSide' 'RightSide' __d__'@.
xoDstSideR :: Distributive d
  => XOrtOrientation d -> XOrtSite From d -> X (DstSide RightSide d)
xoDstSideR xo xf = amap1 fromDual $ xoDstSideL (coXOrtOrientation xo) (coXOrtSite xf)

--------------------------------------------------------------------------------
-- xodDst -

-- | the induced random variable for 'Distributive' structures.
xoDst :: Distributive d
  => XOrtOrientation d -> XOrtSite From d -> XOrtSite To d -> XDst d
xoDst xo xf xt = XDst xrsl xsl xrsr xsr where
  xrsl = xoDstRootSideL xo xt
  xsl = xoDstSideL xo xt
  xrsr = xoDstRootSideR xo xf
  xsr = xoDstSideR xo xf
