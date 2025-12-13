
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Product.Proposition
-- Description : propositions on products over oriented symbols
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on free products over 'Oriented' symbols with exponents in a 'Number'.
module OAlg.Entity.Product.Proposition
  (
    -- * Proposition
    prpProduct
  , prpOrtProductNOrntSymbol, prpOrtProductZOrntSymbol
  , prpMltProductNOrntSymbol, prpMltProductZOrntSymbol
  

    -- * Random Variables
  , xStartProduct, xStartProductForm
  , xPrdSymStart, xPrdSymMlt

    -- * Example
  , xT, dstT
  )
  where

import Control.Monad

import OAlg.Prelude

import OAlg.Data.Symbol hiding (P)
import OAlg.Data.Canonical
import OAlg.Data.Constructable

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Ring
import OAlg.Structure.Number

import OAlg.Entity.Product.Definition

--------------------------------------------------------------------------------
-- xStartProductForm -

-- | random variable of product forms with maximal /depth/ @d@ (a ':^' constructor
-- dose not increases the depth).
xStartProductForm :: (Oriented a, Number r)
  => XOrtSite From a -> X r -> N -> XOrtSite From (ProductForm r a)
xStartProductForm xs@(XStart xp _) xr d
  = XStart xp (xPrdFrm' d xs xr) where

  xPrdFrm' d xs xr p = do
    d' <- xNB 0 (d+1)
    xPrdFrm d' xs xr p
  
  xBoolExp = xOneOfW [(10,False),(1,True)]

  -- random variable of 1 and -1 - if -1 exists.
  xOneMinusOne :: Number r => X r
  xOneMinusOne = case minusOne of
    Just e  -> xOneOf [rOne,e]
    Nothing -> return rOne 
  
  -- xExp True enriches the product form by a randomly picked exponent, but
  -- lets the orientation unchanged.
  xExp :: (Oriented a, Number r) => Bool -> X r -> ProductForm r a -> X (ProductForm r a)
  xExp False _ pf             = return pf
  xExp True xr pf | isEndo pf = xr >>= return . (pf:^)
                  | otherwise = do
    r   <- xOneMinusOne
    pf' <- return $ if r < rZero then prfInverse pf else pf
    return (pf':^r)

  xPrdFrm :: (Oriented a, Number r, f ~ ProductForm r a)
    => N -> XOrtSite From a -> X r -> Point f -> X f
  xPrdFrm 0 _ xr p = do
    b  <- xBoolExp
    pf <- xExp b xr (One p)
    return pf

  xPrdFrm 1 xs xr p = do
    pth <- xosPathMaxAt xs 1 p
    case pth of
      Path _ []    -> xPrdFrm 0 xs xr p
      Path _ (a:_) -> do
        b  <- xBoolExp
        pf <- xExp b xr (P a)
        return pf

  xPrdFrm d xs xr p = do
    (df,dg) <- xTupple2 xd xd
    g       <- xPrdFrm df xs xr p
    f       <- xPrdFrm dg xs xr (end g)
    (bf,bg) <- xTupple2 xBoolExp xBoolExp
    g'      <- xExp bg xr g
    f'      <- xExp bf xr f
    b       <- xBoolExp
    xExp b xr (f':*g')
    where xd = join $ xOneOfW [(10,xNB 1 (d>-1)),(1,return 0)]


--------------------------------------------------------------------------------
-- xEndProductForm -

-- | the induced random variable.
xEndProductForm :: (Oriented a, Number r) 
  => XOrtSite To a -> X r -> N -> XOrtSite To (ProductForm r a)
xEndProductForm xEnd xr n = fDual $ xStartProductForm (toDual xEnd) xr n where
  fDual :: XOrtSite From (ProductForm r (Op a)) -> XOrtSite To (ProductForm r a)
  fDual xs = fromDual (hh xs)

  hh :: XOrtSite From (ProductForm r (Op a)) -> XOrtSite From (Op (ProductForm r a))
  hh (XStart xp xof) = XStart xp xof' where
    xof' p = ff (xof p)

  ff :: X (ProductForm r (Op a)) -> X (Op (ProductForm r a))
  ff = fmap (Op . prfFromOp)

--------------------------------------------------------------------------------
-- dstXStartProductFrom -

dstXStartProductForm :: Int -> N -> IO ()
dstXStartProductForm n d = getOmega >>= putDistribution n (fmap asps xpf)
  where
    -- asps pf = (dpth pf,skew pf,exp pf)
    -- asps pf = start pf == E && validate' (valid pf)
    asps pf = (dpth pf,exp pf)
    -- asps pf = exp pf
    -- asps pf = (dpth pf,endos pf,exp pf)
    -- asps pf = dpth pf
  
    xpf = xosStart (xStartProductForm (xStartOrnt xSymbol) xr d) E
  
    xr = xZB (-10) 10

dpth :: ProductForm r a -> N
dpth (One _) = 0
dpth (P _)   = 1
dpth (f:^_)  = dpth f
dpth (f:*g)  = max (dpth f) (dpth g) + 1
  
skew :: ProductForm r a -> Z
skew (One _) = 0
skew (P _)   = 1
skew (f:^_)  = skew f
skew (f:*g)  = skew g - skew f
  
exp :: ProductForm r a -> N
exp (f:^_) = exp f + 1
exp (f:*g) = exp f + exp g
exp _      = 0
{-
true1 True = 1
true1 _    = 0

endos :: (Oriented a, Number r) => ProductForm r a -> N
endos (One _) = 1
endos (P a)   = true1 $ isEndo a
endos (f:^_)  = endos f
endos (f:*g)  = endos f + endos g + true1 (isEndo (f:*g))
-}


--------------------------------------------------------------------------------
-- xStartProduct -

-- | random variable of products generated from product forms with a maximal given /depth/
-- (':^' dose not increases the depth).
xStartProduct :: (Oriented a, Integral r) => XOrtSite From a -> X r
  -> N -> XOrtSite From (Product r a)
xStartProduct xs xr d
  = XStart (xosPoint xs) (xPrd $ xosStart $ xStartProductForm xs xr d) where
    xPrd :: (Oriented a, Integral r)
         => (Point a -> X (ProductForm r a))
         -> Point a -> X (Product r a)
    xPrd ixpf = fmap make . ixpf


--------------------------------------------------------------------------------
-- xEndProduct -

-- | random variable of products generated from product forms with a maximal given /depth/
-- (':^' dose not increases the depth).
xEndProduct :: (Oriented a, Integral r) => XOrtSite To a -> X r
  -> N -> XOrtSite To (Product r a)
xEndProduct xe xr d
  = XEnd (xosPoint xe) (xPrd $ xosEnd $ xEndProductForm xe xr d) where
    xPrd :: (Oriented a, Integral r)
         => (Point a -> X (ProductForm r a))
         -> Point a -> X (Product r a)
    xPrd ixpf = fmap make . ixpf


--------------------------------------------------------------------------------
-- dstXStartProduct -

dstXStartProduct :: Int -> N -> IO ()
dstXStartProduct n d = getOmega >>= putDistribution n (fmap asps xprd)
  where
    -- asps pf = (dpth pf,skew pf,exp pf)
    -- asps pf = 
    -- asps pf = (dpth pf,exp pf)
    -- asps pf = exp pf
    
    -- asps (Just p) = start p == 'e' && validate' (valid p)
    asps p = (restrict dpth p,restrict exp p)
    
    xprd = xosStart (xStartProduct (xStartOrnt xSymbol) xr d) E
    -- xprd = xStartProduct (XStart xPthChar) xr d
  
    xr = xZB (-10) 10

--------------------------------------------------------------------------------
-- dstXEndProduct -

dstXEndProduct :: Int -> N -> IO ()
dstXEndProduct n d = getOmega >>= putDistribution n (fmap asps xprd)
  where
    -- asps pf = (dpth pf,skew pf,exp pf)
    -- asps pf = 
    -- asps pf = (dpth pf,exp pf)
    -- asps pf = exp pf
    
    -- asps (Just p) = start p == 'e' && validate' (valid p)
    asps p = (restrict dpth p,restrict exp p,validate' (valid p))
    
    xprd = xosEnd (xEndProduct (xEndOrnt xSymbol) xr d) E
    -- xprd = xEndProduct (XEnd xPthChar) xr d
  
    xr = xZB (-10) 10

--------------------------------------------------------------------------------
-- xStartProductSymbol -

-- | the induced random variable on @'Orientation' 'Symbol')@.
xPrdSymStart :: Integral r => N -> X r -> XOrtSite From (Product r (Orientation Symbol))
xPrdSymStart d xr = xStartProduct (xStartOrnt xSymbol) xr d

xPrdSymEndo :: (Entity p, Integral r, m ~ Product r (Orientation p))
  => X m -> X (Endo m)
xPrdSymEndo xpr = do
  p <- xpr
  return $ Endo $ if isEndo p then p else (inj (end p:>start p) * p)

--------------------------------------------------------------------------------
-- xPrdSymMlt -

-- | the induced random variable for validating 'Multiplicative' structures.
xPrdSymMlt :: Integral r => N -> X r -> XMlt (Product r (Orientation Symbol))
xPrdSymMlt d xr = xMlt xs xn xe where
  xn = xNB 0 10
  xs = xPrdSymStart d xr
  xe = xPrdSymEndo $ xosOrt xs

--------------------------------------------------------------------------------
-- prpOrtProductNOrntSymbol -

-- | validity of @'Product' t'N' ('Orientation' 'Symbol')@ being 'Oriented'.
prpOrtProductNOrntSymbol :: Statement
prpOrtProductNOrntSymbol = Prp "OrtProductNOrntSymbol"
  :<=>: prpOrt xprd where
    xr   = xNB 0 3
    xprd = xosOrt $ xPrdSymStart 7 xr

--------------------------------------------------------------------------------
-- prpOrtProductZOrntSymbol -

-- | validity of @'Product' t'Z' ('Orientation' 'Symbol')@ being 'Oriented'.
prpOrtProductZOrntSymbol :: Statement
prpOrtProductZOrntSymbol = Prp "OrtProductZOrntSymbol"
  :<=>: prpOrt xprd where
    xr   = xZB (-5) 5
    xprd = xosOrt $ xPrdSymStart 11 xr 

--------------------------------------------------------------------------------
-- prpMltProductNOrntSymbol -

-- | validity of @'Product' t'N' ('Orientation' 'Symbol')@ being 'Multiplicative'.
prpMltProductNOrntSymbol :: Statement
prpMltProductNOrntSymbol = Prp "MltProductNOrntSymbol"
  :<=>: prpMlt xprd where
    xr   = xNB 0 7
    xprd = xPrdSymMlt 7 xr

--------------------------------------------------------------------------------
-- prpMltProductZOrntSymbol -

-- | validity of @'Product' t'Z' ('Orientation' 'Symbol')@ being 'Multiplicative'.
prpMltProductZOrntSymbol :: Statement
prpMltProductZOrntSymbol = Prp "MltProductZOrntSymbol"
  :<=>: prpMlt xprd where
    xr   = xZB (-7) 7
    xprd = xPrdSymMlt 7 xr

--------------------------------------------------------------------------------
-- prpProduct -

-- | validity of @'Product' __r__ ('Orientation' 'Symbol')@ for @__r__@ equal to t'N' and t'Z'
-- respectively
prpProduct :: Statement
prpProduct = Prp "Product"
  :<=>: And [ prpOrtProductNOrntSymbol
            , prpOrtProductZOrntSymbol
            , prpMltProductNOrntSymbol
            , prpMltProductZOrntSymbol
            ]


--------------------------------------------------------------------------------
-- Example -

-- | example of a 'XStart' for the quiver having two points \'a\' and \'b\' and two
--   arrows @\'a\':>\'a\'@ and @\'a\':>\'b\'@.
xT :: XOrtSite From (Orientation Char)
xT = XStart xp mxs where
  xp  = xOneOfW [(10,'a'),(1,'b')]
  mxs 'a' = xOneOfW [(2,('a':>'a')),(1,('a':>'b'))]
  mxs _   = XEmpty

-- | its distribution
dstT :: Int -> N -> IO ()
dstT n d = getOmega >>= putDistribution n (fmap asps xprd) where
  asps = show
  xprd = xosStart (xStartProduct xT xn d) 'a'
  xn = xNB 0 10

  

