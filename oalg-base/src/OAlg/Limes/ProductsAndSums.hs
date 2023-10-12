
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}


-- | Products and Sums, i.e. limits of 'Discrete'-diagrams.
module OAlg.Limes.ProductsAndSums
  (
    -- * Products
    Products, Product, ProductCone, ProductDiagram

    -- ** Construction
  , prdDiagram, prdCone
  , products, products0, products1, products2

    -- *** Orientation
  , prdConeOrnt, productOrnt, productsOrnt

    -- * Sums
  , Sums, Sum, SumCone, SumDiagram

    -- ** Duality
  , sumLimitsDuality

    -- ** Construction
  , sumDiagram, sumCone
  , sums, sums', sums0, sums1, sums2

    -- *** Orientation
  , sumConeOrnt, sumOrnt, sumsOrnt

  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.FinList
import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Diagram as D

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits

import OAlg.Limes.TerminalAndInitialPoint
import OAlg.Limes.MinimaAndMaxima

--------------------------------------------------------------------------------
-- Product -

type ProductDiagram n         = Diagram Discrete n N0
type ProductCone n            = Cone Mlt Projective Discrete n N0
type Product n                = Limes Mlt Projective Discrete n N0
type Products n               = Limits Mlt Projective Discrete n N0


--------------------------------------------------------------------------------
-- prdDiagram -

-- | the product diagram given by a source diagram.
prdDiagram :: Oriented a => Diagram (Star From) (n+1) n a -> ProductDiagram n a
prdDiagram (DiagramSource _ as) = DiagramDiscrete (amap1 end as)

--------------------------------------------------------------------------------
-- prdCone -

-- | the product cone given by a source diagram.
prdCone :: Multiplicative a => Diagram (Star From) (n+1) n a -> ProductCone n a
prdCone d@(DiagramSource p as) = ConeProjective (prdDiagram d) p as

--------------------------------------------------------------------------------
-- products0 -

-- | products of @0@ points given by a terminal point.
products0 :: Multiplicative a => TerminalPoint a -> Products N0 a
products0 t = Limits (prd t) where
  prd :: Multiplicative a => TerminalPoint a -> ProductDiagram N0 a -> Product N0 a
  prd t d@(DiagramDiscrete Nil) = LimesProjective l u where 
    l = ConeProjective d (tip $ universalCone t) Nil
    u (ConeProjective _ x Nil) = universalFactor t (trmCone x)

--------------------------------------------------------------------------------
-- products1 -

-- | products of @1@ point, i.e. 'minima'.
products1 :: Multiplicative a => Products N1 a
products1 = Limits prd where
  prd :: Multiplicative a => ProductDiagram N1 a -> Product N1 a
  prd d@(DiagramDiscrete (p:|Nil)) = LimesProjective l u where
    min = limes minimaFrom (DiagramChainFrom p Nil)
    ConeProjective d' t cs = universalCone min
    l = ConeProjective d t cs
    u (ConeProjective _ t cs) = universalFactor min (ConeProjective d' t cs) 

--------------------------------------------------------------------------------
-- products2 -

-- | products of at least @2@ points given by products of @2@ points.
products2 :: Multiplicative a => Products N2 a -> Products (n+2) a
products2 prd2 = Limits (prd prd2) where
  prd :: (Multiplicative a, n ~ (n'+2))
      => Products N2 a -> ProductDiagram n a -> Product n a
  prd prd2 d@(DiagramDiscrete (_:|_:|Nil))        = limes prd2 d
  prd prd2 d@(DiagramDiscrete (p0:|pN@(_:|_:|_))) = LimesProjective l u where
    dN = DiagramDiscrete pN
    LimesProjective lN uN = prd prd2 dN
    tN = tip lN
    cN = shell lN

    d2 = DiagramDiscrete (p0:|tN:|Nil)
    LimesProjective l2 u2 = prd prd2 d2
    t2 = tip l2
    l0:|l1:|Nil = shell l2
    
    l = ConeProjective d t2 ls
    ls = l0:|amap1 (*l1) cN

    u (ConeProjective _ t (c0:|cN@(_:|_:|_)))
      = u2 (ConeProjective d2 t (c0:|c1:|Nil)) where
        c1 = uN (ConeProjective dN tN cN)

--------------------------------------------------------------------------------
-- products -

-- | products of @n@ points given by products of @0@ and @2@ points.
products :: Multiplicative a => Products N0 a -> Products N2 a -> Products n a
products prd0 prd2 = Limits (prd prd0 prd2) where
  prd :: Multiplicative a
      => Products N0 a -> Products N2 a -> ProductDiagram n a -> Product n a
  prd prd0 prd2 d = case d of
    DiagramDiscrete Nil       -> limes prd0 d
    DiagramDiscrete (_:|Nil)  -> limes products1 d
    DiagramDiscrete (_:|_:|_) -> limes (products2 prd2) d

--------------------------------------------------------------------------------
-- prdConeOrnt -

-- | product cone for 'Orientation'.
prdConeOrnt :: Entity p => p -> FinList n p -> ProductCone n (Orientation p)
prdConeOrnt p ps = cnPrjOrnt p (DiagramDiscrete ps)

--------------------------------------------------------------------------------
-- productOrnt -

-- | product for 'Orientation'.
productOrnt :: Entity p => p -> FinList n p -> Product n (Orientation p)
productOrnt p ps = lmToPrjOrnt p (DiagramDiscrete ps)

--------------------------------------------------------------------------------
-- productsOrnt -

-- | products for 'Orientation'.
productsOrnt :: Entity p => p -> Products n (Orientation p)
productsOrnt = lmsToPrjOrnt


--------------------------------------------------------------------------------
-- Sum -

type SumDiagram n         = Diagram Discrete n N0
type SumCone n            = Cone Mlt Injective Discrete n N0
type Sum n                = Limes Mlt Injective Discrete n N0
type Sums n               = Limits Mlt Injective Discrete n N0

--------------------------------------------------------------------------------
-- sumDiagram -

sumDiagram :: Oriented a => Diagram (Star To) (n+1) n a -> SumDiagram n a
sumDiagram (DiagramSink _ as) = DiagramDiscrete (amap1 start as)

--------------------------------------------------------------------------------
-- sumCone -

sumCone :: Multiplicative a => Diagram (Star To) (n+1) n a -> SumCone n a
sumCone d@(DiagramSink p as) = ConeInjective (sumDiagram d) p as

--------------------------------------------------------------------------------
-- Sum - Duality - 

sumLimitsDuality :: Multiplicative a => LimitsDuality Mlt (Sums n) (Products n) a
sumLimitsDuality = LimitsDuality ConeStructMlt Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- sums0 -

sums0 :: Multiplicative a => InitialPoint a -> Sums N0 a
sums0 int = lmsFromOp sumLimitsDuality $ products0 $ lmToOp intLimesDuality int

sums1 :: Multiplicative a => Sums N1 a
sums1 = lmsFromOp sumLimitsDuality $ products1

sums2 :: Multiplicative a => Sums N2 a -> Sums (n+2) a
sums2 sum2 = lmsFromOp sumLimitsDuality $ products2 $ lmsToOp sumLimitsDuality sum2

sums :: Multiplicative a => Sums N0 a -> Sums N2 a -> Sums n a
sums sum0 sum2 = Limits (sum sum0 sum2) where
  sum :: Multiplicative a
      => Sums N0 a -> Sums N2 a -> SumDiagram n a -> Sum n a
  sum sum0 sum2 d = case d of
    DiagramDiscrete Nil       -> limes sum0 d
    DiagramDiscrete (_:|Nil)  -> limes sums1 d
    DiagramDiscrete (_:|_:|_) -> limes (sums2 sum2) d 

sums' :: Multiplicative a => p n -> Sums N0 a -> Sums N2 a -> Sums n a
sums' _ = sums

--------------------------------------------------------------------------------
-- sumConeOrnt -

sumConeOrnt :: Entity p => p -> FinList n p -> SumCone n (Orientation p)
sumConeOrnt p ps = cnInjOrnt p (DiagramDiscrete ps)

--------------------------------------------------------------------------------
-- sumOrnt -

sumOrnt :: Entity p => p -> FinList n p -> Sum n (Orientation p)
sumOrnt p ps = lmFromInjOrnt p (DiagramDiscrete ps)
  
--------------------------------------------------------------------------------
-- sumsOnt -

sumsOrnt :: Entity p => p -> Sums n (Orientation p)
sumsOrnt = lmsFromInjOrnt

