
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.ProductsAndSums
-- Description : products and sums
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- products and sums, i.e. limits of @'Diagram' 'Discrete'@.
module OAlg.Limes.ProductsAndSums
  (
    -- * Products
    Products, ProductsG
  , Product, ProductG
  , ProductCone, ProductConic
  , ProductDiagram, ProductDiagrammatic

    -- ** Construction
  , prdDiagram, prdCone
  , products, products0, products1, products2

    -- *** Orientation
  , prdConeOrnt, productOrnt, productsOrnt

    -- * Sums
  , Sums, SumsG
  , Sum, SumG
  , SumCone, SumConic
  , SumDiagram, SumDiagrammatic

    -- ** Duality
  , DualisableGDiscrete
  , coProducts, coProductsG

    -- ** Construction
  , sumDiagram, sumCone
  , sums, sums', sums0, sums1, sums2

    -- *** Orientation
  , sumConeOrnt, sumOrnt, sumsOrnt
  )
  where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Entity.FinList
import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Diagram as D

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits

import OAlg.Limes.TerminalAndInitialPoint
import OAlg.Limes.MinimaAndMaxima

--------------------------------------------------------------------------------
-- Product -

-- | 'Diagrammatic' object for a product.
type ProductDiagrammatic d (n :: N') = d Discrete n N0 :: Type -> Type

-- | 'Diagram' for a product.
type ProductDiagram n = ProductDiagrammatic Diagram n

-- | 'Conic' object for a product.
type ProductConic c (d :: DiagramType -> N' -> N' -> Type -> Type) (n :: N')
  = c Mlt Projective d Discrete n N0 :: Type -> Type

-- | 'Cone' for a product.
type ProductCone n = ProductConic Cone Diagram n

-- | generic product as a 'LimesG'.
type ProductG c d n = LimesG c Mlt Projective d Discrete (n :: N') N0

-- | product as a 'Limes'.
type Product n = ProductG Cone Diagram n

-- | generic products for a 'Multiplicative' structure.
type ProductsG c d n = LimitsG c Mlt Projective d Discrete (n :: N') N0

-- | products for a 'Multiplicative' structure.
type Products n = ProductsG Cone Diagram n

--------------------------------------------------------------------------------
-- prdDiagram -

-- | the underlying product diagram.
prdDiagram :: (Oriented x, Diagrammatic d)
  => d (Star From) (n+1) n x -> ProductDiagram n x
prdDiagram d = DiagramDiscrete (amap1 end as) where DiagramSource _ as = diagram d 

--------------------------------------------------------------------------------
-- prdCone -

-- | the product cone.
prdCone :: (Multiplicative x, Diagrammatic d)
  => d (Star From) (n+1) n x -> ProductCone n x
prdCone d = ConeProjective (prdDiagram d) p as where DiagramSource p as = diagram d

--------------------------------------------------------------------------------
-- products0 -

-- | products of zero points given by a terminal point.
products0 :: Multiplicative x => TerminalPoint x -> Products N0 x
products0 t = LimitsG (prd t) where
  prd :: Multiplicative x => TerminalPoint x -> ProductDiagram N0 x -> Product N0 x
  prd t d@(DiagramDiscrete Nil) = LimesProjective l u where 
    l = ConeProjective d (tip $ universalCone t) Nil
    u (ConeProjective _ x Nil) = universalFactor t (trmCone x)

--------------------------------------------------------------------------------
-- products1 -

-- | products of one point, i.e. 'Minima'.
products1 :: Multiplicative x => Products N1 x
products1 = LimitsG prd where
  prd :: Multiplicative x => ProductDiagram N1 x -> Product N1 x
  prd d@(DiagramDiscrete (p:|Nil)) = LimesProjective l u where
    min = limes minimaFrom (DiagramChainFrom p Nil)
    ConeProjective d' t cs = universalCone min
    l = ConeProjective d t cs
    u (ConeProjective _ t cs) = universalFactor min (ConeProjective d' t cs) 

--------------------------------------------------------------------------------
-- products2 -

-- | products of at least two points given by products of two points.
products2 :: Multiplicative x => Products N2 x -> Products (n+2) x
products2 prd2 = LimitsG (prd prd2) where
  prd :: (Multiplicative x, n ~ (n'+2))
      => Products N2 x -> ProductDiagram n x -> Product n x
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

-- | products of @n@ points given by products of zero and two points.
products :: Multiplicative x => Products N0 x -> Products N2 x -> Products n x
products prd0 prd2 = LimitsG (prd prd0 prd2) where
  prd :: Multiplicative x
      => Products N0 x -> Products N2 x -> ProductDiagram n x -> Product n x
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
productOrnt p = lmMltPrjOrnt p . DiagramDiscrete

--------------------------------------------------------------------------------
-- productsOrnt -

-- | products for 'Orientation'.
productsOrnt :: Entity p => p -> Products n (Orientation p)
productsOrnt = lmsMltPrjOrnt

--------------------------------------------------------------------------------
-- Sum -

-- | 'Diagrammatic' object for a sum.
type SumDiagrammatic d (n :: N') = d Discrete n N0 :: Type -> Type

-- | 'Diagram' for a sum.
type SumDiagram n = SumDiagrammatic Diagram n

-- | 'Conic' object for a sum.
type SumConic c (d :: DiagramType -> N' -> N' -> Type -> Type) (n :: N')
  = c Mlt Injective d Discrete n N0 :: Type -> Type

-- | 'Cone' for a sum.
type SumCone n = SumConic Cone Diagram n

-- | generic sum as a 'LimesG'.
type SumG c d n = LimesG c Mlt Injective d Discrete (n :: N') N0

-- | sum as a 'Limes'.
type Sum n = SumG Cone Diagram n

-- | generic sums for a 'Multiplicative' structure.
type SumsG c d n = LimitsG c Mlt Injective d Discrete (n :: N') N0

-- | sums for a 'Multiplicative' structure.
type Sums n = SumsG Cone Diagram n

--------------------------------------------------------------------------------
-- DualisableGDiscrete -

-- | type for dualisable generic limits of 'Conic'' objects over t'Discrete' 'Diagrammatic' objects.
type DualisableGDiscrete p o c d n
  = NaturalConicBi (IsoO Mlt o) c Mlt p d Discrete n N0
  
--------------------------------------------------------------------------------
-- coProductsG -

coProductsG ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableGDiscrete Projective o c d n
  )
  => ProductsG c d n x -> SumsG c d n (o x)
coProductsG ps = ss where
  Contravariant2 i = toDualO (Struct :: Multiplicative x => Struct Mlt x)

  SDualBi (Left1 ss) = amapF i (SDualBi (Right1 ps))

coProducts ::
  ( Multiplicative x
  , TransformableGRefl o Mlt
  , DualisableMultiplicative Mlt o
  )
  => Products n x -> Sums n (o x)
coProducts = coProductsG

--------------------------------------------------------------------------------
-- sumDiagram -

-- | the underlying sum diagram given by a sink diagram.
sumDiagram :: Oriented a => Diagram (Star To) (n+1) n a -> SumDiagram n a
sumDiagram (DiagramSink _ as) = DiagramDiscrete (amap1 start as)

--------------------------------------------------------------------------------
-- sumCone -

-- | the sum cone given by a sink diagram.
sumCone :: Multiplicative a => Diagram (Star To) (n+1) n a -> SumCone n a
sumCone d@(DiagramSink p as) = ConeInjective (sumDiagram d) p as

--------------------------------------------------------------------------------
-- sums0 -

-- | sums of zero points given by a initial point.
sums0 :: Multiplicative x => InitialPoint x -> Sums N0 x
sums0 ip = sms where
  Contravariant2 i = toDualOpMlt

  SDualBi (Left1 tp)   = amapF i (SDualBi (Right1 ip))
  pds                  = products0 tp
  SDualBi (Right1 sms) = amapF (inv2 i) (SDualBi (Left1 pds)) 


-- | sums of one point, i.e. 'Maxima'.
sums1 :: Multiplicative x => Sums N1 x
sums1 = ss where
  Contravariant2 i = toDualOpMlt
  SDualBi (Right1 ss) = amapF (inv2 i) (SDualBi (Left1 products1))
  
-- | sums of at least two points given by sums of two points.
sums2 :: Multiplicative a => Sums N2 a -> Sums (n+2) a
sums2 s2 = ss where
  Contravariant2 i = toDualOpMlt

  SDualBi (Left1 p2)  = amapF i (SDualBi (Right1 s2))
  ps                  = products2 p2 
  SDualBi (Right1 ss) = amapF (inv2 i) (SDualBi (Left1 ps))
  

-- | sums of @n@ points given by sums of zero and two points.
sums :: Multiplicative a => Sums N0 a -> Sums N2 a -> Sums n a
sums sum0 sum2 = LimitsG (sum sum0 sum2) where
  sum :: Multiplicative a
      => Sums N0 a -> Sums N2 a -> SumDiagram n a -> Sum n a
  sum sum0 sum2 d = case d of
    DiagramDiscrete Nil       -> limes sum0 d
    DiagramDiscrete (_:|Nil)  -> limes sums1 d
    DiagramDiscrete (_:|_:|_) -> limes (sums2 sum2) d 


-- | sums given by a proxy type for @n@.
sums' :: Multiplicative a => p n -> Sums N0 a -> Sums N2 a -> Sums n a
sums' _ = sums

--------------------------------------------------------------------------------
-- sumConeOrnt -

-- | sum cone for 'Orientation'.
sumConeOrnt :: Entity p => p -> FinList n p -> SumCone n (Orientation p)
sumConeOrnt p ps = cnInjOrnt p (DiagramDiscrete ps)

--------------------------------------------------------------------------------
-- sumOrnt -

-- | sum for 'Orientation'.
sumOrnt :: Entity p => p -> FinList n p -> Sum n (Orientation p)
sumOrnt p ps = lmMltInjOrnt p (DiagramDiscrete ps)

--------------------------------------------------------------------------------
-- sumsOnt -

-- | sums for 'Orientation'.
sumsOrnt :: Entity p => p -> Sums n (Orientation p)
sumsOrnt = lmsMltInjOrnt


