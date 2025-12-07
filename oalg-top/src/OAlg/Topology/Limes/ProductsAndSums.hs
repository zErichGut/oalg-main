
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, TupleSections #-}

-- |
-- Module      : OAlg.Topology.Limes.ProductsAndSums
-- Description : product and disjoint union space.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Product and disjoint union space.
module OAlg.Topology.Limes.ProductsAndSums
  (
  ) where

import Control.Monad as M

import Data.Typeable
import Data.List as L (zip,head,tail,groupBy,(++),foldl)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Canonical
import OAlg.Data.Either
import OAlg.Data.Filterable

-- import OAlg.Structure.Definition
import OAlg.Structure.Oriented
-- import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.PartiallyOrdered

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
-- import OAlg.Entity.Matrix.Vector

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.ProductsAndSums
-- import OAlg.Limes.Proposition

import OAlg.Homology.Simplical hiding (simplex)
import OAlg.Homology.Complex hiding (cpxProduct)
import OAlg.Homology.ChainComplex

import OAlg.Topology.Definition
import OAlg.Topology.Limes.TerminalAndInitialSpace

--------------------------------------------------------------------------------
-- gphProductPrs -

-- | the product graph for the given sets.
--
-- __Prpoperty__ 
gphProductPrs :: (Entity x, Ord x, Entity y, Ord y)
  => Set x -> Set y -> Graph Z (Set (Set (x,y)))
gphProductPrs xs ys = Graph $ gph (-1) xy0 (Set [empty]) where
  dx  = dimension xs
  dy  = dimension ys
  dxy = (-1) `max` (dx + dy)
  xy0 = Set [(x,y) | x <- setxs xs, y <- setxs ys]

  gph :: (Ord x, Ord y) => Z -> Set (x,y) -> Set (Set (x,y)) -> [(Z,Set (Set (x,y)))]
  gph d xy0 xys = (d,xys) : if d < dxy then gph d' xy0 xys' else [] where
    d'   = succ d
    xys' = Set [Set (xy:xys'') | xy <- setxs xy0, Set xys'' <- setxs xys, elg xy xys'']

  elg :: (Ord x, Ord y) => (x,y) -> [(x,y)] -> Bool
  elg _ []                     = True
  elg xy@(x,y) (xy'@(x',y'):_) = x <= x' && y <= y' && xy /= xy'

--------------------------------------------------------------------------------
-- gphProduct -

gphProduct :: (Entity x, Ord x, Entity y, Ord y) => Set x -> Set y -> Graph Z (Set (Set (x,y)))
gphProduct (Set (x:xs)) (Set (y:ys)) =  (x,y) <: gphProduct (Set xs) (Set (y:ys))
                                     || (x,y) <: gphProduct (Set xs) (Set ys)
                                     || (x,y) <: gphProduct (Set (x:xs)) (Set ys)
gphProduct (Set [x]) (Set ys)        = Graph [(dimension ys,Set [Set $ amap1 ((x,)) ys])]
gphProduct (Set xs) (Set [y])        = Graph [(dimension xs,Set [Set $ amap1 ((,y)) xs])]
gphProduct _ _                       = Graph [(-1,Set [empty])]
                                

infixr 5 <:

-- pre: x < x' in g
(<:) :: x -> Graph Z (Set (Set x)) -> Graph Z (Set (Set x))
x <: Graph zxss = Graph $ amap1 (\(z,Set xs) -> (z+1,Set $ amap1 (x<<:) xs)) zxss where

  (<<:) :: x -> Set x -> Set x
  x <<: Set xs = Set (x:xs)

--------------------------------------------------------------------------------
-- cpxRelations -

cpxRelations :: Complex x -> Graph Z (Set (Set x))
cpxRelations (Complex (Graph g)) = Graph (L.tail $ L.tail g)

--------------------------------------------------------------------------------
-- cpxProductPrs -

-- | product for complex within @'ComplexMap' 'Asc'@.
--
-- __Property__ Let @ab = 'cpxProductPrs' a b@, then holds:
--
-- (1) @'ComplexMapPrs' ab a ('Map' fst)@ and @'CompelxMapPrs' ab b ('Map' snd')@ are 'valid'.
cpxProductPrs :: (Entity x, Ord x, Entity y, Ord y)
  => Complex x -> Complex y -> Complex (x,y)
-- cpxProductPrs = cpxProductAsc
{-
cpxProductPrs (Complex (Graph zxss)) (Complex (Graph zyss))
  = Complex $ L.foldl (||) e [gphProduct xs ys | xs <- rxs, ys <- rys]  where

  e   = Graph [(-1,Set [empty])]
  rxs = join $ amap1 (setxs . snd) zxss
  rys = join $ amap1 (setxs . snd) zyss
-}

cpxProductPrs a b
  = Complex $ Graph $ gph xy0 (elg a b) (-1) (Set [empty]) where

  xs  = cpxVertices a
  ys  = cpxVertices b
  dx  = cpxDim a
  dy  = cpxDim b
  dxy = dx + dy
  xy0 = Set [(x,y) | x <- setxs xs, y <- setxs ys]

  map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
  map = Map

  elg :: (Entity x, Ord x, Entity y, Ord y)
    => Complex x -> Complex y -> Set (x,y) -> Bool
  elg a b = (cpxElem a . amap1 (map fst)) && (cpxElem b . amap1 (map snd))

  -- pre: for all xy in xys hilds:
  --        - dimension xy == d.
  --        - elg xy is True.
  gph :: (Ord x, Ord y)
    => Set (x,y) -> (Set (x,y) -> Bool) -> Z -> Set (Set (x,y)) -> [(Z,Set (Set (x,y)))]
  gph xy0 elg d xys = (d,xys) : if d < dxy then gph xy0 elg d' xys' else [] where
    d'   = succ d
    xys' = Set
         $ filter elg
         $ [Set (xy:xys'') | xy <- setxs xy0, Set xys'' <- setxs xys, xy << xys'']

  (<<) :: (Ord x, Ord y) => (x,y) -> [(x,y)] -> Bool
  _ << []                     = True
  xy@(x,y) << (xy'@(x',y'):_) = x <= x' && y <= y' && xy /= xy'

{-
l = complex [Set [0,1]] :: Complex N
k = complex [Set "ab"]
p = cpxProductPrs l k
-}

--------------------------------------------------------------------------------
-- cpxProduct -

cpxProduct :: (Entity x, Ord x, Entity y, Ord y)
  => Complex x -> Complex y
  -> ( Complex (x,y)
     , ComplexMap Asc (Complex (x,y)) (Complex x)
     , ComplexMap Asc (Complex (x,y)) (Complex y)
     )
cpxProduct a b = (ab, mFst, mSnd) where
  ab   = cpxProductPrs a b
  s    = SpxTypeAsc
  mFst = ComplexMap s ab a (Map fst)
  mSnd = ComplexMap s ab b (Map snd)

--------------------------------------------------------------------------------
-- cntProduct2 -

cntProduct2 :: Diagram Discrete N2 N0 (Continuous Asc Abstract)
  -> Product N2 (Continuous Asc Abstract)
cntProduct2 d@(DiagramDiscrete (SpaceAbstract a:|SpaceAbstract b:|Nil))
  = LimesProjective abCn (abUn ab) where
  
  (ab,mFst,mSnd) = cpxProduct a b

  abCn = ConeProjective d (SpaceAbstract ab) (CntAbstract mFst:|CntAbstract mSnd:|Nil)

  abUn :: (Entity x, Ord x, Entity y, Ord y)
    => Complex (x,y) -> ProductCone N2 (Continuous Asc Abstract)
    -> Continuous Asc Abstract
  abUn ab (ConeProjective _ (SpaceAbstract t)  (CntAbstract f:|CntAbstract g:|Nil))
    = case elg ab t f g of
      Nothing                    -> throw $ NotEligibleCone
      Just (Refl,Refl,Refl,Refl) -> CntAbstract fg where
        fg = ComplexMap s t ab (Map (\t -> (f' t, g' t)))
        ComplexMap s _ _ (Map f') = f
        ComplexMap _ _ _ (Map g') = g
        
  elg ::
    (Typeable x, Typeable y, Typeable t)
    => Complex (x,y)
    -> Complex t
    -> ComplexMap Asc (Complex tF) (Complex x')
    -> ComplexMap Asc (Complex tS) (Complex y')
    -> Maybe (t :~: tF,t :~: tS,x :~: x', y :~: y')
  elg ab t f g = do
    tF <- tFEq t f
    tS <- tFEq t g
    xF <- xFEq ab f
    yS <- ySEq ab g
    return (tF,tS,xF,yS)
    
    where
      tFEq :: Typeable t
        => Complex t -> ComplexMap s (Complex tF) c
        -> Maybe (t :~: tF)
      tFEq _ (ComplexMap _ _ _ f) = case tauTyp $ domain f of Struct -> eqT

      xFEq :: Typeable x
        => Complex (x,y) -> ComplexMap s (Complex tF) (Complex xF)
        -> Maybe (x :~: xF)
      xFEq _ (ComplexMap _ _ _ f) = case tauTyp $ range f of Struct -> eqT 

      ySEq :: Typeable y
        => Complex (x,y) -> ComplexMap s (Complex tS) (Complex yS)
        -> Maybe (y :~: yS)
      ySEq _ (ComplexMap _ _ _ g) = case tauTyp $ range g of Struct -> eqT

--------------------------------------------------------------------------------
-- cntProducts2 -

cntProducts2 :: Products N2 (Continuous Asc Abstract)
cntProducts2 = LimitsG cntProduct2

--------------------------------------------------------------------------------
-- cntProducts -

cntProducts :: Products n (Continuous Asc Abstract)
cntProducts = products (products0 spcTerminal) cntProducts2

--------------------------------------------------------------------------------
-- 

instance ApplicativeG (Graph i) (->) (->) where amapG = M.fmap

--------------------------------------------------------------------------------
-- cpxSum2 -

cpxSum2 :: (Entity x, Ord x, Entity y, Ord y)
  => SimplexType s
  -> Complex x -> Complex y
  -> ( Complex (Either x y)
     , ComplexMap s (Complex x) (Complex (Either x y))
     , ComplexMap s (Complex y) (Complex (Either x y))
     )
cpxSum2 s a@(Complex ssx) b@(Complex ssy) = (ab, mFst, mSnd) where
  ab   = Complex (amap1 left ssx || amap1 right ssy)
  mFst = ComplexMap s a ab (Map Left)
  mSnd = ComplexMap s b ab (Map Right)

  left :: Set (Set x) -> Set (Set (Either x y))
  left (Set sx) = Set $ amap1 (\(Set xs) -> Set (amap1 Left xs)) sx

  right :: Set (Set y) -> Set (Set (Either x y))
  right (Set sy) = Set $ amap1 (\(Set ys) -> Set (amap1 Right ys)) sy

--------------------------------------------------------------------------------
-- cntSum2 -

cntSum2 :: Simplical1 s
  => SimplexType s
  -> Diagram Discrete N2 N0 (Continuous s Abstract)
  -> Sum N2 (Continuous s Abstract)
cntSum2 s d@(DiagramDiscrete (SpaceAbstract a:|SpaceAbstract b:|Nil))
  = LimesInjective abCn (abUn s ab) where
  (ab,mFst,mSnd) = cpxSum2 s a b
  
  abCn = ConeInjective d (SpaceAbstract ab) (CntAbstract mFst:|CntAbstract mSnd:|Nil)

  abUn :: (Entity x, Ord x, Entity y, Ord y)
    => SimplexType s -> Complex (Either x y) -> SumCone N2 (Continuous s Abstract)
    -> Continuous s Abstract
  abUn s ab (ConeInjective _ (SpaceAbstract t)  (CntAbstract f:|CntAbstract g:|Nil))
    = case elg ab t f g of
      Nothing                    -> throw $ NotEligibleCone
      Just (Refl,Refl,Refl,Refl) -> CntAbstract $ ComplexMap s ab t (Map fg) where
        
        fg (Left x) = f' x
        fg (Right y) = g' y

        ComplexMap _ _ _ (Map f') = f
        ComplexMap _ _ _ (Map g') = g

  elg ::
    (Typeable x, Typeable y, Typeable t)
    => Complex (Either x y)
    -> Complex t
    -> ComplexMap s (Complex x') (Complex tF)
    -> ComplexMap s (Complex y') (Complex tS)
    -> Maybe (t :~: tF,t :~: tS,x :~: x', y :~: y')
  elg ab t f g = do
    tF <- tEq t f
    tS <- tEq t g
    ex <- xEq ab f
    ey <- yEq ab g
    return (tF,tS,ex,ey)

  tEq :: Typeable t
    => Complex t -> ComplexMap s c (Complex tF) -> Maybe (t :~: tF)
  tEq _ (ComplexMap _ _ _ f) = case tauTyp $ range f of Struct -> eqT

  xEq :: Typeable x
    => Complex (Either x y) -> ComplexMap s (Complex x') c -> Maybe (x :~: x')
  xEq _ (ComplexMap _ _ _ f) = case tauTyp $ domain f of Struct -> eqT

  yEq :: Typeable y
    => Complex (Either x y) -> ComplexMap s (Complex y') c -> Maybe (y :~: y')
  yEq _ (ComplexMap _ _ _ g) = case tauTyp $ domain g of Struct -> eqT


--------------------------------------------------------------------------------
-- cntSums2 -

cntSums2 :: Simplical1 s => SimplexType s -> Sums N2 (Continuous s Abstract)
cntSums2 s = LimitsG $ cntSum2 s

--------------------------------------------------------------------------------
-- cntSums -

cntSums :: Simplical1 s => SimplexType s -> Sums n (Continuous s Abstract)
cntSums s = sums (sums0 (spcInitial s)) (cntSums2 s)


d :: Diagram Discrete N3 N0 (Continuous Asc Abstract)
d = DiagramDiscrete (spcPoint:|spcPoint:|spcPoint:|Nil)

p = limes cntProducts d
s = limes (cntSums SpxTypeAsc) d
pU = universalCone p
sU = universalCone s
{-
pF = universalFactor p pU
sF = universalFactor s sU

(f:|g:|h:|Nil) = shell sU
-}

--------------------------------------------------------------------------------
-- spcType -

spcType :: Space m -> TypeRep
spcType (SpaceAbstract c) = typeOf c
spcType (SpaceConcrete c) = typeOf c


--------------------------------------------------------------------------------
-- spcBorder -

dropLast :: [a] -> [a]
dropLast []     = []
dropLast [_]    = []
dropLast (x:xs) = x:dropLast xs

spcBorder :: Space m -> Space m
spcBorder (SpaceAbstract (Complex (Graph ssx)))
  = SpaceAbstract $ Complex $ Graph $ case ssx of
  [_] -> ssx
  _   -> dropLast ssx

--------------------------------------------------------------------------------
-- simplex -

simplex :: N -> Space Abstract
simplex n = SpaceAbstract $ complex $ [Set [0..n]]

--------------------------------------------------------------------------------
-- sphere -

sphere :: N -> Space Abstract
sphere n = spcBorder $ simplex (n+1)

t :: Diagram Discrete N3 N0 (Continuous Asc Abstract)
t = DiagramDiscrete (s:|s:|s:|Nil) where s = sphere 1

torus :: Space Abstract
torus = tip $ universalCone $ limes cntProducts t

torus' = spcChainComplexSetZ ChainComplexStandard SpxTypeAsc (attest :: Any N3) torus 

-- crds = pmap (hCrd ChainComplexExtended SpxTypeAsc (attest :: Any N3)) torus


cntDim :: Space m -> Z
cntDim (SpaceAbstract (Complex g)) = (inj $ lengthN g) - 2
cntDim s = cntDim $ spcAbstract s

spcCards :: Any n -> Space m -> Cards n
spcCards n (SpaceAbstract c) = cpxCards n c
spcCards n s = spcCards n $ spcAbstract s

{-
ghci> spcCards (attest :: Any N3) torus
DiagramDiscrete [|1,27,189,324,162,0|]

ghci> pmap (cntHmlg ChainComplexExtended SpxTypeAsc (attest :: Any N4)) torus
DiagramDiscrete [|AbGroup[],AbGroup[Z^3],AbGroup[Z^3],AbGroup[Z],AbGroup[]|]

DiagramDiscrete [|1,81,1215,4050,4860,1944,0|]




ghci> spcCards (attest :: Any N3) torus
DiagramDiscrete [|1,27,189,324,162,0|]

ghci> pmap (cntHmlg ChainComplexExtended SpxTypeAsc (attest :: Any N3)) torus
DiagramDiscrete [|AbGroup[],AbGroup[Z^3],AbGroup[Z^3],AbGroup[Z]|]

ghci> spcCards (attest :: Any N5) torus
DiagramDiscrete [|1,243,7533,43740,94770,87480,29160,0|]

-}
