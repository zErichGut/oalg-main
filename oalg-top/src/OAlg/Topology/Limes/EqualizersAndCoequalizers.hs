
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, TupleSections #-}

-- |
-- Module      : OAlg.Topology.Limes.EqualizersAndCoequalizers
-- Description : equalizers and coequalizers.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Equalizers and coequalizers.
module OAlg.Topology.Limes.EqualizersAndCoequalizers
  (
  ) where

import Control.Monad as M

import Data.Typeable

import Data.List as L (zip,(++),groupBy,head,tail,reverse)

import OAlg.Prelude

import OAlg.Category.Map

-- import OAlg.Data.Ord
-- import OAlg.Data.Either
-- import OAlg.Data.Filterable

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
-- import OAlg.Structure.PartiallyOrdered

import OAlg.Entity.Diagram
import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList as F hiding (zip,(++),tail)
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph

import OAlg.Entity.Matrix

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.EqualizersAndCoequalizers
import OAlg.Limes.Exact.Deviation

import OAlg.Homology.Simplical hiding (simplex,dimension)
import OAlg.Homology.Complex -- hiding (cpxProduct, cpxProductAsc)
import OAlg.Homology.ChainComplex
import OAlg.Homology.Definition -- hiding (B,D,F)

import OAlg.Topology.Definition
import OAlg.Topology.Limes.ProductsAndSums hiding (line)
-- import OAlg.Topology.Limes.TerminalAndInitialSpace

import qualified OAlg.Data.Symbol as S

--------------------------------------------------------------------------------
-- connectionClasses -

-- | the various connection classes.
connectionClasses :: Space m -> Matrix F2
connectionClasses u@(SpaceConcrete _) = connectionClasses $ spcAbstract u
connectionClasses (SpaceAbstract cx)  = p * v where
  p = cokernelFactor $ universalCone ckr
  v = universalFactor kr (ConeKernel d o) where
    d = universalDiagram kr
    o = one $ end $ kernelFactor $ universalCone kr

  VarianceG _ ((kr,ckr):|Nil) = homology f2 cf

  cc = chainComplex ChainComplexStandard SpxTypeSet (attest :: Any N0) cx
  cf = pmap (hF f2 . hZ) cc
  f2 = HmlgF :: f ~ F2 => Homological f (Matrix f)

--------------------------------------------------------------------------------
-- psqList -

-- | the list given by a partially defined sequence with the given length, where the omitted elements
-- are set by the given default value.
psqList :: N -> x -> PSequence N x -> [x]
psqList iL xD (PSequence xis) = psq 0 xD xis where
  psq :: N -> x -> [(x,N)] -> [x]
  psq i _ _ | iL <= i        = []
  psq i xD []                = xD : psq (i+1) xD []
  psq i xD xis@((x,i'):xis') = if i < i'
    then (xD:psq (i+1) xD xis)
    else (x:psq (i+1) xD xis')

--------------------------------------------------------------------------------
-- mtxColVecs -

-- | the columns as a list of vectors.
mtxColVecs :: Semiring x => Matrix x -> [Vector x]
mtxColVecs m = vcs (cols m) (mtxRowCol m) where
  vcs :: Semiring x => Dim' x -> Row N (Col N x) -> [Vector x]
  vcs cls (Row xjs) = psqList (lengthN cls) (zero ()) $ psqMap toVec xjs

  toVec :: Col N x -> Vector x
  toVec (Col xis) = Vector xis
   
--------------------------------------------------------------------------------
-- cpxConnectionGraph -

-- | the connection classes of a complex, represented as a 'Graph' where the first component of its
-- associations is a vertex in the given complex together with its connection class - i.e. the
-- @0@-th homology class according to 'F2' - represented by a 'Vector' over 'F2'. 
cpxConnectionGraph :: (Entity x, Ord x) => Complex x -> Graph x (Vector F2)
cpxConnectionGraph cx = Graph (vx `zip` mtxColVecs (p * v)) where
  vx = setxs $ cpxVertices cx
  
  p = cokernelFactor $ universalCone ckr
  v = universalFactor kr (ConeKernel d o) where
    d = universalDiagram kr
    o = one $ end $ kernelFactor $ universalCone kr

  VarianceG _ ((kr,ckr):|Nil) = homology f2 cf

  cc = chainComplex ChainComplexStandard SpxTypeSet (attest :: Any N0) cx
  cf = pmap (hF f2 . hZ) cc
  f2 = HmlgF :: f ~ F2 => Homological f (Matrix f)


--------------------------------------------------------------------------------
-- cpxMap -

-- | the induced complex map with domain equal to the given one.
cpxMapStruct :: Homomorphous EntOrd x y
  -> Complex x -> Map EntOrd x y -> ComplexMap [] (Complex x) (Complex y)
cpxMapStruct s@(Struct:>:Struct) a f = ComplexMap SpxTypeLst a b f where
  b = complex $ join $ amap1 (setxs . amap1 (mapSet s f) . snd) $ gphxs $ cpxGenerators a
  
  mapSet :: Homomorphous EntOrd x y -> Map EntOrd x y -> Map EntOrd (Set x) (Set y)
  mapSet (Struct:>:Struct) f = Map (amapG f) 

-- | the induced complex map with domain equal to the given one.
cpxMap :: Complex x -> Map EntOrd x y -> ComplexMap [] (Complex x) (Complex y)
cpxMap c f = cpxMapStruct (homomorphous f) c f

--------------------------------------------------------------------------------
-- gphInv -

-- | a /inverse/ graph
gphInv :: Ord x => Graph i x -> Graph x i
gphInv g = Graph $ amap1 L.head $ groupBy (<=>) $ sortFst $ amap1 swp $ gphxs g where
  (x,_) <=> (y,_) = x == y
  
  swp :: (a,b) -> (b,a)
  swp (a,b) = (b,a)
  
--------------------------------------------------------------------------------
-- cntCoequalizerLst -

--  pre:
--  - cpxDomain mf == cpxDomain mg
--  - cpxRange mf == cpxRange mg
coeqStruct :: Homomorphous EntOrd x y
  -> ComplexMap [] (Complex x) (Complex y) -> ComplexMap [] (Complex x) (Complex y)
  -> ( ComplexMap [] (Complex y) (Complex (Vector F2))
     , Map EntOrd (Vector F2) y
     )
coeqStruct (Struct:>:Struct) mf mg = (cpxMap cy (Map h),Map i) where
  ComplexMap _ cx cy (Map f) = mf
  ComplexMap _ _ _ (Map g)   = mg

  -- definition of the quotient complex
  ch = complex (  [Set [y]       | y <- setxs $ cpxVertices cy]
               ++ [set [f x,g x] | x <- setxs $ cpxVertices cx]
               )
       
  gh = cpxConnectionGraph ch      
  h  = fromJust . gphLookup gh

  gi = gphInv gh
  i  = fromJust . gphLookup gi


coeq :: ComplexMap [] (Complex x) (Complex y) -> ComplexMap [] (Complex x) (Complex y)
  -> ( ComplexMap [] (Complex y) (Complex (Vector F2))
     , Map EntOrd (Vector F2) y
     )     
coeq f@(ComplexMap _ _ _ mf) = coeqStruct (homomorphous mf) f


cntCoequalizerLst :: f ~ Continuous [] Abstract => CoequalizerDiagram N2 f -> Coequalizer N2 f
cntCoequalizerLst d@(DiagramParallelRL _ _ (CntAbstract cf:|CntAbstract cg:|Nil))
  = cq d (eqxy cf cg) cf cg where

  eqxy :: ComplexMap s (Complex x) (Complex y) -> ComplexMap s (Complex x') (Complex y')
       -> (Maybe (x :~: x'),Maybe (y :~: y'))
  eqxy (ComplexMap _ _ _ (Map _)) (ComplexMap _ _ _ (Map _)) = (eqT,eqT)

  eqx :: Map EntOrd (Vector F2) x -> ComplexMap s (Complex x') (Complex y')
      -> Maybe (x :~: x')
  eqx (Map _) (ComplexMap _ _ _ (Map _)) = eqT
  
  cq :: f ~ Continuous [] Abstract
     => CoequalizerDiagram N2 f
     -> (Maybe (x :~: x'),Maybe (y :~: y'))
     -> ComplexMap [] (Complex x) (Complex y) -> ComplexMap [] (Complex x') (Complex y')
     -> Coequalizer N2 f
  cq d (Just Refl,Just Refl) f g = LimesInjective cn (uv t i) where
    (p,i) = coeq f g
    
    t  = cpmRange p
    cn = ConeInjective d (SpaceAbstract t) (CntAbstract p:| CntAbstract (p `cpmMlt` f):|Nil)



    uv :: f ~ Continuous [] Abstract
       => Complex (Vector F2)
       -> Map EntOrd (Vector F2) x
       -> CoequalizerCone N2 f -> f
    uv t i (ConeInjective _ _ (CntAbstract h@(ComplexMap s _ cy mh) :|_)) = case eqx i h of
      Just Refl -> CntAbstract (ComplexMap s t cy (mh . i))
      Nothing   -> throw $ InvalidData "not eligible cone"
    
  cq _ _ _ _ = throw $ InvalidData "CoequalizerDiagram"

--------------------------------------------------------------------------------
-- cntCoequalizersLst -

cntCoequalizersLst :: Coequalizers N2 (Continuous [] Abstract)
cntCoequalizersLst = LimitsG cntCoequalizerLst

--------------------------------------------------------------------------------
--

cpxPath :: (Entity x, Ord x, Enum x) => x -> x -> Complex x
cpxPath l h = complex $ amap1 (\(x,y) -> set [x,y]) $ (xs `zip` tail xs) where xs = [l..h]

line :: (Entity x, Ord x, Enum x) => x -> x -> Space Abstract
line l h = SpaceAbstract $ cpxPath l h

cpmReverse :: (Entity x, Ord x) => Complex x -> ComplexMap [] (Complex x) (Complex x)
cpmReverse c = ComplexMap SpxTypeLst c c (Map (fromJust . gphLookup rv)) where
  vs = setxs $ cpxVertices c
  rv = Graph (vs `zip` reverse vs)

cntReverse :: Space Abstract -> Continuous [] Abstract
cntReverse (SpaceAbstract c) = CntAbstract $ cpmReverse c

ff :: (Entity x, Ord x, Enum x)
  => x -> x -> Diagram (Parallel RightToLeft) N2 N2 (Continuous [] Abstract)
ff xl xh                               = case (p,l) of
  (SpaceAbstract cp,SpaceAbstract cl) -> case eqv cp cl of
    Nothing                           -> throw $ ImplementationError ""
    Just Refl                         -> DiagramParallelRL p l (b:|t:|Nil) where
      -- if vl is empty, the resulting maps b and t are still valid!
      vl = setxs $ cpxVertices cl
      vb = L.head vl
      vt = L.head $ reverse vl
      b  = CntAbstract (ComplexMap SpxTypeLst cl cp (Map (fromJust . gphLookup g))) where
        g = Graph $ amap1 (\v -> (v,(vb,v))) vl
      t  = CntAbstract (ComplexMap SpxTypeLst cl cp (Map (fromJust . gphLookup g))) where
        g = Graph $ amap1 (\v -> (v,(vt,v))) vl
    
  where
    p = l <*> l
    l = line xl xh

    eqv :: (Typeable x, Typeable x') => Complex x -> Complex x' -> Maybe (x :~: (x',x'))
    eqv _ _ = eqT


e  = ff S.A S.E

e' = DiagramParallelRL p l (b':|t:|Nil) where
  DiagramParallelRL p l (b:|t:|Nil) = e
  b' = b * cntReverse l
  
le = limes cntCoequalizersLst e
ue = universalCone le
ue' = universalCone $ limes cntCoequalizersLst e'

z = HmlgZ

eC h n = hC' SpxTypeSet h ChainComplexStandard n


{-
p :: Complex S.Symbol
p = complex [Set [S.A,S.B,S.D],Set [S.A,S.C,S.D]]

i :: Complex N
i = complex [Set[0,1]]

f :: ComplexMap [] (Complex N) (Complex S.Symbol)
f = ComplexMap SpxTypeLst i p (Map f') where
  f' 0 = S.A
  f' 1 = S.B

g :: ComplexMap [] (Complex N) (Complex S.Symbol)
g = ComplexMap SpxTypeLst i p (Map g') where
  g' 0 = S.C
  g' 1 = S.D

t :: ComplexMap [] (Complex S.Symbol) (Complex (Vector F2))
t = coeq f g

f2 :: f ~ F2 => Homological F2 (Matrix F2)
f2 = HmlgF

z = HmlgZ

ccStruct :: (Ring r, Commutative r)
  => Homomorphous EntOrd x y -> ComplexMap s (Complex x) (Complex y) -> ChainComplexHom r N3
ccStruct (Struct:>:Struct) = chainComplexHom ChainComplexStandard attest

cc :: ComplexMap s (Complex x) (Complex y) -> ChainComplexHom F2 N3
cc f@(ComplexMap _ _ _ mf) = ccStruct (homomorphous mf) f

ccZ :: ComplexMap s (Complex x) (Complex y) -> ChainComplexHom Z N3
ccZ f@(ComplexMap _ _ _ mf) = ccStruct (homomorphous mf) f
-}

{-
f :: Map EntOrd Symbol (Vector F2)
f = Map (fromJust . gphLookup (cpxConnectionGraph s))

ff :: ComplexMap [] (Complex Symbol) (Complex (Vector F2))
ff = cpxMap s f
-}
