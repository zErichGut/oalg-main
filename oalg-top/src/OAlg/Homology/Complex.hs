
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , DataKinds
  , TupleSections
#-}

-- |
-- Module      : OAlg.Homology.Complex
-- Description : definition of simplical complexes.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of simplical 'Complex'.
module OAlg.Homology.Complex
  (

    -- * Complex
    Complex(..), cpxxs, complex, cpxSet, cpxVertexSet
  , cpxEmpty, cpxIndex

    -- * Complex Map
  , ComplexMap(..)

{-    
    -- * Complex
    Complex(..)
  , cpxDim
  , cpxSet, cpxSucc, cpxPred
  , cpxIndex
  -- , cpxMapBoundary, cpxHomBoundary'

    -- ** Construction
  , cpxEmpty, (<+), complex
  -- , SomeComplex(..)

    -- * Examples
    -- ** Dimension 1
  , segment

    -- ** Dimension 2
  , triangle, plane, torus, torus2
  , kleinBottle, moebiusStrip
  , projectivePlane

  , dh0, dh1, dh2

    -- ** Dimension n
  , sphere
-}
  ) where

import Control.Monad

import Data.List as L (head,tail,zip,last,reverse,repeat,(++),span,filter)
import Data.Foldable (toList,foldl)
import Data.Maybe

import OAlg.Prelude

import OAlg.Data.Constructable

import OAlg.Structure.Number.Definition (mod)


import OAlg.Hom.Distributive ()

import OAlg.Entity.Sequence hiding (span)

import OAlg.Homology.Simplical

-- | set of simplices over @__x__@ according to @__s__@.
--
-- __Properties__ Let @'SimplexSet' zssx@ be in @'SimplexSet' __s__ __x__@ for a 'Simplical' structure
-- @__s__@, then holds:
--
-- (1) For all @(z,ssx)@ in @zssx@ holds:
--
--    (1) @ssx@ is not empty.
--
--    (2) @'dimension' sx '==' z@ for all @sx@ in @ssx@.
--
-- (2) For all @..(z,ssx):(z',ssx')..@ in @zssx@ holds: @z < z'@.
data SimplexSet s x = SimplexSet [(Z,Set (s x))]

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Set -

deriving instance (Ord i, Ord x) => Ord (Graph i x)

--------------------------------------------------------------------------------
-- setDifference -
setDifference :: Ord x => Set x -> Set x -> Set x
setDifference (Set xs) (Set ys) = Set $ diff xs ys where
  diff [] _          = []
  diff xs []         = xs
  diff (x:xs) (y:ys) = case x `compare` y of
    LT -> x : diff xs (y:ys)
    EQ -> diff xs ys
    GT -> diff (x:xs) ys

--------------------------------------------------------------------------------
-- Cycle -

-- | cycle over the index @__i__@, i.e. a monomorph list @i 0, i 1 .. i j, i (j+1)..,i (n-1),i n@
--   where @1 <= n@ and represents the permutation where @i j@ maps to @i (j+1)@ for @j = 0..n.1@ and
--   @j n@ maps to @i 0@.
--
--   __Properties__ Let @'Cycle' is@ be in @'Cycle' __i__@, then holds:
--
--  (1) @'length' is '>=' 2@.
--
--  (2) @is@ is monomorph.
newtype Cycle i = Cycle [i] deriving (Show,Eq,Ord)

instance (Show i, Ord i, Validable i) => Validable (Cycle i) where
  valid (Cycle is) = Label "Cycle" :<=>:
    And [ valid is
        , Label "length" :<=>: (lengthN is >= 2) :?> Params ["length is":= (show $ lengthN is)]
        , Label "monomorph" :<=>: (lengthN is == (lengthN $ set is)) :?> Params ["is":=show is]
        ]

--------------------------------------------------------------------------------
-- splitCycle -

splitCycle :: Eq i => Permutation i -> Maybe (Cycle i,Permutation i)
splitCycle p = do
  PermutationForm jis <- return $ form p
  (c,jis')            <- splitCycle' jis
  return (c,make $ PermutationForm jis')

splitCycle' :: Eq i => PSequence i i -> Maybe (Cycle i,PSequence i i)
splitCycle' (PSequence [])          = Nothing
splitCycle' (PSequence ((j,i):jis)) = Just (Cycle $ reverse cs,PSequence jis') where
  (cs,jis') = sc i j ([i],jis)

  sc i j res | i == j = res
  sc i j (cs,jis)     = case span ((j/=) . snd) jis of
    (jis',jis'')     -> case jis'' of
      (j',_):jis'''  -> sc i j' (j:cs,jis' ++ jis''')
      _              -> throw $ InvalidData "splitCycle'"
    
--------------------------------------------------------------------------------
-- splitCycles -

splitCycles :: Eq i => Permutation i -> [Cycle i]
splitCycles p = cyc is where
  PermutationForm is = form p
  
  cyc is = case splitCycle' is of
    Nothing      -> []
    Just (c,is') -> c : cyc is'
  
--------------------------------------------------------------------------------
-- pmtSign -

-- | the signum of a permutation
pmtSign :: Permutation N -> Z
pmtSign p = if mod (lengthN $ splitCycles p) 2 == 0 then 1 else -1


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Complex -

-- | complex over a vertex type @__x__@.
--
--  __Properties__ Let @c = 'Complex' zssx@ be in @'Complex' __x__@, then holds:
--
--  (1) @zssx@ is a non empty list.
--
--  (2) @z0 '==' -1@ where @(z0,_) = 'head' zsx@.
--
--  (3) For all @(z,'Set' sxs)@ in @zssx@ holds: @'dimension' sx '==' z@ for all @sx@ in @sxs@.
--
--  (4) For all @..(z,su)':'(z',sv)..@ in @zsx@ holds:
--
--    (1) @z' '==' z '+' 1@.
--
--    (2) @'faces'' sv'@ is a subset of @su@.
newtype Complex x = Complex [(Z,Set (Set x))] deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- Complex - Set - Entity -

instance (Entity x, Ord x) => Validable (Complex x) where
  valid (Complex zsx) = Label "Complex" :<=>: case zsx of
    []            -> Label "1" :<=>: SInvalid
    ((z,sx):zsx') -> And [ Label "2" :<=>: (z == -1) :?> Params ["z0" := show z]
                         , valid sx
                         , vldDimension z sx
                         , vldFaces z sx zsx'
                         ]
    where
      vldDimension z sx = Label "3" :<=>:
        (foldl vDim True sx) :?> Params ["z":=show z, "sx" := show sx]
          where vDim b sx = b && (dimension sx == z)

      vldFaces _ _ [] = SValid
      vldFaces z su ((z',sv):zsx')
        = And [ valid sv
              , Label "4.1'" :<=>: (z' == succ z) :?> Params ["z":=show z, "z'":=show z']
              , vldDimension z' sv
              , Label "4.2" :<=>: let fsv = faces' sv in
                  (fsv `isSubSet` su) :?> Params ["fsv":=show (fsv `setDifference` su)]
              , vldFaces z' sv zsx'
              ]


instance (Entity x, Ord x) => Entity (Complex x)

--------------------------------------------------------------------------------
-- cpxxs -

cpxxs :: Complex x -> [(Z,Set (Set x))]
cpxxs (Complex zsx) = zsx

--------------------------------------------------------------------------------
-- cpxVertices -

cpxVertices :: Complex x -> Set (Set x)
cpxVertices (Complex zsx) = case tail zsx of
  (_,sv):_ -> sv
  _        -> setEmpty

--------------------------------------------------------------------------------
-- isVertex -

isVertex :: Ord x => x -> Complex x -> Bool
isVertex x c = Set [vertex x] `isSubSet` cpxVertices c

--------------------------------------------------------------------------------
-- cpxSet -

cpxSet :: Complex x -> Set (Z,Set x)
cpxSet (Complex zsx) = Set $ join $ amap1 (\(z,Set sx) -> amap1 (z,) sx) zsx

--------------------------------------------------------------------------------
-- cpxSetMax -

-- | the maximal simplices for each dimension which are not faces. They form a generator set
-- of the complex.
cpxSetMax :: Ord x => Complex x -> Set (Z,Set (Set x))
cpxSetMax (Complex zsx)
  = Set $ filter ((setEmpty /=).snd) $ amap1 (uncurry diff) (zsx `zip` tail zsx') where
    zsx' = amap1 (\(_,sx) -> (faces' sx)) zsx ++ repeat setEmpty
    diff (z,sx) sx' = (z,sx `setDifference` sx')

--------------------------------------------------------------------------------
-- cpxIndex -

cpxIndex :: Ord x => Complex x -> (Z,Set x) -> Maybe N
cpxIndex = setIndex . cpxSet

--------------------------------------------------------------------------------
-- cpxCards -

cpxCards :: Complex x -> [(Z,N)]
cpxCards (Complex zsx) = amap1 (\(z,s) -> (z,lengthN s)) zsx

--------------------------------------------------------------------------------
-- cpxEmpty -

cpxEmpty :: Complex x
cpxEmpty = Complex [(-1,Set [setEmpty])]

--------------------------------------------------------------------------------
-- cpxBorder -

cpxBorder :: Complex x -> Maybe (Complex x)
cpxBorder (Complex [_]) = Nothing -- empty complex has no border!
cpxBorder (Complex ss)  = Just $ Complex (dropLast ss) where
  dropLast []     = []
  dropLast [_]    = []
  dropLast (x:xs) = x : dropLast xs


--------------------------------------------------------------------------------
-- (<|>) -

-- | the union of two complexes.
(<|>) :: Ord x => Complex x -> Complex x -> Complex x
Complex as <|> Complex bs = Complex $ uni as bs where
  uni [] bs = bs
  uni as [] = as
  uni ((z,sx):zsx) ((_,sy):zsy) = (z,sx `setUnion` sy):uni zsx zsy


--------------------------------------------------------------------------------
-- complex -

complex :: Ord x => [Set x] -> Complex x
complex = foldl (<|>) cpxEmpty . amap1 (Complex . simplices)

--------------------------------------------------------------------------------
-- cpxTerminal -

cpxTerminal :: Ord x => x -> Complex x
cpxTerminal x = complex [Set [x]]

--------------------------------------------------------------------------------
-- cpxVertexSet -

cpxVertexSet :: Complex x -> Set x
cpxVertexSet = Set . amap1 (head . toList) . setxs . cpxVertices

--------------------------------------------------------------------------------
-- cpxProduct -


cpxProduct :: (Ord x, Ord y) => Complex x -> Complex y -> Complex (x,y)
cpxProduct a b
  = Complex
  $ filter ((/= setEmpty) . snd)
  $ spxFilter (feasable . snd)
  $ simplices
  $ Set [(x,y) | x <- setxs $ cpxVertexSet a, y <- setxs $ cpxVertexSet b]
  where
    ia = setIndex $ cpxSet a
    ib = setIndex $ cpxSet b

    feasable xys = (spxAdjDim xs `elem` ia) && (spxAdjDim ys `elem` ib) where
      xs = amap1 (OrdMap fst) xys
      ys = amap1 (OrdMap snd) xys

    elem x i = case i x of
      Nothing -> False
      Just _  -> True

--------------------------------------------------------------------------------
-- ComplexMap -

-- | mapping between complexes, where the underlying map induces a map between the two
-- given simpliex sets.
--
-- __Properties__ Let @'ComplexMap' cx cy f@ be in
-- @'ComplexMap' ('Complex' __x__) ('Complex' __y__)@ then for all simplices @s@ in @cx@ holds: 
-- @'amap1' f s@ is an element of @cy@.
--
-- __Note__ If @cx@ and @cy@ are 'valid' then it is sufficient to thest the property on the
-- maximal simplexes @s@, given by @'cpxSetMax' cx@.
data ComplexMap a b where
  ComplexMap
    :: Complex x -> Complex y
    -> OrdMap x y
    -> ComplexMap (Complex x) (Complex y) 

--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance (Show x, Show y) => Show (ComplexMap (Complex x) (Complex y)) where
  show (ComplexMap a b f) = "ComplexMap (" ++ show a ++ ") (" ++ show b ++ ") (VertexMap "
                          ++ show [(v,amap1 f v) | v <- setxs $ cpxVertices a] ++ ")"

instance Eq (ComplexMap (Complex x) (Complex y)) where
  ComplexMap a b f@(OrdMap _) == ComplexMap a' b' f'
    = (a,b,[amap1 f v | v <- vs]) == (a',b',[amap1 f' v | v <- vs])
    where vs = setxs $ cpxVertices a

instance Ord (ComplexMap (Complex x) (Complex y)) where
  compare (ComplexMap a b f@(OrdMap _)) (ComplexMap a' b' f')
    = compare (a,b,[amap1 f $ v | v <- vs a]) (a',b',[amap1 f' v | v <- vs a'])
    where vs = setxs . cpxVertices

instance (Entity x, Entity y) => Validable (ComplexMap (Complex x) (Complex y)) where
  valid (ComplexMap cx cy f@(OrdMap _ )) = Label "ComplexMap" :<=>:
    And [ valid cx
        , valid cy
        , vldMapSet (cpxIndex cy) f (amap1 snd $ setxs $ cpxSetMax cx)
{-        
        , vldElg (Set $ cpxxs cy)
                 (spxDimSets $ join $ amap1 (setxs . smap f . snd) $ setxs $ cpxSetMax cx)
-}
        ]
    where

      smap :: OrdMap x y -> Set (Set x) -> Set (Set y)
      smap f@(OrdMap _) = amap1 (OrdMap $ amap1 f)

      setJoin :: [Set x] -> [x]
      setJoin = join . amap1 setxs

      vldElg :: (Entity y, Ord y) => Set ((Z,Set (Set y))) -> Set ((Z,Set (Set y))) -> Statement
      vldElg cy fx = (fx `isSubSet` cy) :?> Params ["fx":=show (fx `setDifference` cy)]
      
      vldMapSet _ _ [] = SValid
      vldMapSet elg f (ssx:ssxs)
        = And [ vldMap elg f ssx
              , vldMapSet elg f ssxs
              ]

      vldMap _ _ (Set [])         = SValid
      vldMap elg f (Set (sx:sxs)) = case elg $ spxAdjDim $ amap1 f sx of
        Nothing -> False :?> Params ["sx":=show sx]
        Just _  -> vldMap elg f (Set sxs)

instance (Entity x, Entity y) => Entity (ComplexMap (Complex x) (Complex y))
  
--------------------------------------------------------------------------------
-- cpxMapTerminal -

cpxMapTerminal :: Ord x
  => Complex x -> ComplexMap (Complex x) (Complex ())
cpxMapTerminal c = ComplexMap c (cpxTerminal ()) (OrdMap $ const ())

--------------------------------------------------------------------------------
-- cpxMapVertex -

cpxMapVertex :: Ord x
  => x -> Complex x -> Maybe (ComplexMap (Complex ()) (Complex x))
cpxMapVertex x c = case isVertex x c of
  True  -> Just $ ComplexMap (cpxTerminal ()) c (OrdMap $ const x)
  False -> Nothing

--------------------------------------------------------------------------------
Just a = cpxBorder $ complex $ [set "abc"]
Just b = cpxBorder $ complex $ [set [0::N .. 2]]
c = cpxProduct a b

p1 = ComplexMap c a (OrdMap fst)
p2 = ComplexMap c b (OrdMap snd)

u = complex [Set "abe"]
v = complex [Set "abc",Set "bce",Set "ae"]

f = ComplexMap u v (OrdMap id)

