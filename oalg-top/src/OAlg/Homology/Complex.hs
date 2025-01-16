
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
    Complex(..), cpxElem, complex
  , cpxVertices, cpxSimplices, cpxGenerators

    -- * Map
  , ComplexMap(..)
  ) where

import Control.Monad

import Data.Typeable
import Data.List as L ((++)) -- head,tail,zip,last,reverse,repeat,(++),span)
import Data.Foldable (foldl)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Filterable

import OAlg.Hom.Distributive ()

import OAlg.Entity.Sequence hiding (span,isEmpty)

import OAlg.Structure.PartiallyOrdered

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- Complex -

-- | complex over a vertex type @__x__@.
--
--  __Properties__ Let @c = 'Complex' ('Graph' zxs)@ be in @'Complex' __x__@, then holds:
--
--  (1) @zxs@ is not empty.
--
--  (2) @z0 '==' -1@ where @(z0,_) = 'head' zxs@.
--
--  (3) For all @(z,'Set' sxs)@ in @zsx@ holds:
--
--     (1) @xsx@ is not empty.
--
--     (2) @'dimension' sx '==' z@ for all @sx@ in @sxs@.
--
--  (4) For all @..(z,su)':'(z',sv)..@ in @zsx@ holds:
--
--    (1) @z' '==' z '+' 1@.
--
--    (2) @'faces'' sv'@ is a subset of @su@.
newtype Complex x = Complex (Graph Z (Set (Set x))) deriving (Show,Eq,Ord)


--------------------------------------------------------------------------------
-- Complex - Set - Entity -

instance (Entity x, Ord x) => Validable (Complex x) where
  valid (Complex (Graph zsx)) = Label "Complex" :<=>: case zsx of
    []            -> Label "1" :<=>: SInvalid
    ((z,sx):zsx') -> And [ Label "2" :<=>: (z == -1) :?> Params ["z0" := show z]
                         , valid sx
                         , vldDimension z sx
                         , vldFaces z sx zsx'
                         ]
    where
      vldDimension z sx
        = And [ Label "3.1" :<=>: (not $ isEmpty sx) :?> Params ["sx":=show sx]
              , Label "3.2" :<=>: let vDim b sx = b && (dimension sx == z) in
                  (foldl vDim True sx) :?> Params ["z":=show z, "sx" := show sx]
              ]

      vldFaces _ _ [] = SValid
      vldFaces z su ((z',sv):zsx')
        = And [ valid sv
              , Label "4.1'" :<=>: (z' == succ z) :?> Params ["z":=show z, "z'":=show z']
              , vldDimension z' sv
              , Label "4.2" :<=>: let fsv = faces' sv in
                  (fsv <<= su) :?> Params ["fsv":=show (fsv // su)]
              , vldFaces z' sv zsx'
              ]
                                
instance (Entity x, Ord x) => Entity (Complex x)

--------------------------------------------------------------------------------
-- cpxSimplices -

-- | the simplices of the given complex.
cpxSimplices :: Complex x -> Graph Z (Set (Set x))
cpxSimplices (Complex g) = g

--------------------------------------------------------------------------------
-- cpxGenerators -

-- | the generators for the given complex.
cpxGenerators :: (Entity x, Ord x) => Complex x -> Graph Z (Set (Set x))
cpxGenerators (Complex g) = g // gphFaces g

--------------------------------------------------------------------------------
-- cpxElem -

-- | checking for being a simplex of the given complex.
cpxElem :: (Entity x, Ord x) => Complex x -> Set x -> Bool
cpxElem (Complex g) = isElem $ setIndex $ gphset g where
  isElem :: (Entity x, Ord x) => ((Z,Set x) -> Maybe n) -> Set x -> Bool
  isElem i = isJust . i . spxAdjDim

cpx :: N -> Complex N
cpx n = complex [Set [1..n]]

--------------------------------------------------------------------------------
-- complex -

-- | the induced complex given by a list of simplices.
complex :: (Entity x, Ord x) => [Set x] -> Complex x
complex = Complex . foldl (||) empty . amap1 simplices

--------------------------------------------------------------------------------
-- cpxVertices -

-- | the set of vertices of the given complex.
cpxVertices :: Complex x -> Set x
cpxVertices (Complex g) = case gphxs g of
  _ : (0,vs) : _ -> Set $ join $ amap1 setxs $ setxs vs
  _              -> Set []

--------------------------------------------------------------------------------
-- cpxProduct -

cpxProduct :: (Entity x, Ord x, Entity y, Ord y) => Complex x -> Complex y -> Complex (x,y)
cpxProduct a b = Complex $ filter (not . isEmpty) $ gphSetFilter (elig a b) gp where
  gp = simplices $ Set [(x,y) | x <- setxs $ cpxVertices a, y <- setxs $ cpxVertices b]

  map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
  map = Map

  elig :: (Entity x, Ord x, Entity y, Ord y) => Complex x -> Complex y -> Set (x,y) -> Bool
  elig a b = (cpxElem a . amap1 (map fst)) && (cpxElem b . amap1 (map snd))


--------------------------------------------------------------------------------
-- ComplexMap -

-- | mapping between complexes, where the underlying map induces a map between the two
-- given simpliex sets.
--
-- __Property__ Let @'ComplexMap' cx cy f@ be in
-- @'ComplexMap' ('Complex' __x__) ('Complex' __y__)@ then holds:
--
-- (1) for all simplices @s@ in @cx@ holds: @'amap1' f s@ is an element of @cy@.
--
-- __Note__ If @cx@ and @cy@ are 'valid' then it is sufficient to test the property on the
-- generators, given by @'cpxGenerators' cx@.
data ComplexMap a b where
  ComplexMap
    :: Complex x -> Complex y
    -> Map EntOrd x y
    -> ComplexMap (Complex x) (Complex y) 


--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance Show (ComplexMap a b) where
  show (ComplexMap a b (Map f))
    = "ComplexMap (" ++ show a ++ ") (" ++ show b ++ ") ("
                     ++ (show $ Graph [(v,f v) | v <- setxs $ cpxVertices a]) ++ ")"

instance Eq (ComplexMap a b) where
  ComplexMap a b (Map f) == ComplexMap a' b' (Map f')
    = (a,b,[f v | v <- vs]) == (a',b',[f' v | v <- vs])
    where vs = setxs $ cpxVertices a

instance Ord (ComplexMap a b) where
  compare (ComplexMap a b (Map f)) (ComplexMap a' b' (Map f'))
    = compare (a,b,[f v | v <- vs a]) (a',b',[f' v | v <- vs a'])
    where vs = setxs . cpxVertices

instance Validable (ComplexMap a b) where
  valid (ComplexMap a b f@(Map _)) = Label "ComplexMap" :<=>:
    And [ valid a
        , valid b
        , Label "1" :<=>: (fa <<= sb) :?> Params ["fa":= show (fa // sb)]
        ]
    where
      fa = setgph $ amap1 (map spxAdjDim . Map (amap1 f) . map snd) $ gphset $ cpxGenerators a
      sb = cpxSimplices b

      map :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> Map EntOrd x y
      map = Map

instance (Typeable a, Typeable b) => Entity (ComplexMap a b)

--------------------------------------------------------------------------------

a = complex [Set "ab",Set "bc",Set "ac"] :: Complex Char
b = complex [Set [0,1],Set [1,2], Set [0,2]] :: Complex N

c = cpxProduct a b

p1 = ComplexMap c a (Map fst)
p2 = ComplexMap c b (Map snd)

  
{-
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

-}

--------------------------------------------------------------------------------
-- ComplexMap - Entity -
{-


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

-}
