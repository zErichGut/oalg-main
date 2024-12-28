
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
    Complex(..), complex, cpxSet
{-    
    -- * Complex
    Complex(..)
  , cpxDim
  , cpxSet, cpxSucc, cpxPred
  , cpxIndex
  -- , cpxHomBoundary, cpxHomBoundary'

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

import Data.Typeable
import Data.List as L (head,tail,last,sort,group,sortBy,groupBy,reverse,(++),span,zip
                      ,dropWhile,take,repeat,takeWhile,filter
                      )
import Data.Foldable (toList,foldl,foldr)
import Data.Maybe

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Symbol hiding (S)

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Number.Definition (mod)


import OAlg.Hom.Distributive ()

import OAlg.Entity.Sequence hiding (span)
import OAlg.Entity.Sum

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

deriving instance (Ord i, Ord x) => Ord (Graph i x)

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
-- ComplexException -

data ComplexException
  = NotAVertex String
  deriving (Show)

instance Exception ComplexException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- Complex -

-- | complex over a vertex type @__x__@.
--
--  __Properties__ Let @c = 'Complex' zss@ be in @'Complex' __x__@, then holds:
--
--  (1) If @zss@ is not empty, then holds: @z0 '==' 0@ where @(z0,_) = 'head' zss@.
--
--  (2) For all @(z,'Set' sxs)@ in @zss@ holds: @'dimension' sx '==' z@ for all @sx@ in @sxs@.
--
--  (3) For all @..(z,sxs)':'(z',sxs')..@ holds:
--
--    (1) @z' '==' z'+'1@
--
--    (2) @'faces' sx'@ is a sub-list of @sxs@ for all @sx'@ in @sxs'@.
newtype Complex x = Complex [(Z,Set (Set x))] deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- Complex - Set - Entity -

instance (Entity x, Ord x) => Validable (Complex x) where
  valid (Complex zss) = Label "Complex" :<=>: case zss of
    []             -> SValid
    ((z,sxs):zss') -> And [ Label "1" :<=>: (z == 0) :?> Params ["z0" := show z]
                          , valid sxs
                          , vldDimension z sxs
                          , vldFaces z sxs zss'
                          ]
    where
      vldDimension z sxs = Label "2" :<=>:
        (foldl vDim True sxs) :?> Params ["z":=show z, "sxs" := show sxs]
          where vDim b sx = b && (dimension sx == z)

      vldFaces _ _ [] = SValid
      vldFaces z sxs ((z',sxs'):zss')
        = And [ valid sxs'
              , Label "3.1'" :<=>: (z' == succ z) :?> Params ["z":=show z, "z'":=show z']
              , vldDimension z' sxs'
              , Label "3.2" :<=>: vldSubList sxs sxs'
              , vldFaces z' sxs' zss'
              ]


      vldSubList sxs sxs' = foldl isSubList SValid sxs' where
        i = setIndex sxs
        isSubList v sx = v && foldl isElement SValid (faces sx)

        isElement v f = v && case i f of
          Nothing -> SInvalid
          _       -> SValid

instance (Entity x, Ord x) => Entity (Complex x)

--------------------------------------------------------------------------------
-- cpxxs -

cpxxs :: Complex x -> [(Z,Set (Set x))]
cpxxs (Complex zsx) = zsx

--------------------------------------------------------------------------------
-- cpxVertices -

cpxVertices :: Complex x -> Set (Set x)
cpxVertices (Complex [])          = setEmpty
cpxVertices (Complex ((_,sxs):_)) = sxs

--------------------------------------------------------------------------------
-- isVertex -

isVertex :: Ord x  => x -> Complex x -> Bool
isVertex x c = Set [vertex x] `isSubSet` cpxVertices c

--------------------------------------------------------------------------------
-- cpxSet -

cpxSet :: Complex x -> Set (Z,Set x)
cpxSet (Complex zsx) = Set $ join $ amap1 (\(z,Set sx) -> amap1 (z,) sx) zsx

--------------------------------------------------------------------------------
-- cpxCards -

cpxCards :: Complex x -> [(Z,N)]
cpxCards (Complex zsx) = amap1 (\(z,s) -> (z,lengthN s)) zsx

--------------------------------------------------------------------------------
-- cpxSetMax -

cpxSetMax :: Complex x -> (Z,Set (Set x))
cpxSetMax (Complex [])  = (-1,setEmpty)
cpxSetMax (Complex sxs) = last sxs 

--------------------------------------------------------------------------------
-- cpxEmpty -

cpxEmpty :: Complex x
cpxEmpty = Complex []

--------------------------------------------------------------------------------
-- cpxTerminal -

cpxTerminal :: x -> Complex x
cpxTerminal x = Complex [(0,Set [Set [x]])]

--------------------------------------------------------------------------------
-- cpxBorder -

cpxBorder :: Complex x -> Complex x
cpxBorder (Complex ss) = Complex (dropLast ss) where
  dropLast []     = []
  dropLast [_]    = []
  dropLast (x:xs) = x : dropLast xs

--------------------------------------------------------------------------------
-- complex -

complex :: Ord x => Set (Set x) -> Complex x
complex (Set []) = Complex []
complex (Set sxs)
  = Complex
  $ reverse
  $ aggrFaces
  $ reverse
  $ amap1 (\zsxs -> (fst $ head zsxs,Set $ amap1 snd zsxs))
  $ groupBy (~) $ sort
  $ amap1 (\sx -> (dimension sx,sx)) sxs

  where
    (z,_) ~ (z',_) = z == z'

    aggrFaces :: Ord x => [(Z,Set (Set x))] -> [(Z,Set (Set x))]
    aggrFaces []            = throw $ ImplementationError "complex.aggrFaces"  
    aggrFaces ((0,sx):_)    = [(0,sx)] -- set of vertices
    aggrFaces ((z,sx):zsxs) = (z,sx) : aggrFaces ((pred z,faces' sx) +> zsxs) where
      (z,sx) +> []              = [(z,sx)]
      (z,sx) +> ((z',sx'):zsxs) = case z == z' of
        True  -> (z',sx `setUnion` sx'):zsxs
        False -> (z,sx):(z',sx'):zsxs

--------------------------------------------------------------------------------
-- cpxVertexSet -

cpxVertexSet :: Complex x -> Set x
cpxVertexSet = Set . amap1 (head . toList) . setxs . cpxVertices

--------------------------------------------------------------------------------
-- cpxProduct -

a = cpxBorder $ complex $ set [set "abc"]
b = cpxBorder $ complex $ set [set [0::N .. 2]]
c = cpxProduct a b

p1 = ComplexHom c a (OrdMap fst)
p2 = ComplexHom c b (OrdMap snd)

cpxProduct :: (Ord x, Ord y) => Complex x -> Complex y -> Complex (x,y)
cpxProduct a b
  = Complex
  $ filter ((/= setEmpty) . snd)
  $ spxFilter (feasable . snd)
  $ subsets
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
-- ComplexHom -

-- | homomorphism between complexes, where the underlying function induces a map between the two
-- given sets.
--
-- __Properties__ Let @'ComplexHom' cx cy f@ be in
-- @'ComplexHom' ('Complex' __x__) ('Complex' __y__)@ then for all simplices @s@ in @cx@ holds: 
-- @'amap1' f s@ is an element of @cy@.
data ComplexHom a b where
  ComplexHom
    :: Complex x -> Complex y
    -> OrdMap x y
    -> ComplexHom (Complex x) (Complex y) 

--------------------------------------------------------------------------------
-- cpxMapGraph -

cpxMapGraph :: ComplexHom (Complex x) (Complex y) -> Graph (Z,Set x) (Z,Set y)
cpxMapGraph (ComplexHom cx _ f)
  = Graph [((z,x),let y = amap1 f x in spxAdjDim y) | (z,x) <- setxs $ cpxSet cx]

--------------------------------------------------------------------------------
-- cpxMapStructOrd -

cpxMapStructOrd :: ComplexHom (Complex x) (Complex y) -> (Struct Ord' x,Struct Ord' y)
cpxMapStructOrd (ComplexHom _ _ (OrdMap _)) = (Struct,Struct)

--------------------------------------------------------------------------------
-- ComplexHom - Entity -

instance (Show x, Show y) => Show (ComplexHom (Complex x) (Complex y)) where
  show f = "ComplexHom (" ++ (show $ cpxMapGraph f) ++ ")"

instance Eq (ComplexHom (Complex x) (Complex y)) where
  f == g = case cpxMapStructOrd f of (Struct,Struct) -> cpxMapGraph f == cpxMapGraph g

instance Ord (ComplexHom (Complex x) (Complex y)) where
  compare f g = case cpxMapStructOrd f of (Struct,Struct) -> compare (cpxMapGraph f) (cpxMapGraph g)
  

instance (Entity x, Entity y) => Validable (ComplexHom (Complex x) (Complex y)) where
  valid f@(ComplexHom x y _) = case cpxMapStructOrd f of
    (Struct,Struct) -> Label "ComplexHom" :<=>:
                         And [ valid x
                             , valid y
                             , vldGraph (isElement (setIndex $ cpxSet y)) (gphxs $ cpxMapGraph f)
                             ]
    where
      vldGraph :: (Entity x, Ord x, Entity y, Ord y)
        => ((Z,Set y) -> Bool) -> [((Z,Set x),(Z,Set y))] -> Statement
      vldGraph _ []          = SValid
      vldGraph i ((x,y):xys) = And [ valid x
                                   , valid y
                                   , Label "isElement" :<=>:
                                       (i y) :?> Params ["x":=show x,"y":=show y]
                                   , vldGraph i xys
                                   ]
                               
      isElement i y = case i y of
        Nothing -> False
        _       -> True

instance (Entity x, Entity y) => Entity (ComplexHom (Complex x) (Complex y))

--------------------------------------------------------------------------------
-- cpxHomTerminal -

cpxHomTerminal :: Ord x
  => Complex x -> ComplexHom (Complex x) (Complex ())
cpxHomTerminal c = ComplexHom c (cpxTerminal ()) (OrdMap $ const ())


--------------------------------------------------------------------------------
-- cpxHomVertex -

cpxHomVertex :: Ord x
  => x -> Complex x -> Maybe (ComplexHom (Complex ()) (Complex x))
cpxHomVertex x c = case isVertex x c of
  True  -> Just $ ComplexHom (cpxTerminal ()) c (OrdMap $ const x)
  False -> Nothing








  

