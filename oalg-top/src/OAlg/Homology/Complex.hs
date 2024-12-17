
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

import OAlg.Homology.Simplex

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

-- | complex over a simplex type @__s__@.
--
--  __Properties__ Let @c = 'Complex' zss@ be in @'Complex' __s__ __x__@ for a 'Simplical'-structure
--  @__s__@, then holds:
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
newtype Complex s x = Complex [(Z,Set (s x))] deriving (Show,Eq,Ord)

instance (Simplical s, Validable (s x), Ord (s x), Show (s x)) => Validable (Complex s x) where
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

instance (Simplical s, Entity (s x), Ord (s x), Typeable s, Typeable x) => Entity (Complex s x)

--------------------------------------------------------------------------------
-- cpxxs -

cpxxs :: Complex s x -> [(Z,Set (s x))]
cpxxs (Complex zsx) = zsx

--------------------------------------------------------------------------------
-- cpxVertices -

cpxVertices :: Complex s x -> Set (s x)
cpxVertices (Complex [])          = setEmpty
cpxVertices (Complex ((_,sxs):_)) = sxs

--------------------------------------------------------------------------------
-- isVertex -

isVertex :: (Simplical s, Ord (s x))  => x -> Complex s x -> Bool
isVertex x c = isSubSet (Set [vertex x]) (cpxVertices c)

--------------------------------------------------------------------------------
-- cpxSet -

cpxSet :: Complex s x -> Set (Z,s x)
cpxSet (Complex zsx) = Set $ join $ amap1 (\(z,Set sx) -> amap1 (z,) sx) zsx

--------------------------------------------------------------------------------
-- cpxSetMax -

cpxSetMax :: Complex s x -> (Z,Set (s x))
cpxSetMax (Complex [])  = (-1,setEmpty)
cpxSetMax (Complex sxs) = last sxs 

--------------------------------------------------------------------------------
-- cpxEmpty -

cpxEmpty :: Complex s x
cpxEmpty = Complex []

--------------------------------------------------------------------------------
-- cpxTerminal -

cpxTerminal :: Simplical s => x -> Complex s x
cpxTerminal v = Complex [(0,Set [vertex v])]

--------------------------------------------------------------------------------
-- cpxBorder -

cpxBorder :: Complex s x -> Complex s x
cpxBorder (Complex ss) = Complex (dropLast ss) where
  dropLast []     = []
  dropLast [_]    = []
  dropLast (x:xs) = x : dropLast xs
  
--------------------------------------------------------------------------------
-- complex -

complex :: (Simplical s, Ord (s x)) => Set (s x) -> Complex s x
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

    aggrFaces :: (Simplical s, Ord (s x)) => [(Z,Set (s x))] -> [(Z,Set (s x))]
    aggrFaces []            = throw $ ImplementationError "complex.aggrFaces"  
    aggrFaces ((0,sx):_)    = [(0,sx)] -- set of vertices
    aggrFaces ((z,sx):zsxs) = (z,sx) : aggrFaces ((pred z,faces' sx) +> zsxs) where
      (z,sx) +> []              = [(z,sx)]
      (z,sx) +> ((z',sx'):zsxs) = case z == z' of
        True  -> (z',sx `setUnion` sx'):zsxs
        False -> (z,sx):(z',sx'):zsxs

--------------------------------------------------------------------------------
-- cpxVertexSet -

cpxVertexSet :: Complex Set x -> Set x
cpxVertexSet = Set . amap1 (head . setxs) . setxs . cpxVertices

--------------------------------------------------------------------------------
-- cpxProduct -

a = cpxBorder $ complex $ set [set "abc"]
b = cpxBorder $ complex $ set [set [0::N .. 2]]
c = cpxProduct a b
p1 = ComplexMap c a (OrdMap fst)
p2 = ComplexMap c b (OrdMap snd)

cpxProduct :: (Ord x, Ord y) => Complex Set x -> Complex Set y -> Complex Set (x,y)
cpxProduct a b
  = Complex 
  $ spxGroup
  $ filter feasable
  $ subsets
  $ Set [(x,y) | x <- setxs $ cpxVertexSet a, y <- setxs $ cpxVertexSet b]
  where
    ia = setIndex $ cpxSet a
    ib = setIndex $ cpxSet b

    feasable (Set xys)= ((dimension xs,xs) `elem` ia) && ((dimension ys,ys) `elem` ib) where
      xs = set $ amap1 fst xys
      ys = set $ amap1 snd xys

    elem x i = case i x of
      Nothing -> False
      Just _  -> True

--------------------------------------------------------------------------------
-- spxGroup -

spxGroup :: (Simplical s, Ord (s x)) => [s x] -> [(Z,Set (s x))]
spxGroup = amap1 (\ss -> (fst $ head ss, Set $ amap1 snd ss))
         . groupBy (~) . sort
         . amap1 (\s -> (dimension s, s))
  where (d,_) ~ (d',_) = d == d'
  

--------------------------------------------------------------------------------
-- ComplexMap -

-- | /continous mapping/ between complexes.
--
-- __Properties__ Let @'ComplexMap' cx cy f@ be in
-- @'ComplexMap' __c__ __s__ ('Complex' __s__ __x__) ('Complex' __s__ __y__)@ where @__c__@
-- is 'Applicative1' and @__s__@ is 'Simplcal', then for all simplices @s@ in @cx@ holds: 
-- @'amap1' f s@ is an element of @cy@.
data ComplexMap c s a b where
  ComplexMap
    :: (Entity (s x), Ord (s x), Entity (s y), Ord (s y))
    => Complex s x -> Complex s y -> c x y -> ComplexMap c s (Complex s x) (Complex s y) 

--------------------------------------------------------------------------------
-- cpxMapGraph -

cpxMapGraph :: (Applicative1 c s, Simplical s)
  => ComplexMap c s (Complex s x) (Complex s y) -> Graph (Z,s x) (Z,s y)
cpxMapGraph (ComplexMap cx _ f)
  = Graph [((z,x),let y = amap1 f x in (dimension y,y)) | (z,x) <- setxs $ cpxSet cx]

--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance (Applicative1 c s, Simplical s) => Show (ComplexMap c s a b) where
  show f@(ComplexMap _ _ _) = "ComplexMap (" ++ (show $ cpxMapGraph f) ++ ")"

instance (Applicative1 c s, Simplical s) => Eq (ComplexMap c s a b) where
  f@(ComplexMap _ _ _) == g@(ComplexMap _ _ _) = cpxMapGraph f == cpxMapGraph g

instance (Applicative1 c s, Simplical s) => Ord (ComplexMap c s a b) where
  compare f@(ComplexMap _ _ _) g@(ComplexMap _ _ _) = compare (cpxMapGraph f) (cpxMapGraph g)


instance (Applicative1 c s, Simplical s) => Validable (ComplexMap c s a b) where
  valid f@(ComplexMap x y _) = Label "ComplexMap" :<=>:
    And [ valid x
        , valid y
        , vldGraph (isElement (setIndex $ cpxSet y)) (gphxs $ cpxMapGraph f)
        ]
    where
      vldGraph :: (Entity x, Entity y)
        => ((Z,y) -> Bool) -> [((Z,x),(Z,y))] -> Statement
      vldGraph _ []          = SValid
      vldGraph i ((x,y):xsy) = And [ valid x
                                   , valid y
                                   , Label "isElement" :<=>:
                                       (i y) :?> Params ["x":=show x,"y":=show y]
                                   , vldGraph i xsy
                                   ]
                            
      isElement i y = case i y of
        Nothing -> False
        _       -> True

instance ( Applicative1 c s, Simplical s
         , Typeable c, Typeable s, Typeable a, Typeable b
         )
  => Entity (ComplexMap c s a b)

--------------------------------------------------------------------------------
-- cpxMapTerminal -

cpxMapTerminal :: (Entity x, Ord x)
  => Complex Set x -> ComplexMap OrdMap Set (Complex Set x) (Complex Set ())
cpxMapTerminal c = ComplexMap c (cpxTerminal ()) (OrdMap $ const ())


--------------------------------------------------------------------------------
-- cpxMapVertex -

cpxMapVertex :: (Entity x, Ord x)
  => x -> Complex Set x -> ComplexMap OrdMap Set (Complex Set ()) (Complex Set x)
cpxMapVertex x c = case isVertex x c of
  True  -> ComplexMap (cpxTerminal ()) c (OrdMap $ const x)
  False -> throw $ NotAVertex $ show x




  

{-
--------------------------------------------------------------------------------
-- Complex -

-- | complex of dimension @__n__@ over @__x__@.
data Complex n x where
  Vertices :: Set x -> Complex N0 x
  Complex  :: Set (Simplex (S (S n)) x) -> Complex n x -> Complex (S n) x

--------------------------------------------------------------------------------
-- cpxDim -

-- | the dimension of the complex space.
cpxDim :: Complex n x -> Any n
cpxDim (Vertices _)  = W0
cpxDim (Complex _ c) = SW $ cpxDim c

--------------------------------------------------------------------------------
-- cpxSet -

cpxSet :: Complex n x -> Set (Simplex (n+1) x)
cpxSet (Vertices (Set xs))  = Set $ amap1 (Simplex . (:|Nil)) xs
cpxSet (Complex s _)        = s

--------------------------------------------------------------------------------
-- cpxIndex -

cpxIndex :: Ord x => Complex n x -> Simplex (n+1) x -> Maybe N
cpxIndex = setIndex . cpxSet

--------------------------------------------------------------------------------
-- cpxSucc -

cpxSucc :: Complex n x -> Complex (n+1) x
cpxSucc c = Complex setEmpty c

--------------------------------------------------------------------------------
-- cpxPred -

cpxPred :: Complex (n+1) x -> Complex n x
cpxPred (Complex _ c) = c

--------------------------------------------------------------------------------
-- Comlex - Entity -

deriving instance Show x => Show (Complex n x)

deriving instance Eq x => Eq (Complex n x)

instance (Entity x, Ord x) => Validable (Complex n x) where
  valid (Vertices xs) = valid xs
  valid (Complex xs@(Set xs') c') = valid xs && valid c' && vldSimplices 0 xs' (cpxIndex c') where

      vldSimplices :: (Entity x, Ord x)
        => N -> [Simplex (n+1) x] -> (Simplex n x -> Maybe N) -> Statement
      vldSimplices _ [] _      = SValid
      vldSimplices i (s:ss) fs = vldFaces i 0 (faces s) fs && vldSimplices (succ i) ss fs

      vldFaces :: (Entity x, Ord x)
        => N -> N -> FinList m (Simplex n x) -> (Simplex n x -> Maybe N) -> Statement
      vldFaces _ _ Nil _      = SValid
      vldFaces i j (s:|ss) fs = case fs s of
        Just _  -> vldFaces i (succ j) ss fs
        Nothing -> False :?> Params ["index (simplex,face)":=show (i,j), "simplex":=show s]

instance (Entity x, Ord x, Typeable n) => Entity (Complex n x)

--------------------------------------------------------------------------------
-- (<+) -

infixr 5 <+

-- | merging a set of simpliex with a complex.
(<+) :: Ord x => Set (Simplex (n+1) x) -> Complex n x -> Complex n x
Set xs <+ Vertices s' = Vertices (Set (amap1 x xs) `setUnion` s') where
  x :: Simplex N1 x -> x
  x (Simplex x') = F.head x'
s@(Set xs) <+ Complex s' c = Complex s'' (fs <+ c) where
  s'' = s `setUnion` s'
  fs  = set $ join $ amap1 (toList . faces) xs
  
  
--------------------------------------------------------------------------------
-- cpxEmpty -

cpxEmpty :: Attestable n => Complex n x
cpxEmpty = ce attest where
  ce :: Any n -> Complex n x
  ce W0 = Vertices setEmpty
  ce (SW n) = Complex setEmpty (ce n)

-------------------------------------------------------------------------------
-- complex -

-- | generates a complex by the given set of simplices.
complex :: (Ord x, Attestable n) => Set (Simplex (n+1) x) -> Complex n x
complex s = s <+ cpxEmpty

--------------------------------------------------------------------------------
-- ComplexMap -

-- | /continous/ mapping between two complexes, i.e. the underlying mappin induces a mapping between
--  the simplices of the given complexes.
--
--  __Property__ Let @f = 'ComplexMap' a b f'@ be in @'ComplexMap' __x__ __y__@, then holds:
--
data ComplexMap x y where
  ComplexMap
    :: ( Ord x, Entity x, Attestable n
       , Ord y, Entity y, Attestable m
       )
     => Complex n x -> Complex m y -> (x -> y) -> ComplexMap x y


{-

--------------------------------------------------------------------------------
-- cpxOrd -

cpxOrd :: Simplical s x => Complex s n x -> Struct Ord' (s n x)
cpxOrd _ = sOrd


--------------------------------------------------------------------------------
-- cpxHomBoundary -

cpxHomBoundary :: (Ring r, Commutative r, Entity x, Ord x, Attestable n)
  => Complex (n+1) x -> Representable r (HomBoundary r) (Chain r (n+1) x) (Chain r n x)
cpxHomBoundary (Complex sn' c) = Representable HomBoundary sn' (cpxSet c)

cpxHomBoundary' :: (Ring r, Commutative r, Entity x, Ord x, Attestable n)
  => p r -> Complex (n+1) x -> Representable r (HomBoundary r) (Chain r (n+1) x) (Chain r n x)
cpxHomBoundary' _ = cpxHomBoundary
-}


--------------------------------------------------------------------------------
-- triangle -

-- | triangle given by the three points.
trn :: v -> v -> v -> Simplex N3 v
trn a b c = Simplex (a:|b:|c:|Nil)

-- | the square devided into two simplices.
--
-- @
--    c ---> d
--    ^    ^ ^
--    |   /  |
--    |  /   | 
--    | /    |
--    a ---> b
-- @
ru :: v -> v -> v -> v -> [Simplex N3 v]
ru a b c d = [trn a c d, trn a b d]

-- | the square devided into two simplices.
--
-- @
--    c ---> d
--    ^    ^ |
--    |   /  |
--    |  /   | 
--    | /    v
--    a ---> b
-- @
rd :: v -> v -> v -> v -> [Simplex N3 v]
rd a b c d = [trn a c d, trn a d b]

-- | the square devided into two simplices.
--
-- @
--    c <--- d
--    ^    ^ ^
--    |   /  |
--    |  /   | 
--    | /    |
--    a ---> b
-- @
lu :: v -> v -> v -> v -> [Simplex N3 v]
lu a b c d = [trn a d c, trn a b d]

-- | the square devided into two simplices.
--
-- @
--    c <--- d
--    ^    ^ |
--    |   /  |
--    |  /   | 
--    | /    v
--    a ---> b
-- @
ld :: v -> v -> v -> v -> [Simplex N3 v]
ld a b c d = [trn a d c, trn a d b]


-- | the simplex-set of the triangle given by the tree points.
triangle :: v -> v -> v -> Set (Simplex N3 v)
triangle a b c = Set [trn a b c]

--------------------------------------------------------------------------------
-- segment -

segment :: v -> v -> Set (Simplex N2 v)
segment a b = Set [Simplex (a:|b:|Nil)]

--------------------------------------------------------------------------------
-- plane -

pln :: [a] -> [b] -> [Simplex N3 (a,b)]
pln as bs = plnas as bs where
  
  plnas (a0:a1:as') bs@(b0:b1:_)
    = trn (a0,b0) (a1,b0) (a1,b1) : trn (a0,b0) (a0,b1) (a1,b1) : plnas (a1:as') bs
  plnas [_] (_:b1:bs) = plnas as (b1:bs)
  plnas _ _           = []

plane :: (Ord a, Ord b) => Set a -> Set b -> Set (Simplex N3 (a,b))
plane (Set as) (Set bs) = set $ pln as bs

--------------------------------------------------------------------------------
-- torus -

torus :: (Ord a, Ord b) => Set a -> Set b -> Set (Simplex N3 (a,b))
torus (Set as) (Set bs) = set $ pln (join [as,[L.head as]]) (join [bs,[L.head bs]]) 


--------------------------------------------------------------------------------
-- sphere -

sphere :: (Enum v, Ord v) => Any n -> v -> Set (Simplex (n+1) v)
sphere n v = set $ toList $ faces $ simplex (SW n) v

--------------------------------------------------------------------------------
-- torus2 -

torus2 :: Set (Simplex N3 Symbol)
torus2 = set $ join
  [ ru A B D F, ru B C F G, ru C A G D
  , ru D F E H, ru F G H I, ru G D I E
  , ru E H A B, ru H I B C, ru I E C A
  ]

--------------------------------------------------------------------------------
-- projectivePlane -

projectivePlane :: Set (Simplex N3 Symbol)
projectivePlane = set $ join
  [ ru V A C E, ru A B E F, rd B W F D
  , ru C E D G, ru E F G H, rd F D H C
  , lu D G W B, lu G H B A, ld H C A V
  ]

--------------------------------------------------------------------------------
-- kleinBottle -

kleinBottle :: Set (Simplex N3 Symbol)
kleinBottle = set $ join
  [ ru A B D F, ru B C F G, rd C A G E
  , ru D F E H, ru F G H I, rd G E I D
  , ru E H A B, ru H I B C, rd I D C A
  ]

--------------------------------------------------------------------------------
-- moebiusStrip -

moebiusStrip :: Set (Simplex N3 Symbol)
moebiusStrip = set $ join
  [ ru A B E F, ru B C F G, ru C D G H
  , ru E F I J, ru F G J K, ru G H K L
  , lu I J D C, lu J K C B, lu K L B A
  ]

--------------------------------------------------------------------------------
-- dunceHat -

dh0 :: Set (Simplex N3 Symbol)
dh0 = Set [trn A A A]

dh1 :: Set (Simplex N3 Symbol)
dh1 = set [trn A B B, trn B B B, trn B A B, trn B B A]

dh2 :: Set (Simplex N3 Symbol)
dh2 = set
  [ trn A B C, trn B C D, trn B A D
  , trn A C B, trn C E B, trn E B A
  , trn A D B, trn D B E, trn B E A
  , trn C D E
  ]
-}


