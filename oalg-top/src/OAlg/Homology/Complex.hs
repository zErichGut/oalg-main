
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
import Data.List as L (head,tail,last, groupBy,reverse,(++),span,zip,dropWhile,take,repeat
                      ,takeWhile
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

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.FinList as F hiding ((++))
import OAlg.Entity.Sequence hiding (span)
import OAlg.Entity.Sum

import OAlg.Homology.Simplex

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
-- Complex -

-- | complex over a simplex type @__s__@.
--
--  __Properties__ Let @c = 'Complex' zss@ be in @'Complex' __s__ __x__@ for a 'Simplical'-structure
--  @__s__@, then holds:
--
--  (1) If @zss@ is not empty, then holds: @z0 '==' 0@ where @(z0,_) = 'head' zss@.
--
--  (2) For all @(z,'Set' sxs)@ in @zss@ holds:
--
--    (1) @0 '<=' z@.
--
--    (2) @'dimension' sx '==' z@ for all @sx@ in @sxs@.
--
--  (3) For all @..(_,sxs)':'(_,sxs')..@ holds: @'faces' sx'@ is a sub-list of @sxs@ for all
--      @sx'@ in @sxs'@. 
newtype Complex s x = Complex [(Z,Set (s x))] deriving (Show,Eq,Ord)

instance (Simplical s, Validable (s x), Ord (s x), Show (s x)) => Validable (Complex s x) where
  valid (Complex zss) = Label "Complex" :<=>: case zss of
    []             -> SValid
    ((z,sxs):zss') -> And [ Label "1" :<=>: (z == 0) :?> Params ["z0" := show z]
                          , valid sxs
                          , Label "2.2" :<=>: vldDimension z sxs
                          , Label "3" :<=>: vldFaces z sxs zss'
                          ]
    where
      vldDimension z sxs = (foldl vDim True sxs) :?> Params ["z":=show z, "sxs" := show sxs] where
        vDim b sx = b && (dimension sx == z)

      vldFaces _ _ [] = SValid
      vldFaces z sxs ((z',sxs'):zss')
        = And [ valid sxs'
              , Label "z < z'" :<=>: (z < z') :?> Params ["z":=show z, "z'":=show z']
              , Label "2.2" :<=>: vldDimension z' sxs'
              , vldSubList sxs sxs'
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
-- vertices -

vertices :: Complex s x -> Set (s x)
vertices (Complex [])          = setEmpty
vertices (Complex ((_,sxs):_)) = sxs
  
--------------------------------------------------------------------------------
-- cpxSet -

cpxSet :: Complex s x -> Set (Z,s x)
cpxSet (Complex zsx) = Set $ join $ amap1 (\(z,Set sx) -> amap1 (z,) sx) zsx

--------------------------------------------------------------------------------
-- cpxEmpty -

cpxEmpty :: Complex s x
cpxEmpty = Complex []

--------------------------------------------------------------------------------
-- cpxTerminal -

cpxTerminal :: Simplical s => x -> Complex s x
cpxTerminal v = Complex [(0,Set [vertex v])]

--------------------------------------------------------------------------------
-- complex -

complex :: Simplical s => Set (s x) -> Complex s x
complex (Set [])  = Complex []
complex (Set sxs) = error "nyi"

--------------------------------------------------------------------------------
-- ComplexMap -

-- | /continous mapping/ between complexes.
--
-- __Properties__ Let @'ComplexMap' cx cy f@ be in
-- @'ComplexMap' __c__ __s__ ('Complex' __s__ __x__) ('Complex' __s__ __y__)@ where @__c__@
-- is 'Applicative1' and @__s__@ is 'Simplcal', then holds:
-- For all simplices @s@ in @cx@ holds: @'amap1' f s@ is an element of @cy@.
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
        , vldGraph (isElement (setIndex $ cpxSet y)) $ gphxs $ cpxMapGraph f
        ]
    where
      vldGraph :: (Entity x, Entity y) =>  (y -> Bool) -> [(x,y)] -> Statement
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
{-
--------------------------------------------------------------------------------
-- Complex -

-- | complex as a set of simplices with vertices in @__x__@ such that the list of the faces of each
--   simplex is a sublist of the given set of simplices.
--
-- __Properties__ Let @c = 'Complex' ss@ be in @'Complex' __x__@, then holds:
-- For all simplices @s@ in @ss@ holds:
--
-- (1) @0 '<=' 'spxDim' s@
--
-- (2) if @0 '<' 'spxDim's@ then holds: @'faces' s@ is a sub list of @ss@,
--
-- __Note__ The set of simplices of a complex may be __infinite__! As a example see 'cpxTerminal'.
-- For such complexes use 'cpxCut'.
newtype Complex x = Complex (Set (Simplex x)) deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- cpxCut -

-- | the subcomplex containing all simplices with maximal dimension of the given dimension.
cpxCut :: Z -> Complex x -> Complex x
cpxCut n (Complex (Set ss)) = Complex $ Set $ takeWhile ((<=n).spxDim) $ ss

--------------------------------------------------------------------------------
-- cpxTerminal -

-- | the infinite complex generatet by the given point, i.e
--   @'Simplex' [x],'Simplex' [x,x], 'Simplex' [x,x,x]..@
cpxTerminal :: x -> Complex x
cpxTerminal x = Complex $ Set $ amap1 Simplex $ units x [] where
  units x us = us' : units x us' where us' = x:us 

--------------------------------------------------------------------------------
-- cpxEmpty -

-- | the empty complex.
cpxEmpty :: Complex x
cpxEmpty = Complex setEmpty

--------------------------------------------------------------------------------
-- Complex - Entity -

instance (Entity x, Ord x) => Validable (Complex x) where
  valid (Complex (Set ss)) = Label "Complex" :<=>:
    case ss of
      []   -> SValid
      s:ss -> And [ valid s
                  , Label "0 <= spxDim s" :<=>: valid s && (0 <= spxDim s) :?> Params ["s":=show s] 
                  , vldFaces s
                  , Label "setFaces" :<=>:  vldSetFaces s ss
                  ]
    where
      ssIndex = setIndex (Set ss)


      vldSetFaces _ [] = SValid
      vldSetFaces s (s':ss)
        = And [ valid s'
              , Label "set" :<=>: (s < s') :?> Params ["s":=show s,"s'":=show s']
              , vldFaces s'
              , vldSetFaces s' ss
              ]

      vldFaces s = Label "faces"
        :<=>: if 0 < spxDim s then (And $ amap1 isElement $ faces s) else SValid
        
      isElement s = case ssIndex s of
        Nothing -> SInvalid
        Just _  -> SValid


instance (Entity x, Ord x) => Entity (Complex x)


--------------------------------------------------------------------------------
-- complex -

-- | generates the complex, where all the faces of the given set of simplices are added.
complex :: Ord x => Set (Simplex x) -> Complex x
complex ss
  = Complex
  $ Set
  $ L.tail -- eliminiating the empty simplex
  $ join
  $ reverse
  $ amap1 setxs
  $ adjFaces
  $ reverse -- not expensive, because the dimension is in general very small
  $ amap1 Set
  $ groupBy (~)
  $ setxs ss
  where
    a ~ b = lengthN a == lengthN b

    -- adjFaces ss = ss' adjons to ss all the faces.
    -- pre  : - ss is a list of non-empty simplex-sets having the same dimension an in descending order
    -- post : - ss' is a list of non-empty simplex-sets having the same dimension an in descending
    --          order
    --        - ss' has all the faces adjoint
    --        - ss' is not empty an its last entry is Set [Simplex []]
    adjFaces :: Ord x => [Set (Simplex x)] -> [Set (Simplex x)]
    adjFaces []       = [Set [spxEmpty]]
    adjFaces [s]      = case dim s of
      -1             -> [s]
      0              -> s : [Set [spxEmpty]]
      _              -> s : adjFaces [faces' s]
    adjFaces (s:t:ss) = s : adjFaces ss' where
      fs = faces' s
      
      ss' | dim fs == dim t = fs `setUnion` t : ss
          | otherwise       = fs : t : ss

    dim :: Set (Simplex x) -> Z
    dim (Set (s:_)) = spxDim s
    dim _           = throw $ ImplementationError "complex.dim"
-}




{-
--------------------------------------------------------------------------------
-- cpxSet -

cpxSet :: Complex n x -> Set (Simplex x)
cpxSet (Complex s) = s

--------------------------------------------------------------------------------
-- cpxSets -

cpxSets :: Attestable n => Complex n x -> FinList (n+1) (Set (Simplex x))
cpxSets c@(Complex s) = sts (SW $ cpxAttest c) (amap1 Set $ groupBy (~) $ setxs s) where
  a ~ b = lengthN a == lengthN b

  sts :: Any n -> [Set (Simplex x)] -> FinList n (Set (Simplex x))
  sts n ss = case maybeFinList n (ss ++ L.repeat setEmpty) of
    Just ss' -> ss'
    Nothing  -> throw $ ImplementationError "cpxSets"

--------------------------------------------------------------------------------
-- vertices -

-- | the set of vertices.
vertices :: Attestable n => Complex n x -> Set x
vertices = Set . amap1 (L.head . spxxs) .  setxs . F.head . cpxSets

--------------------------------------------------------------------------------
-- ComplexMap -

-- | _/continous function/_ between complexes, i.e. a mapping of the vertices such that these
--   mapping induces a mapping of the simplces.
--
--   __Property__ Let @'ComplexMap' x y f@ be in
--   @'ComplexMap' __n__ ('Complex' __n__ __x__) ('Complex' __n__ __y__)@, then holds:
--   For all simplices @s@ in @'cpxSet' x@ holds: @'fst '$' 'spxMap' f@ is in @'cpxSet' y@.  
data ComplexMap n a b where
  ComplexMap :: Complex n x -> Complex n y -> (x -> y) -> ComplexMap n (Complex n x) (Complex n y)

--------------------------------------------------------------------------------
-- cpxMapGraphFull -

cpxMapGraphFull :: ComplexMap n (Complex n x) (Complex n y) -> Graph (Simplex x) (Simplex y)
cpxMapGraphFull (ComplexMap x _ f) = Graph [(x,spxMap f x) | x <- setxs $ cpxSet x]

--------------------------------------------------------------------------------
-- cpxMapGraph -

cpxMapGraph :: Attestable n => ComplexMap n (Complex n x) (Complex n y) -> Graph x y
cpxMapGraph (ComplexMap x _ f) = Graph [(v,f v) | v <- setxs $ vertices x]


--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance (Attestable n, Show x, Show y) => Show (ComplexMap n (Complex n x) (Complex n y)) where
  show f@(ComplexMap a b _)
    = "ComplexMap (" ++ show a ++ ") (" ++ show b ++ ") (" ++ (show $ cpxMapGraph f) ++ ")"

instance (Attestable n, Eq x, Eq y) => Eq (ComplexMap n (Complex n x) (Complex n y)) where
  f@(ComplexMap a b _) == g@(ComplexMap a' b' _) = (a,b,cpxMapGraph f) == (a',b',cpxMapGraph g)

instance (Attestable n, Ord x, Ord y) => Ord (ComplexMap n (Complex n x) (Complex n y)) where
  compare f@(ComplexMap a b _) g@(ComplexMap a' b' _)
    = compare (a,b,cpxMapGraph f) (a',b',cpxMapGraph g)

instance (Attestable n, Entity x, Ord x, Entity y, Ord y)
  => Validable (ComplexMap n (Complex n x) (Complex n y)) where
  valid f@(ComplexMap a b _) = Label "ComplexMap" :<=>:
    And [ valid a
        , valid b
        , valid (cpxMapGraph f)
        , vldGraphFull b (cpxMapGraphFull f)
        ]
    where

      vldGraphFull (Complex sy) (Graph assocs) = vld assocs where
        iy = setIndex sy

        vld []                 = SValid
        vld ((x,y):assocs) = case iy y of
          Just _ -> vld assocs
          Nothing -> False :?> Params ["x":=show x,"y":=show y]

instance (Attestable n, Entity x, Ord x, Entity y, Ord y)
  => Entity (ComplexMap n (Complex n x) (Complex n y))

--------------------------------------------------------------------------------
-- cpxMapTerminal -

cpxMapTerminal :: Complex x -> ComplexMap (Complex x) (Complex ())
cpxMapTerminal c = ComplexMap c cpxTerminal (const ())

--------------------------------------------------------------------------------
-- cpxProduct -

-- | the induced simplices with dimension of the sum of the two given simplices.
spxMerge :: (Ord x, Ord y) => Simplex x -> Simplex y -> [Simplex (x,y)]
spxMerge (Simplex (Set xs)) (Simplex (Set ys))
  = amap1 (simplex . merge xs ys) $ [(x,y) | x <- xs, y <- ys]
  where
    merge :: [x] -> [y] -> (x,y) -> [(x,y)]
    merge xs ys (x,y) = amap1 (,y) xs ++ amap1 (x,) ys

cpxProduct :: (Ord x, Ord y) => Complex x -> Complex y -> Complex (x,y)
cpxProduct sxs sys
  = complex
  $ set
  $ join
  $ amap1 (uncurry spxMerge)
  $ [(sx,sy) | sx <- setxs $ last $ cpxSets sxs, sy <- setxs $ last $ cpxSets sys]

--------------------------------------------------------------------------------
-- Space -

data Space where
  Space :: (Entity x, Ord x) => Complex x -> Space

deriving instance Show Space

eqV :: (Typeable x, Typeable y) => Complex x -> Complex y -> Maybe (x :~: y)
eqV _ _ = eqT

instance Eq Space where
  Space x == Space y = case eqV x y of
    Just Refl -> x == y
    Nothing   -> False
{-
instance Ord Space where
  compare (Space x) (Space y) = case eqV x y of
    Just Refl ->
-}

instance Validable Space where valid (Space x) = valid x
instance Entity Space

--------------------------------------------------------------------------------
-- Continous -

data Continous where
  Continous :: (Entity x, Ord x, Entity y, Ord y) => ComplexMap (Complex x) (Complex y) -> Continous

deriving instance Show Continous

instance Eq Continous where
  Continous f@(ComplexMap x y _) == Continous g@(ComplexMap x' y' _)
    = case (eqV x x',eqV y y') of
        (Just Refl, Just Refl) -> f == g
        _                      -> False

instance Validable Continous where valid (Continous f) = valid f

instance Entity Continous

instance Oriented Continous where
  type Point Continous = Space
  orientation (Continous (ComplexMap x y _)) = Space x :> Space y

instance Multiplicative Continous where
  one (Space x) = Continous (ComplexMap x x id)

  Continous (ComplexMap y' z f') * Continous (ComplexMap x y g') = case eqV y' y of
    Just Refl | y' == y -> Continous $ ComplexMap x z (f' . g')
    _                   -> throw NotMultiplicable
  
-}

























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


