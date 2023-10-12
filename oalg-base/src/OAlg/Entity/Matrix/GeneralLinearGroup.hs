
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Matrix.GeneralLinearGroup
-- Description : general linear group and elementary transformations
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- general linear group 'GL' and elementary transformations over a 'Galoisian' structure.
module OAlg.Entity.Matrix.GeneralLinearGroup
  (
    -- * Transformation
    Transformation(..)

    -- * GL
  , GL, GL2(..)

    -- * GLT
  , GLT()
  , permute, permuteFT
  , scale, shear
  , rdcGLTForm
  
  , GLTForm, gltfTrsp

    -- * FT
  , FT
  
    -- * Homomorphism
    
    -- ** Ort
  , TrApp(..)
  , trGLT
  
    -- ** Mlt
  , GLApp(..)

  )

  where

import Control.Monad hiding (sequence)

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude hiding (T)

import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Canonical
import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Number
import OAlg.Structure.Exponential
import OAlg.Structure.Operational

import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative

import OAlg.Entity.Product
import OAlg.Entity.Sequence

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Definition

--------------------------------------------------------------------------------
-- GL -

-- | general linear groupoid of matrices.
type GL x = Inv (Matrix x)

--------------------------------------------------------------------------------
-- GL2 -

-- | the general linear group of @2x2@ matrices for a 'Galoisian' structure @__x__@.
--
--  __Property__ Let @'GL2' s t u v@ be in @t'GL2' __x__@ for a 'Galoisian' structure
--  @__x__@, then holds: @s'*'v '-' u'*'t@ is invertible.
--
--  __Example__ Let @g = 'GL2' 3 5 4 7 :: 'GL2' 'Z'@:
--
--  >>> invert g
-- GL2 7 -5 -4 3
--
-- >>> g * invert g
-- GL2 1 0 0 1
--
-- which is the 'one' in @'GL2' 'Z'@.
--
--  __Note__
--
--  @'GL2' (s t u v)@ represents the @2x2@-matrix
--
-- @
--    [s t]
--    [u v]
-- @
--
-- and is obtained by 'GL2GL'.
data GL2 x = GL2 x x x x deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- gl2Det -

-- | the determinate of a galoisian matrix.
gl2Det :: Galoisian x => GL2 x -> x
gl2Det (GL2 s t u v) = s*v - u*t

--------------------------------------------------------------------------------
-- gl2GL -

-- | the associate invertible @2x2@-matrix.
gl2GL :: Galoisian x => GL2 x -> GL x
gl2GL g = Inv (gl g) (gl $ invert g) where
  gl (GL2 s t u v) = Matrix d d (Entries (PSequence xs)) where
    d = dim unit ^ 2
    xs = [(s,(0,0)),(t,(0,1)),(u,(1,0)),(v,(1,1))]

--------------------------------------------------------------------------------
-- GL2 - Cayleyan -

instance Galoisian x => Validable (GL2 x) where
  valid g@(GL2 s t u v)
    = And [ valid (s,t,u,v)
          , Label "det" :<=>: isInvertible (gl2Det g) :?> Params ["g":=show g] 
          ]

instance Galoisian x => Entity (GL2 x)

instance Galoisian x => Oriented (GL2 x) where
  type Point (GL2 x) = Point x
  orientation _ = unit :> unit

instance Galoisian x => Total (GL2 x)

instance Galoisian x => Multiplicative (GL2 x) where
  one p = GL2 o z z o where
    o = one p
    z = zero (p:>p)

  GL2 s t u v * GL2 s' t' u' v' = GL2 (s*s' + t*u') (s*t' + t*v')
                                      (u*s' + v*u') (u*t' + v*v')

instance Galoisian x => Invertible (GL2 x) where
  tryToInvert g@(GL2 s t u v) = do
    r <- tryToInvert (gl2Det g)
    return (GL2 (r*v) (negate (r*t)) (negate (r*u)) (r*s))

instance Galoisian x => Cayleyan (GL2 x)

instance Galoisian x => Exponential (GL2 x) where
  type Exponent (GL2 x) = Z
  (^) = zpower

instance (Galoisian x, TransposableDistributive x) => Transposable (GL2 x) where
  transpose (GL2 s t u v) = GL2 (trs s) (trs u) (trs t) (trs v) where trs = transpose

instance (Galoisian x, TransposableDistributive x) => TransposableOriented (GL2 x)
instance (Galoisian x, TransposableDistributive x) => TransposableMultiplicative (GL2 x)

--------------------------------------------------------------------------------
-- gl2ScaleRow1 -

-- | scaling the first row.
gl2ScaleRow1 :: Galoisian x => Inv x -> GL2 x -> GL2 x
gl2ScaleRow1 (Inv x _) (GL2 s t u v) = GL2 (x*s) (x*t) u v

--------------------------------------------------------------------------------
-- gl2ScaleRow2 -

-- | scaling the second row.
gl2ScaleRow2 :: Galoisian x => Inv x -> GL2 x -> GL2 x
gl2ScaleRow2 (Inv x _) (GL2 s t u v) = GL2 s t (x*u) (x*v)

--------------------------------------------------------------------------------
-- gl2ScaleCol1 -

-- | scaling the first column.
gl2ScaleCol1 :: Galoisian x => GL2 x -> Inv x -> GL2 x
gl2ScaleCol1 (GL2 s t u v) (Inv x _) = GL2 (s*x) t (u*x) v

--------------------------------------------------------------------------------
-- gl2ScaleCol2 -

-- | scaling the second column.
gl2ScaleCol2 :: Galoisian x => GL2 x -> Inv x -> GL2 x
gl2ScaleCol2 (GL2 s t u v) (Inv x _) = GL2 s (t*x) u (v*x)


--------------------------------------------------------------------------------
-- Transformation -

-- | elementary linear transformation over a 'Distributive' structure @__x__@.
--
-- __Property__ Let @f@ be in @'Transformation' __x__@ then holds:
--
-- (1) If @f@ matches @'Permute' r c p@ then holds:
--
--         (1) @h '<=' 'It' n@ where @(_,h) = 'span' 'nProxy' p@ and @n = 'lengthN' c@.
--
--         (2) @r '==' c '<*' p@.
--
-- (2) If @f@ matches @'Scale' d k s@ then holds:
--
--     (1) @k '<' 'lengthN' d@.
--
--     (2) @s@ is an endo at @d '?' k@.
--
--     (3) @s@ is 'valid'.
--
-- (3) If @f@ matches @'Shear' d k l g@ then holds:
--
--     (1) @k '<' 'lengthN' d@ and @l '<' 'lengthN' d@.
--
--     (2) @k '<' l@.
--
--     (3) @g@ is 'valid'.
--
--
-- __Note__ @'Shear' d k l ('GL2' s t u v)@ represents the square matrix @m@ of dimension @d@
-- where @m k k '==' s@, @m k l '==' t@, @m l k '==' u@, @m l l '==' v@ and
-- for all @i, j@ not in @[k,l]@ holds: If @i '/=' j@ then @m i j@ is 'zero' else @m i i@
-- is 'one'.
data Transformation x where
  Permute :: Distributive x
    => Dim x (Point x) -> Dim x (Point x) -> Permutation N -> Transformation x
  Scale :: Distributive x => Dim x (Point x) -> N -> Inv x -> Transformation x
  Shear :: Galoisian x => Dim x (Point x) -> N -> N -> GL2 x -> Transformation x

--------------------------------------------------------------------------------
-- Transformation - Entity -

deriving instance Eq (Transformation x)
deriving instance Show (Transformation x)

instance Validable (Transformation x) where
  valid (Permute r c p) = Label "Permute" :<=>:
    And [ valid (r,c,p)
        , Label "1.1" :<=>: let {(_,h) = span nProxy p; n = lengthN c} in
            (h <= It n) :?> Params["h":=show h,"n":=show n]
        , Label "1.2" :<=>: (r == c <* p) :?> Params["r":=show r,"c":=show c,"p":=show p]
        ]
  valid (Scale d k s) = Label "Scale" :<=>:
    And [ valid (d,k)
        , Label "2,1" :<=>: let n = lengthN d in
            (k < n):?>Params["d":=show d,"lengthN d":=show n]
        , Label "2.2" :<=>: isEndoAt (d?k) s :?>Params ["s":=show s]
        , Label "2.3" :<=>: valid s
        ]
  valid (Shear d k l g) = Label "Shear" :<=>:
    And [ valid (d,k,l)
        , Label "3.1" :<=>: let n = lengthN d in
            And [ (k < n):?>Params["d":=show d,"lengthN d":=show n]
                , (l < n):?>Params["l":=show l,"lengthN d":=show n]
                ]
        , Label "3.2":<=>: (k < l):?>Params["(k,l":=show (k,l)]
        , Label "3.3" :<=>: valid g
        ]

instance Typeable x => Entity (Transformation x)

--------------------------------------------------------------------------------
-- Transformation - Oriented -

instance Oriented x => Oriented (Transformation x) where
  type Point (Transformation x) = Dim x (Point x)
  orientation tr = case tr of
    Permute r c _ -> c :> r
    Scale d _ _   -> d :> d
    Shear d _ _ _ -> d :> d

--------------------------------------------------------------------------------
-- trmtx -

-- | associated matrix of a transformation.
trmtx :: Transformation x -> Matrix x

trmtx (Permute r c p) = Matrix r c os where
  os = crets ((mtxColRow $ one c) <* p)

trmtx (Scale d k s) = matrix d d ((inj s,k,k):os) where
  os = [(one p,i,i) | (p,i) <- dimxs d, i /= k]

trmtx (Shear d k l (GL2 s t u v))= matrix d d (xs ++ os) where
  xs = [(s,k,k),(t,k,l),(u,l,k),(v,l,l)]
  os = [(one p,i,i) | (p,i) <- dimxs d, i /= k, i /= l]

--------------------------------------------------------------------------------
-- trInverse -

-- | the formal inverse of a transformation.
trInverse :: Transformation x -> Transformation x
trInverse (Permute r c p) = Permute c r (invert p)
trInverse (Scale d k s)   = Scale d k (invert s)
trInverse (Shear d k l g) = Shear d k l (invert g)

--------------------------------------------------------------------------------
-- trGL -

-- | the associated invertible matrix.
trGL :: Transformation x -> GL x
trGL t = Inv (trmtx t) (trmtx $ trInverse t)

--------------------------------------------------------------------------------
-- rdcPower -

-- | pre: if z /= 1 then f is an endo.
rdcPower :: Transformation x -> Z -> Rdc (Transformation x)
rdcPower f 1         = return f
rdcPower f z | z < 0 = rdcPower (trInverse f) (abs z)
rdcPower f z         = let n = prj z :: N in case f of
  Permute r c p -> reducesTo $ Permute r c (npower p n)
  Scale d k s   -> reducesTo $ Scale d k (npower s n)
  Shear d k l g -> reducesTo $ Shear d k l (npower g n)

--------------------------------------------------------------------------------
-- rdcTransformations -

-- | reducing transformations.
rdcTransformations :: Word Z (Transformation x) -> Rdc (Word Z (Transformation x))
rdcTransformations (Word fs) = rdcTrafos fs >>= return . Word where
  rdcTrafos fs = case fs of
    (_,0):fs' -> reducesTo fs' >>= rdcTrafos
  
    (f,z):fs' | z /= 1 -> do
      fs'' <- rdcTrafos fs'
      f'   <- rdcPower f z
      rdcTrafos ((f',1):fs'')

    (Permute _ _ p,_):fs' | p == one () -> reducesTo fs' >>= rdcTrafos
    (Permute r _ p,1):(Permute _ c q,1):fs'
      -> reducesTo (Permute r c (q * p))
         >>= \f -> rdcTrafos ((f,1):fs')
  
    (Scale d k s,_):fs' | s == one (d?k) -> reducesTo fs' >>= rdcTrafos
    (Scale d k s,1):(Scale _ k' t,1):fs' | k == k'
      -> reducesTo (Scale d k (s * t))
         >>= \f -> rdcTrafos ((f,1):fs')

    (Shear _ _ _ g,_):fs' | isOne g -> reducesTo fs' >>= rdcTrafos
    (Shear d k l g,1):(Shear _ k' l' h,1):fs' | (k,l) == (k',l')
      -> reducesTo (Shear d k l (g * h))
         >>= \f -> rdcTrafos ((f,1):fs')

    (Scale _ k' r,1):(Shear d k l g,1):fs'
      | k' == k -> reducesTo (Shear d k l $ gl2ScaleRow1 r g)
                   >>= \f -> rdcTrafos ((f,1):fs')
      | k' == l -> reducesTo (Shear d k l $ gl2ScaleRow2 r g)
                   >>= \f -> rdcTrafos ((f,1):fs')

    (Shear d k l g,1):(Scale _ k' r,1):fs'
      | k == k' -> reducesTo (Shear d k l $ gl2ScaleCol1 g r)
                   >>= \f -> rdcTrafos ((f,1):fs')
      | l == k' -> reducesTo (Shear d k l $ gl2ScaleCol2 g r)
                   >>= \f -> rdcTrafos ((f,1):fs')

    fz:fs' -> rdcTrafos fs' >>= return . (fz:)
       
    _ -> return fs

--------------------------------------------------------------------------------
-- trTrsp -

-- | transposition of a elementary transformation.
trTrsp :: TransposableDistributive r => Transformation r -> Transformation r
trTrsp tr = case tr of
  Permute r c p       -> Permute c r (invert p)
  Scale d k s         -> Scale d k (transpose s)
  Shear d k l g       -> Shear d k l (transpose g)

--------------------------------------------------------------------------------
-- GLTForm -

-- | form of 'GLT'.
type GLTForm x = ProductForm Z (Transformation x)

--------------------------------------------------------------------------------
-- rdcGLTForm -

-- | reduces a @'GLTForm' __x__@ to its normal form.
--
--  __Property__ Let @f@ be in @'GLTForm' __x__@ for a 'Oriented' structure @__x__@,
--  then holds:
--
--  (1) @'rdcGLTForm' ('rdcGLTForm' f) '==' 'rdcGLTForm' f@.
--
--  (2) For all exponents @z@ in @'rdcGLTForm' f@ holds: @0 '<' z@.
rdcGLTForm :: Oriented x => GLTForm x -> GLTForm x
rdcGLTForm = prfReduceWith rdcTransformations

--------------------------------------------------------------------------------
-- FT -

-- | the free groupoid of 'Transformation's.
type FT x = Product Z (Transformation x)

--------------------------------------------------------------------------------
-- GLT -

-- | quotient groupoid of the free groupoid of 'Transformation' (see 'FTGLT') given by the
-- relations:
--
-- * @'permuteFT' d c p '*' 'permuteFT' b a q ~ 'permuteFT' d a (q'*'p)@ where @b '==' c@
-- and @'Permute' d c p@, @'Permute' b a q@ are 'valid' (Note: the permutations @p@ and
-- @q@ are switched on the right side of the equation).
--
-- * ...
--
-- __Property__ Let @g@ be in 'GLT', then holds:
--
-- (1) For all exponents @z@ in @'form' g@ holds: @0 '<' z@.
--
-- __Example__ Let @d = 'dim' [()] '^' 10 :: t'Dim'' t'Z'@,
-- @a = 'permuteFT' d d ('swap' 2 8)@, @b = 'permuteFT' d d ('swap' 2 3)@ and
-- @c = 'permuteFT' d d ('swap' 2 3 * 'swap' 2 8)@ then:
--
-- >>> a * b == c
-- False
--
-- but in 'GLT' holds: let @a' = 'amap' 'FTGLT' a@, @b' = 'amap' 'FTGLT' b@ and
-- @c' = 'amap' 'FTGLT' c@ in
--
-- >>> a' * b' == c'
-- True
--
-- and 
--
-- >>> amap GLTGL (a' * b') == amap GLTGL a' * amap GLTGL b'
-- True
--
-- __Note__: As a consequence of the property (1.), 'GLT' can be canonically embedded
-- via @'prj' '.' 'form'@ - in to @'ProductForm' 'N' ('Transformation' x)@. 
newtype GLT x = GLT (GLTForm x) deriving (Eq,Show,Validable,Entity)

--------------------------------------------------------------------------------
-- GLT - Constructable -

instance Exposable (GLT x) where
  type Form (GLT x) = GLTForm x
  form (GLT f) = f
  
instance Oriented x => Constructable (GLT x) where
  make = GLT . rdcGLTForm

instance Embeddable (GLT x) (ProductForm N (Transformation x)) where
  inj = prj . form
  
--------------------------------------------------------------------------------
-- trGLT -

-- | the induced element of the groupoid 'GLT'.
trGLT :: Oriented x => Transformation x -> GLT x
trGLT = make . P

--------------------------------------------------------------------------------
-- GLT - Multiplictive -

instance Oriented x => Oriented (GLT x) where
  type Point (GLT x) = Dim x (Point x)
  orientation = restrict orientation

instance Oriented x => Multiplicative (GLT x) where
  one d = GLT (One d)
  GLT f * GLT g | start f == end g = make (f:*g)
                | otherwise = throw NotMultiplicable

--------------------------------------------------------------------------------
-- gltfTrsp -

-- | transposition of a product of elementary transformation.
gltfTrsp :: TransposableDistributive r => GLTForm r -> GLTForm r
gltfTrsp (One d)  = One d
gltfTrsp (P tr)   = P (trTrsp tr)
gltfTrsp (a :^ n) = gltfTrsp a :^ n
gltfTrsp (a :* b) = gltfTrsp b :* gltfTrsp a

--------------------------------------------------------------------------------
-- gltfInverse -

-- | inverse of a product of elementary transformation.
gltfInverse :: GLTForm x -> GLTForm x
gltfInverse o@(One _) = o
gltfInverse (P t)     = P (trInverse t)
gltfInverse (a :^ n)  = gltfInverse a :^ n
gltfInverse (a :* b)  = gltfInverse b :* gltfInverse a

--------------------------------------------------------------------------------
-- GLT - Cayleyan -

instance Oriented x => Invertible (GLT x) where
  tryToInvert (GLT f) = return $ make (gltfInverse f)

instance Oriented x => Exponential (GLT x) where
  type Exponent (GLT x) = Z
  (^) = zpower

instance Oriented x => Cayleyan (GLT x)

--------------------------------------------------------------------------------
-- TrApp -

-- | 'Oriented' homomorphisms.
data TrApp x y where
  TrFT  :: Oriented x => TrApp (Transformation x) (FT x)
  TrGL  :: Distributive x => TrApp (Transformation x) (GL x)
  TrGLT :: Oriented x => TrApp (Transformation x) (GLT x) 

--------------------------------------------------------------------------------
-- TrApp - Entity -

deriving instance Show (TrApp x y)
instance Show2 TrApp

deriving instance Eq (TrApp x y)
instance Eq2 TrApp

instance Validable (TrApp x y) where
  valid TrFT  = SValid
  valid TrGL  = SValid
  valid TrGLT = SValid
  
instance Validable2 TrApp

instance (Typeable x, Typeable y) => Entity (TrApp x y)
instance Entity2 TrApp

--------------------------------------------------------------------------------
-- TrApp - HomOriented -

instance Morphism TrApp where
  type ObjectClass TrApp = Ort
  homomorphous TrFT  = Struct :>: Struct
  homomorphous TrGL  = Struct :>: Struct
  homomorphous TrGLT = Struct :>: Struct

instance EmbeddableMorphism TrApp Ort
instance EmbeddableMorphism TrApp Typ
instance EmbeddableMorphismTyp TrApp

instance Applicative TrApp where
  amap TrFT  = make . P
  amap TrGL  = trGL
  amap TrGLT = trGLT

instance HomOriented TrApp where
  pmap TrFT  = id
  pmap TrGL  = id
  pmap TrGLT = id

--------------------------------------------------------------------------------
-- GLApp -

-- | 'Multiplicative' homomorphisms.
data GLApp x y where
  FTGL  :: Distributive x => GLApp (FT x) (GL x)
  FTGLT :: Oriented x => GLApp (FT x) (GLT x)
  GLTGL :: Distributive x => GLApp (GLT x) (GL x)
  GL2GL :: Galoisian x => GLApp (GL2 x) (GL x)

deriving instance Show (GLApp x y)
instance Show2 GLApp

deriving instance Eq (GLApp x y)
instance Eq2 GLApp

instance Validable (GLApp x y) where
  valid FTGL  = SValid
  valid FTGLT = SValid
  valid GLTGL = SValid
  valid GL2GL = SValid
  
instance Validable2 GLApp

instance (Typeable x, Typeable y) => Entity (GLApp x y)
instance Entity2 GLApp

--------------------------------------------------------------------------------
-- GLApp - HomMultiplicative -

instance Morphism GLApp where
  type ObjectClass GLApp = Mlt
  homomorphous FTGL = Struct :>: Struct
  homomorphous FTGLT = Struct :>: Struct
  homomorphous GLTGL = Struct :>: Struct
  homomorphous GL2GL = Struct :>: Struct

instance EmbeddableMorphism GLApp Ort
instance EmbeddableMorphism GLApp Typ
instance EmbeddableMorphismTyp GLApp

instance Applicative GLApp where
  amap FTGL  = zProduct TrGL
  amap FTGLT = zProduct TrGLT 
  amap GLTGL = zProductForm TrGL . form
  amap GL2GL = gl2GL
  
instance HomOriented GLApp where
  pmap FTGL  = id
  pmap FTGLT = id
  pmap GLTGL = id
  pmap GL2GL = \p -> productDim [p,p]

instance EmbeddableMorphism GLApp Mlt
instance HomMultiplicative GLApp

--------------------------------------------------------------------------------
-- permute -

-- | permutation of the given dimensions.
--
-- __Property__ Let @r@, @c@ be in @'Dim'' __x__@ and @p@ in @'Permutation' 'N'@ for
-- a 'Distributive' structure @__x__@, then holds:
-- If @'Permute' r c p@ is 'valid' then @'permute' r c p@ is 'valid'.
--
-- __Example__ Let @t = 'permute' r c p@ with @'Permute' r c p@ is 'valid' then its
-- associated matrix (see 'GLTGL') has the orientation @c ':>' r@ and the form
--
-- @
--
--            k         l
--   [1                          ]
--   [  .                        ]
--   [    .                      ]
--   [     1                     ]
--   [                 1         ] k
--   [         1                 ]
--   [           .               ]
--   [             .             ]
--   [               1           ]
--   [       1                   ] l
--   [                    1      ]
--   [                      .    ]
--   [                        .  ]
--   [                          1]
--
-- @
--
-- __Note__ @r@ dose not have to be equal to @c@, but from @r '==' c '<*' p@ follows that
-- both have the same length.
permute :: Distributive x => Dim' x -> Dim' x -> Permutation N -> GLT x
permute r c p = amap TrGLT (Permute r c p)

--------------------------------------------------------------------------------
-- permutFT -

-- | the induce element in the free groupoid of transformations.
permuteFT :: Distributive x
  => Dim' x -> Dim' x -> Permutation N -> FT x
permuteFT r c p = amap TrFT (Permute r c p)

--------------------------------------------------------------------------------
-- scale -

-- | scaling.
--
-- __Property__ Let @d@ be in @'Dim'' __x__@, @k@ in 'N' and @s@ in @'Inv' __x__@, then
-- holds: If @'Scale' d k s@ is 'valid' then @'scale' d k s@ is 'valid'.
--
-- __Example__ Let @t = 'scale' d k s@ with @'Scale' d k s@ is 'valid' then its associated
-- matrix (see 'GLTGL') is an endo with dimension @d@ and has the form 
--
-- @
--
--           k         
--   [1               ]
--   [  .             ]
--   [    .           ]
--   [     1          ]
--   [      s'        ] k
--   [         1      ]
--   [           .    ]
--   [             .  ]
--   [               1]
--
-- @
-- where @s' = ('inj' :: 'Inv' __x__ -> __x__) s@.
scale :: Distributive x => Dim' x -> N -> Inv x -> GLT x
scale d k s = amap TrGLT (Scale d k s)

--------------------------------------------------------------------------------
-- shear -

-- | shearing.
--
--  __Property__ Let @d@ be in @'Dim'' __x__@, @k@, @l@ in 'N' and @g@ in @'GL2' __x__@
-- then holds: If @'Shear' d k l g@ is 'valid' then @'shear' d k l g@ is 'valid'.
--
--  __Example__ Let @t = 'shear' d k l g@ where @'Shear' d k l g@ is 'valid' then its
--  associated matrix (see 'GLTGL') is an endo with dimension @d@ and has the form
--
-- @
--
--            k         l
--   [1                          ]
--   [  .                        ]
--   [    .                      ]
--   [     1                     ]
--   [       s         t         ] k
--   [         1                 ]
--   [           .               ]
--   [             .             ]
--   [               1           ]
--   [       u         v         ] l
--   [                    1      ]
--   [                      .    ]
--   [                        .  ]
--   [                          1]
--
-- @
shear :: Galoisian x  => Dim' x -> N -> N -> GL2 x -> GLT x
shear d k l g = amap TrGLT (Shear d k l g)
