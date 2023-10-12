
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Product.Definition
-- Description : definition of free products over oriented symbols
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- defintion of free products over 'Oriented' symbols with exponents in a 'Number'.
--
-- __Note__ On 'Oriented' structures the canonical injection 'inj' and projection
-- 'prj' are bijections between the 'valid' entities of 'Path' and @'Product' 'N'@.
-- This is not true betwenn 'Path' and @'ProductForm' 'N'@ as
--
-- >>> prj (P 3 :^ 2 :: ProductForm N Q) :: Path Q
-- Path () [3,3]
--
-- and
--
-- >>> prj (P 3 :* P 3 :: ProductForm N Q) :: Path Q
-- Path () [3,3]
--
-- both map to the same 'Path'! But
--
-- >>> let p = make (P 3) :: Product N Q in p * p == p ^ 2
-- True
module OAlg.Entity.Product.Definition
  (
    -- * Product
    Product(), prLength, prFactor, prFactors, prwrd
  , nProduct, zProduct
  , prdMapTotal, prFromOp
  
    -- * Word
  , Word(..), fromWord, prfwrd, wrdprf, wrdPrfGroup
  , nFactorize, nFactorize'

    -- * Form
  , ProductForm(..), prfLength, prfDepth, prfFactors
  , nProductForm, zProductForm
  , prfInverse, prfFromOp
  , prfMapTotal

    -- ** Reduction
  , prfReduce, prfReduceWith

    -- ** Operations
  , prfopr, prfopr', prfopl, prfopl'

  )

  where

import Control.Monad
import Control.Exception

import Data.List ((++),repeat,map,groupBy,zip)

import Data.Foldable hiding (product)
import Data.Monoid hiding (Product)

import OAlg.Prelude

import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Canonical
import OAlg.Data.Singleton

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Ring
import OAlg.Structure.Number
import OAlg.Structure.Exponential

import OAlg.Hom

import OAlg.Entity.Sequence.Definition

infixr 7 :*
infixl 9 :^

--------------------------------------------------------------------------------
-- ProductForm -

-- | form for a free product over 'Oriented' symbols in @__a__@ with exponents in @__r__@.
--
--   __Definition__ Let @__r__@ be a 'Number'. A 'ProductForm' @pf@ is 'valid'
--  if and only if @'orientation' pf@ is 'valid' (see definition below) and all
--  its symbols @x@ - where @'P' x@ occurs in @pf@ - are 'valid'.
--
--  The 'orientation' of @pf@ is defined according:
--
-- @
--  orientation pf = case pf of
--    One p    -> one p
--    P a      -> orientation a
--    f :^ r   -> orientation f ^ r where (^) = power
--    f :* g   -> orientation f * orientation g
-- @
--
--  __Note__ 'Number' is required for @-1@, @0@ and @1@ are not degenerated as in @Z/2@ or
--  @Z/1@.
data ProductForm r a
  = One (Point a)
  | P a
  | ProductForm r a :^ r
  | ProductForm r a :* ProductForm r a

deriving instance (Oriented a, Entity r) => Show (ProductForm r a)
deriving instance (Oriented a, Entity r) => Eq (ProductForm r a)
deriving instance ( Oriented a, Entity r
                  , Ord a, OrdPoint a, Ord r
                  ) => Ord (ProductForm r a)

--------------------------------------------------------------------------------
-- ProductForm - Entity -

instance (Oriented a, Number r) => Validable (ProductForm r a) where
  valid pf = And [ Label "orientation" :<=>: valid (orientation pf)
                 , Label "symbols" :<=>: vld pf
                 ] where

    vld pf = case pf of
      One e   -> valid e
      P a     -> valid a
      pf :^ r -> vld pf && valid r
      a :* b  -> vld a && vld b
    
instance (Oriented a, Number r) => Entity (ProductForm r a)

pf :: Int -> Char -> ProductForm r (Orientation Char)
pf 0 c = One c
pf i c = P (c:>c) :* pf (i-1) c

--------------------------------------------------------------------------------
-- ProductForm - Oriented -

instance (Oriented a, Number r) => Oriented (ProductForm r a) where
  type Point (ProductForm r a) = Point a
  orientation pf = case pf of
    One p    -> one p
    P a      -> orientation a
    f :^ r   -> orientation f ^ r where (^) = power
    f :* g   -> orientation f * orientation g

--------------------------------------------------------------------------------
-- ProductForm - Foldable -

instance Foldable (ProductForm N) where
  foldMap _ (One _)  = mempty
  foldMap f (P a)    = f a
  foldMap _ (_ :^ 0) = mempty
  foldMap f (p :^ n) = foldMap f p <> foldMap f (p :^ pred n)
  foldMap f (p :* q) = foldMap f p <> foldMap f q

--------------------------------------------------------------------------------
-- ProductForm - Canonical -

instance Embeddable (Path a) (ProductForm r a) where
  inj (Path s fs) = foldr (:*) (One s) $ map P fs

instance Embeddable a (ProductForm r a) where
  inj = P
  
instance Oriented a => Projectible (Path a) (ProductForm N a) where
  prj pf = Path (start pf) (toList pf)

instance Integral r => Embeddable (ProductForm N a) (ProductForm r a) where
  inj (One p)  = One p
  inj (P x)    = P x
  inj (x :^ n) = inj x :^ (ntimes n rOne)
  inj (x :* y) = inj x :* inj y

instance Integral r => Projectible (ProductForm N a) (ProductForm r a) where
  prj (One p)  = One p
  prj (P x)    = P x
  prj (x :^ r) = prj x :^ n where n = prj (zFloor r)
  prj (x :* y) = prj x :* prj y
  
--------------------------------------------------------------------------------
-- prfopl -

-- | applicative operation from the left.
prfopl :: (t -> x -> x) -> ProductForm N t -> x -> x
prfopl (*>) pf x = case pf of
  One _    -> x
  P t      -> t *> x
  _ :^ 0   -> x
  a :^ n   -> prfopl (*>) (a :^ pred n) (prfopl (*>) a x)
  a :* b   -> prfopl (*>) a (prfopl (*>) b x)

--------------------------------------------------------------------------------
-- prfopl' -

-- | partially strict version of 'prfopl', i.e. every @n@-th application will be
-- reduced to head normal form.
--
-- Let @x' = 'prfopl'' n op p x@.
--
-- __Pre__ @0 '<' n@.
--
-- __Post__ @x' '==' 'prfopl' op p x@.
prfopl' :: N -> (t -> x -> x) -> ProductForm N t -> x -> x
prfopl' n op p x = fst $ prfopl op' p (x,0) where
  op' t (x,i) = if i `mod` n == 0
    then x' `seq` (x',0) else (x',i+1) where x' = t `op` x


--------------------------------------------------------------------------------
-- prfopr -

-- | applicative operation from the right.
prfopr :: (x -> t -> x) -> x -> ProductForm N t -> x
prfopr (<*) x pf = case pf of
  One _    -> x
  P t      -> x <* t
  _ :^ 0   -> x
  a :^ n   -> prfopr (<*) (prfopr (<*) x a) (a :^ pred n)
  a :* b   -> prfopr (<*) (prfopr (<*) x a) b
  
--------------------------------------------------------------------------------
-- prfopr' -

-- | partially strict version of 'prfopr', i.e. every @n@-th application will be
-- reduced to head normal form.
--
-- Let @x' = 'prfopr'' n op x p@.
--
-- __Pre__ @0 '<' n@.
--
-- __Post__ @x' '==' 'prfopr' op x p@.
prfopr' :: N -> (x -> t -> x) -> x -> ProductForm N t -> x
prfopr' n op x p = fst $ prfopr op' (x,0) p where
  op' (x,i) t = if i `mod` n == 0
    then x' `seq` (x',0) else (x',i+1) where x' = x `op` t


--------------------------------------------------------------------------------
-- prfLength -

-- | length.
prfLength :: Number r => ProductForm r a -> N
prfLength p = case p of
  One _  -> 0
  P _    -> 1
  f :^ r -> prfLength f * nFloor r
  f :* g -> prfLength f + prfLength g
  where nFloor r = prj $ fst $ zFloorFraction r

instance LengthN (ProductForm N a) where
  lengthN = prfLength
  
----------------------------------------
-- prfDepth -

-- | depth.
prfDepth :: ProductForm r a -> N
prfDepth p = case p of
  One _  -> 0
  P _    -> 1
  f :^ _ -> prfDepth f + 1
  f :* g -> max (prfDepth f) (prfDepth g) + 1

--------------------------------------------------------------------------------
-- Word -

-- | list of symbols in @__a__@ together with an exponent in @__r__@.
newtype Word r a = Word [(a,r)] deriving (Show,Eq,Validable)

--------------------------------------------------------------------------------
-- fromWord -

-- | the underlying list of @a@'s with there exponent.
fromWord :: Word r a -> [(a,r)]
fromWord (Word ars) = ars

--------------------------------------------------------------------------------
-- wrdAggr -

-- | aggregating words.
wrdAggr :: (Eq a, Semiring r) => Word r a -> Word r a
wrdAggr = Word . map aggr . groupBy (<=>) . fromWord where
  a <=> b = fst a == fst b
  aggr as@((a,_):_) = (a,foldl (+) rZero $ map snd as)

--------------------------------------------------------------------------------
-- nFactorize -

-- | factorization of a natural number to powers of primes.
--   For @0@ there will be thrown 'Undefined'.
nFactorize :: N -> Word N N
nFactorize 0 = throw $ Undefined "nFactorize 0"
nFactorize n = wrdAggr $ Word $ fct primes n where
  fct _ 1   = []
  fct prms@(p:prms') n = if n `mod` p == 0
    then (p,1):fct prms (n `div` p)
    else fct prms' n

-- | factorization of a natural number to powers of primes smaller then the given bound.
--   For @0@ there will be thrown 'Undefined'.
nFactorize' 
  :: N -- ^ bound for the primes
  -> N -- ^ a natural number
  -> Word N N
nFactorize' _ 0    = throw $ Undefined "nFactorize 0"
nFactorize' pMax n = wrdAggr $ Word $ fct primes n where
  fct _ 1 = []
  fct ps@(p:ps') n | pMax <  p      = []
                   | n `mod` p == 0 = (p,1):fct ps (n `div` p)
                   | otherwise      = fct ps' n
                   
--------------------------------------------------------------------------------
-- prfInverse -

-- | formal inverse
--
--  Let @p@ in @'ProductForm' r a@ then:
--
--   __Pre__ If @p@ contains a factor @'P' a@ then @'minusOne' '/=' 'Nothing'@.
--
--   __Post__ the formal inverse.
prfInverse :: Number r => ProductForm r a -> ProductForm r a
prfInverse p = case p of
  One p    -> One p
  P a      -> case minusOne of
    Just e -> P a :^ e
    _      -> throw NoMinusOne
  P a :^ z -> case minusOne of
    Just e -> P a :^ (e*z)
    _      -> throw NoMinusOne
  a :^ z   -> prfInverse a :^ z
  a :* b   -> prfInverse b :* prfInverse a

--------------------------------------------------------------------------------
-- prfFromOp -

-- | from 'Op' symbols.
prfFromOp :: ProductForm r (Op a) -> ProductForm r a
prfFromOp (One p)    = One p
prfFromOp (P (Op a)) = P a
prfFromOp (fo :^ r)  = prfFromOp fo :^ r
prfFromOp (fo :* fg) = prfFromOp fg :* prfFromOp fo

--------------------------------------------------------------------------------
-- prpToOp -

-- | to 'Op' symbols.
prfToOp :: ProductForm r a -> ProductForm r (Op a)
prfToOp (One p)  = One p
prfToOp (P a)    = P (Op a)
prfToOp (f :^ r) = prfToOp f :^ r
prfToOp (f :* g) = prfToOp g :* prfToOp f

--------------------------------------------------------------------------------
-- prfwrd -

-- | transforming a 'ProductForm' to its corresponding 'Word'.
prfwrd :: Integral r => ProductForm r a -> Word r a
prfwrd pf = Word (tow pf) where
  tow pf = case pf of
    One _       -> []
    P a         -> [(a,rOne)]
    P a :^ z    -> [(a,z)]
    a :^ y :^ z -> tow (a :^ (y*z)) 
    a :^ z      -> join $ takeN n $ repeat $ tow $ if z < rZero then prfInverse a else a
      where n = prj $ fst $ zFloorFraction z
    a :* b      -> tow a ++ tow b

--------------------------------------------------------------------------------
-- wrdprf -

-- | transforming a 'Word' to it corresponding 'ProductForm'.
--
-- __Note__ the 'Point' is needed for empty 'Word's.
wrdprf :: Semiring r => Point a -> Word r a -> ProductForm r a
wrdprf p (Word ws) = prf p ws where
  prf p ws = case ws of 
    []      -> One p
    [(a,r)] -> if r == rOne then P a else (P a :^ r)
    w:ws    -> prf p [w] :* prf p ws

--------------------------------------------------------------------------------
-- wrdPrfGroup -

-- | reducing a 'Word' by adding the exponents of consecutive equal symbols and
-- eliminating symbols with zero exponents.
wrdPrfGroup :: (Eq a, Semiring r) => Word r a -> Rdc (Word r a)
wrdPrfGroup (Word ws) = rdcw ws >>= return . Word where
  rdcw ws = case ws of
    (_,r):ws       | r == rZero -> reducesTo ws >>= rdcw 
    (a,r):(b,s):ws | a == b     -> reducesTo ((a,r+s):ws) >>= rdcw
    ar:ws                       -> rdcw ws >>= return . (ar:)
    []                          -> return ws         
  
--------------------------------------------------------------------------------
-- prfReduceWith -

-- | reduces a product form by the given reduction rules for words until no more
--   reductions are applicable.
prfReduceWith :: (Oriented a, Integral r)
  => (Word r a -> Rdc (Word r a)) -> ProductForm r a -> ProductForm r a
prfReduceWith rel pf
  = wrdprf (end pf)
  $ reduceWith (wrdPrfGroup >>>= rel)
  $ prfwrd pf

--------------------------------------------------------------------------------
-- prfFactors -

-- | list of elementary factors.
prfFactors :: ProductForm N a -> [a]
prfFactors = toList

-- | gets the @n@-the symbol.
prfLookup :: ProductForm N a -> N -> Maybe a
prfLookup p = lookup 0 (fromWord $ prfwrd p) where
  lookup _ [] _         = Nothing
  lookup l ((a,e):ws) i = if i < l' then Just a else lookup l' ws i where l' = l+e 
  
instance Sequence (ProductForm N) N x where
  list _ pf = prfFactors pf `zip` [0..]
  (??) = prfLookup
  
--------------------------------------------------------------------------------
-- prfReduce -

-- | reducing a 'ProductForm'  according to @'prfReduceWith' 'return'@.
prfReduce :: (Oriented a, Integral r) => ProductForm r a -> ProductForm r a
prfReduce = prfReduceWith return

instance (Oriented a, Integral r) => Reducible (ProductForm r a) where
  reduce = prfReduce


--------------------------------------------------------------------------------
-- Product -

-- | free product over 'Oriented' symbols in @__a__@ with exponents in a 'Integral' @__r__@.
--
-- __Definition__ A 'Product' @p@ is 'valid' if and only if its underlying
-- 'ProductForm' @pf@ is 'valid' and @pf@ is reduced, i.e. @pf == 'reduce' pf@.
newtype Product r a = Product (ProductForm r a) deriving (Show,Eq,Ord)

instance (Oriented a, Integral r) => Validable (Product r a) where
  valid (Product pf) = And [ valid pf
                           , Label "reduced"
                             :<=>: (reduce pf == pf) :?> Params ["pf":=show pf]
                           ]

deriving instance Foldable (Product N)
deriving instance LengthN (Product N a)

---------------------------------------
-- Product - Constructable -

instance Exposable (Product r a) where
  type Form (Product r a) = ProductForm r a
  form (Product p) = p

instance (Oriented a, Integral r) => Constructable (Product r a) where
  make = Product . reduce

--------------------------------------------------------------------------------
-- Product - Sequence -

instance Sequence (Product N) N a where
  list f = restrict (list f)
  (??) = restrict (??)
  
----------------------------------------
-- Product - Canonical -

instance (Oriented a, Integral r) => Embeddable a (Product r a) where
  inj a = make $ inj a

instance (Oriented a, Integral r) => Embeddable (Path a) (Product r a) where
  inj p = make $ inj p

instance Oriented a => Projectible (Path a) (Product N a) where
  prj = restrict prj
  
----------------------------------------
-- Product - Structure -

instance (Oriented a, Integral r) => Entity (Product r a)

instance (Oriented a, Integral r) => Oriented (Product r a) where
  type Point (Product r a) = Point a
  orientation = restrict orientation

instance (Oriented a, Integral r) => Multiplicative (Product r a) where
  one p                 = make (One p)
  
  Product f * Product g | start f == end g = make (f :* g)
                        | otherwise        = throw NotMultiplicable

  npower p n = p ^ r where r = ntimes n rOne

instance (Oriented a, Integral r, Ring r) => Invertible (Product r a) where
  tryToInvert = return . invert 
  invert (Product p) = make (p :^ negate rOne)

instance (Oriented a, Integral r, Ring r) => Cayleyan (Product r a)

instance (Oriented a, Integral r) => Exponential (Product r a) where
  type Exponent (Product r a) = r
  p@(Product pf) ^ r
    | not (abs r == rOne || isEndo p) = throw NotExponential
    | otherwise                       = make (pf :^ r)

--------------------------------------------------------------------------------
-- prFactors -

-- | the list of primary factors.
prFactors :: Product N a -> [a]
prFactors = toList

--------------------------------------------------------------------------------
-- prLength -

-- | number of primary factors where where all simple factors are expanded according to there exponent.
prLength :: Product N a -> N
prLength = restrict prfLength

--------------------------------------------------------------------------------
-- prwrd -

-- | restriction of 'prfwrd'.
prwrd :: (Integral r, Oriented a) => Product r a -> Word r a
prwrd (Product pf) = Word (prfwrd pf) where
  -- we use here the property that pf is reduced.
  prfwrd pf = case pf of
    One _          -> []
    P a            -> [(a,rOne)]
    P a :^ r       -> [(a,r)]
    P a :* pf      -> (a,rOne):prfwrd pf
    P a :^ r :* pf -> (a,r):prfwrd pf
    pf             -> throw $ InvalidData $ show $ pf

--------------------------------------------------------------------------------
-- prFactor -

-- | the @n@-th primary factor where all simple factors are expanded according to there
--   exponent. 
prFactor :: Product N a -> N -> a
prFactor = (?)

--------------------------------------------------------------------------------
-- prd -

-- | evaluates the /product/ according to the given exponential and multiplication.
prd :: (Multiplicative x, Oriented a, p ~ Point a, q ~ Point x, Number r)
   => (x -> r -> x) -> (p -> q) -> (a -> x) -> ProductForm r a -> x
prd (^) q x pf = case pf of
  One p  -> one (q p)
  P a    -> x a
  a :^ r -> prd (^) q x a ^ r
  a :* b -> prd (^) q x a * prd (^) q x b

--------------------------------------------------------------------------------
-- prdMapTotal -

-- | mapping a product.
prdMapTotal :: (Singleton (Point y), Oriented y, Integral r)
  => (x -> y) -> Product r x -> Product r y
prdMapTotal f (Product p) = make $ f' p where
  f' (One _)  = One unit
  f' (P x)    = P (f x)
  f' (x :^ r) = f' x :^ r
  f' (x :* y) = f' x :* f' y
  

--------------------------------------------------------------------------------
-- prfMapTotal -

-- | mapping a product form
prfMapTotal :: Singleton (Point y)
  => (x -> ProductForm r y) -> ProductForm r x -> ProductForm r y
prfMapTotal f pf = case pf of
  One _  -> One unit
  P x    -> f x
  x :^ r -> prfMapTotal f x :^ r
  x :* y -> prfMapTotal f x :* prfMapTotal f y

----------------------------------------
-- nProductForm -


nProductFormOrt :: (Hom Ort h, Multiplicative x)
  => Struct Ort a -> h a x -> ProductForm N a -> x
-- nProductFormOrt Struct f = prd npower (pmap f) (f$)
nProductFormOrt Struct h = prd h where
  prd h f = case f of
    One p  -> one (pmap h p)
    P a    -> amap h a
    a :^ n -> prd h a `npower` n
    a :* b -> prd h a * prd h b
    
-- | mapping a product form with exponents in t'N' into a 'Multiplicative' structure
-- applying a homomorphism between 'Oriented' structures.
nProductForm :: (Hom Ort h, Multiplicative x)
  => h a x -> ProductForm N a -> x
nProductForm f = nProductFormOrt (tau $ domain f) f


nProductOrt :: (Hom Ort h, Multiplicative x)
  => Struct Ort a -> h a x -> Product N a -> x
nProductOrt Struct = restrict . nProductForm

--------------------------------------------------------------------------------
-- nProduct -

-- | mapping a product with exponents in t'N' into a 'Multiplicative' structure
--   applying a homomorphism between 'Oriented' structures.
nProduct :: (Hom Ort h, Multiplicative x)
  => h a x -> Product N a -> x
nProduct h = nProductOrt (tau $ domain h) h 

--------------------------------------------------------------------------------
-- zProductForm -

zProductFormOrt :: (Hom Ort h , Cayleyan x)
  => Struct Ort a -> h a x -> ProductForm Z a -> x
zProductFormOrt Struct h = prd h where
  prd h f = case f of
    One p  -> one (pmap h p)
    P a    -> amap h a
    a :^ z -> prd h a `zpower` z
    a :* b -> prd h a * prd h b


-- | mapping a product form with exponents in 'Z' into a 'Cayleyan' structure
-- applying a homomorphism between 'Oriented' structures.
zProductForm :: (Hom Ort h , Cayleyan x)
                 => h a x -> ProductForm Z a -> x
zProductForm f = zProductFormOrt (tau $ domain f) f

--------------------------------------------------------------------------------
-- zProduct -
zProductOrt :: (Hom Ort h, Cayleyan x)
  => Struct Ort a -> h a x -> Product Z a -> x
zProductOrt Struct = restrict . zProductForm

-- | mapping a product with exponents in 'Z' into a 'Cayleyan' structure
--   applying a homomorphism between 'Oriented' structures.
zProduct :: (Hom Ort h, Cayleyan x)
  => h a x -> Product Z a -> x
zProduct h = zProductOrt (tau $ domain h) h


--------------------------------------------------------------------------------
-- prFromOp -

-- | from 'Op' symbols.
--
-- __Property__ For every 'Oriented' structure @__a__@ and 'Integral' @__r__@ the resulting
-- map 'prFromOp' is a __contravariant__ homomorphisms between 'Multiplicative' structures.
prFromOp :: Product r (Op a) -> Product r a
prFromOp (Product f) = Product (prfFromOp f)

