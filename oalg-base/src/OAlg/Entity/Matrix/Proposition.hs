{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Matrix.Proposition
-- Description : propositions on matrices
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on matrices.
module OAlg.Entity.Matrix.Proposition
  (
    -- * Proposition
    prpMatrix, prpMatrixZ
    
  ) where

import Control.Monad

import Data.Typeable
import Data.Kind

import OAlg.Prelude

import OAlg.Category.Unify
import OAlg.Category.SDuality

import OAlg.Data.HomCo

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Distributive
import OAlg.Structure.Algebraic

import OAlg.Limes.ProductsAndSums

import OAlg.Entity.Natural

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.ProductsAndSums

import OAlg.Hom.Oriented.Proposition
--------------------------------------------------------------------------------
-- prpMatrix -

-- | validity of the algebraic structure of matrices.
prpMatrix :: Distributive x
  => XOrtOrientation (Matrix x)
  -> XOrtSite From (Matrix x)
  -> XOrtSite To (Matrix x)
  -> Statement
prpMatrix xo xf xt = Prp "Matrix" :<=>:
  And [ prpOrt (xoOrt xo)
      , prpMlt (xoMlt (xNB 0 10) xo)
      , prpFbr (xoFbr xo)
      , prpFbrOrt (xoFbrOrt xo)
      , prpAdd (xoAdd (xNB 0 5) xo)
      , prpDst (xoDst xo xf xt)
      ]


dstMatrix :: Int -> X (Matrix x) -> IO ()
dstMatrix = putDstr (\m -> [rws m,cls m]) where
  rws (Matrix r _ _) = show $ lengthN r
  cls (Matrix _ c _) = show $ lengthN c


--------------------------------------------------------------------------------
-- prpMatrixZ -

-- | validity of the algebraic structure of block matrices of 'Z'.
prpMatrixZ :: Statement
prpMatrixZ = Prp "MatrixZ"
  :<=>: And [ prpMatrix xo xf xt
            , prpAbl (xoAbl (xZB (-10) 10) xo)            
            , prpVec (xoVec xZ xo)
            , prpAlg (xoAlg xZ xf)
            , Label "Sums N3 (Matrix Z)" 
                 :<=>: valid (mtxSums :: Sums N3 (Matrix Z))
            ]
  where xo = xodZZ
        xf = xoFrom xo
        xt = xoTo xo

--------------------------------------------------------------------------------
-- DstX -

data DstX

type instance Structure DstX x = (Distributive x, XStandardOrtOrientation x)

instance Transformable DstX Typ where tau Struct = Struct

instance Transformable DstX Type where tau _ = Struct
instance TransformableType DstX

instance Transformable DstX Ort where tau Struct = Struct
instance TransformableOrt DstX

instance Transformable DstX Mlt where tau Struct = Struct
instance TransformableMlt DstX

instance Transformable DstX Fbr where tau Struct = Struct
instance TransformableFbr DstX

instance Transformable DstX Add where tau Struct = Struct
instance TransformableAdd DstX

instance Transformable DstX FbrOrt where tau Struct = Struct
instance TransformableFbrOrt DstX

instance Transformable DstX Dst where tau Struct = Struct
instance TransformableDst DstX

instance TransformableG Op DstX DstX where tauG Struct = Struct
instance TransformableGRefl Op DstX
instance TransformableOp DstX

instance TransformableG Matrix DstX DstX where tauG Struct = Struct
instance TransformableGRefl Matrix DstX

instance XStandardDst (Matrix Z) where
  xStandardDst = xoDst xStandardOrtOrientation xStandardOrtSite xStandardOrtSite

--------------------------------------------------------------------------------
-- prpHomCoMatrixFunctorial -

prpHomCoMatrixOpFunctorial ::
  ( FunctorialG t (HomCo m s o) (->)
  , m ~ Matrix, o ~ Op, s ~ DstX
  )
  => X (SomeEntityG t (HomCo m s o)) -> X (SomeCmpb2G t (HomCo m s o)) -> Statement
prpHomCoMatrixOpFunctorial = prpFunctorialGType

xsoId :: XOrtOrientation x -> X (Id x)
xsoId xo = amap1 Id (xoOrientation xo >>= xoArrow xo)

xsoPnt :: Oriented x => XOrtOrientation x -> X (Pnt x)
xsoPnt = amap1 Pnt . xoPoint

xsoRt :: Distributive x => XOrtOrientation x -> X (Rt x)
xsoRt (XOrtOrientation xo _) = amap1 Rt xo

xseHomCoMatrixId :: X (SomeEntityG Id (HomCo Matrix DstX Op))
xseHomCoMatrixId
  = xOneOfX [ xsoId xStandardOrtOrientation >>= return . SomeEntityG (Struct :: Struct DstX (Matrix Z))
            , xsoId xStandardOrtOrientation >>= return . SomeEntityG (Struct :: Struct DstX Z)
            ]

xseHomCoMatrixPnt :: X (SomeEntityG Pnt (HomCo Matrix DstX Op))
xseHomCoMatrixPnt
  = xOneOfX [ xsoPnt xStandardOrtOrientation
              >>= return . SomeEntityG (Struct :: Struct DstX (Matrix Z))
            , xsoPnt xStandardOrtOrientation >>= return . SomeEntityG (Struct :: Struct DstX Z)
            ]

xseHomCoMatrixRt :: X (SomeEntityG Rt (HomCo Matrix DstX Op))
xseHomCoMatrixRt
  = xOneOfX [ xsoRt xStandardOrtOrientation
              >>= return . SomeEntityG (Struct :: Struct DstX (Matrix Z))
            , xsoRt xStandardOrtOrientation >>= return . SomeEntityG (Struct :: Struct DstX Z)
            ]

xsct ::
  ( Entity (t x)
  , Entity (t z)
  )
  => (XOrtOrientation x -> X (t x)) -> Struct DstX x
  -> a y z -> a x y -> X (SomeCmpb2G t a)
xsct xt Struct f g = xt xStandardOrtOrientation >>= return . SomeCmpb2G f g


xscId :: Struct DstX x -> Struct DstX z -> a y z -> a x y -> X (SomeCmpb2G Id a)
xscId sx@Struct Struct = xsct xsoId sx

xscPnt :: Struct DstX x -> Struct DstX z -> a y z -> a x y -> X (SomeCmpb2G Pnt a)
xscPnt sx@Struct Struct = xsct xsoPnt sx 

xscRt :: Struct DstX x -> Struct DstX z -> a y z -> a x y -> X (SomeCmpb2G Rt a)
xscRt sx@Struct Struct = xsct xsoRt sx

scXscHomCoMatrixId :: SomeCmpb2 (HomCo Matrix DstX Op) -> X (SomeCmpb2G Id (HomCo Matrix DstX Op))
scXscHomCoMatrixId (SomeCmpb2 f g) = xscId (domain g) (range f) f g

scXscHomCoMatrixPnt :: SomeCmpb2 (HomCo Matrix DstX Op) -> X (SomeCmpb2G Pnt (HomCo Matrix DstX Op))
scXscHomCoMatrixPnt (SomeCmpb2 f g) = xscPnt (domain g) (range f) f g

scXscHomCoMatrixRt :: SomeCmpb2 (HomCo Matrix DstX Op) -> X (SomeCmpb2G Rt (HomCo Matrix DstX Op))
scXscHomCoMatrixRt (SomeCmpb2 f g) = xscRt (domain g) (range f) f g


xscHomCoMatrix :: X (SomeCmpb2 (HomCo Matrix DstX Op))
xscHomCoMatrix = amap1 soce $ xSctSomeCmpb2 10 (amap1 seoc xseHomCoMatrixId) xMorCo

soce :: SomeCmpb2 (SHom s s o (MorCo m s o)) -> SomeCmpb2 (HomCo m s o)
soce (SomeCmpb2 f g) = SomeCmpb2 (sHomCo f) (sHomCo g)

seoc :: Transformable s Typ
  => SomeEntityG t (HomCo m s o) -> SomeObjectClass (SHom s s o (MorCo m s o))
seoc (SomeEntityG s _) = SomeObjectClass s


xMorCo :: X (SomeMorphism (MorCo Matrix DstX Op))
xMorCo = xOneOf [ SomeMorphism (ToCo   :: MorCo Matrix DstX Op (Op (Matrix Z)) (Matrix (Op Z)))
                , SomeMorphism ( FromCo :: MorCo Matrix DstX Op (Matrix (Op Z)) (Op (Matrix Z)))
                ]

scga :: Category c => SomeCmpb2G Id c -> SomeApplication c
scga (SomeCmpb2G f g (Id x)) = SomeApplication (f . g) x

xscGHomCoMatrix :: X (SomeCmpb2G Id (HomCo Matrix DstX Op))
xscGHomCoMatrix = join $ amap1 scXscHomCoMatrixId xscHomCoMatrix

--------------------------------------------------------------------------------
-- prpHomCoMatrixOp -

prpHomCoMatrixOp :: Statement
prpHomCoMatrixOp = Prp "HomCoMatrixOp" :<=>:
  And [ prpHomCoMatrixOpFunctorial xseHomCoMatrixId xscGHomCoMatrix
      , prpHomCoMatrixOpFunctorial xseHomCoMatrixPnt (join $ amap1 scXscHomCoMatrixPnt xscHomCoMatrix)
      , prpHomCoMatrixOpFunctorial xseHomCoMatrixRt (join $ amap1 scXscHomCoMatrixRt xscHomCoMatrix)
      , prpHomOrientedDisjunctive (amap1 scga xscGHomCoMatrix)
      ]

