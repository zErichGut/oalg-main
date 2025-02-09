
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.AbelianGroup.KernelsAndCokernels
-- Description : kernels and cokernels for homomorphisms between finitely generated abelian groups
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'Kernels' and 'Cokernels' for homomorphisms between finitely generated abelian groups.
module OAlg.AbelianGroup.KernelsAndCokernels
  (
    -- * Kernels
    abhKernels

    -- * Cokernels
  , abhCokernels, abhCokersLftFree
  
    -- * Smith Normal
  , isoSmithNormal

    -- * Adjunction
  , abhSliceFreeAdjunction

    -- * X
    
  )
  where

import Control.Monad

import Data.List (map,(++),repeat,zip)

import OAlg.Prelude hiding ((//))

import OAlg.Data.Canonical
import OAlg.Data.FinitelyPresentable

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative as M
import OAlg.Structure.Additive
import OAlg.Structure.Exponential
import OAlg.Structure.Operational
import OAlg.Structure.Number

import OAlg.Adjunction

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.PullbacksAndPushouts

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList as F hiding ((++),repeat,zip)
import OAlg.Entity.Diagram
import OAlg.Entity.Sequence
import OAlg.Entity.Matrix as M
import OAlg.Entity.Slice
import OAlg.Entity.Product (fromWord)

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.ZMod
import OAlg.AbelianGroup.Euclid
import OAlg.AbelianGroup.Free


--------------------------------------------------------------------------------
-- abhCokernelFreeDgmLftFree -

-- | a liftable cokernel of a free cokernel diagram.
--
--  __Properties__ Let @d@ be in @'CokernelDiagramFree' 'N1' 'AbHom'@ and
-- @cf = 'abhCokernelFreeDgmLftFree' d@, then holds: Let @c = 'clfCokernel' cf@ in
--
-- (1) @'diagram' c '==' d@.
--
-- (2) @'tip' ('universalCone' c)@ is smith normal (see t'AbGroup').
abhCokernelFreeDgmLftFree :: CokernelDiagramFree N1 AbHom -> CokernelLiftableFree AbHom
abhCokernelFreeDgmLftFree (DiagramFree _ d@(DiagramParallelRL _ _ (h:|Nil)))
  = CokernelLiftableFree (LimesInjective (ConeCokernel d coker) univ) lftAny where

  --------------------
  -- cokernel -

  m = abhz h
  SmithNormalForm o ds (RowTrafo ra) _ = smithNormalForm m
  Inv a aInv = amap GLTGL ra
  AbHom aInv' = zabh aInv
  p = lengthN ds
  q = lengthN (rows m) >- (o + p)

  d0 = dim (ZMod 0)
  gp = Dim $ productSymbol $ amap1 (ZMod . prj) ds
  gq = d0 ^ q
  gpq = gp * gq
  
  coker = ( AbHom $ mtxJoin
          $ matrixBlc [gp,gq] [d0^o,d0^p,gq] [(matrix gp (d0^p) ps,0,1),(one gq,1,2)]
          )
        * zabh a where
    ps = [(zmh (ZMod 0 :> ZMod (prj d)) 1,i,i)| (d,i) <- ds `zip` [0..]]
    -- @0 < d@ for all d in ds as ds is the diagonal of the smith normal form

  univ :: CokernelCone N1 AbHom -> AbHom
  univ (ConeCokernel _ (AbHom x))
    = AbHom
    $ Matrix (rows x) gpq
    $ rcets $ Row $ PSequence
    $ map (\(cl,j) -> (cl,j>-o))
    $ fcts o (map fst $ listN gp)
    $ listN $ etsrc $ mtxxs (x*aInv')
    where
      
      fcts :: (Enum j, Ord j) => j -> [ZMod] -> [(Col i ZModHom,j)] -> [(Col i ZModHom,j)] 
      fcts _ [] cls = cls
      fcts _ _ []   = []
      fcts j (z:zs) cls@((cl,j'):cls') = if j < j'
        then fcts (succ j) zs cls
        else ((amap1 (fct z) cl,j'):fcts (succ j) zs cls')

      fct :: ZMod -> ZModHom -> ZModHom
      fct z h = zmh (z:>end h) (toZ h)


  --------------------
  -- liftable -
  lftAny :: Any k -> Liftable From (Free k) AbHom
  lftAny k = case ats k of Ats -> LiftableFrom coker (lft coker)

  lft :: Attestable k => AbHom -> Slice From (Free k) AbHom -> Slice From (Free k) AbHom
  lft c s@(SliceFrom i f)
    | slicePoint i /= start f = throw $ InvalidData $ show s
    | end c /= end f          = throw NotLiftable
    | otherwise               = SliceFrom i f' where
        f'  = zabh (aInv * zf')

        zf  = abhz f
        zf' = mtxJoin $ matrixBlc [dim () ^ r,rows zf] [cols zf] [(zf,1,0)]
        r   = lengthN (start aInv) >- lengthN (rows zf)

        
        
xCokernelDiagramFree :: X (Matrix Z) -> X (CokernelDiagramFree N1 AbHom)
xCokernelDiagramFree xm = do
  m <- xm
  let r = lengthN $ rows m
      c = lengthN $ cols m
      a = zabh m
   in case (someNatural r, someNatural c) of
        (SomeNatural r',SomeNatural c')
          -> return (DiagramFree
                       (SomeFree (Free r'):|SomeFree (Free c'):|Nil)
                       (DiagramParallelRL (end a) (start a) (a:|Nil))
                    )
             
vldAbhCokernelFree :: Statement
vldAbhCokernelFree = Forall (xCokernelDiagramFree xm) (valid . abhCokernelFreeDgmLftFree) where
  xm = xoOrientation xmo >>= xoArrow xmo
  -- xm = xStandard
  xmo = xMatrixTtl 10 0.8 (xZB (-100) 100)

atsFree :: Free k c -> Ats k
atsFree (Free k) = ats k

--------------------------------------------------------------------------------
-- abhCokernelFreeTo' -

-- | the cokernel of a free site to.
--
--  __Properties__ Let @s = 'SliceTo' _ h@ be in @'Slice' 'To' ('Free' __k__) 'AbHom'@ and
-- @cf = 'abhCokernelFreeTo'' s@, then holds: Let @c = 'clfCokernel' cf@ in 
--
-- (1) @'diagram' c '==' 'cokernelDiagram' h@.
--
-- (2) @'tip' ('universalCone' c)@ is smith normal (see t'AbGroup').
abhCokernelFreeTo' :: Attestable k => Slice To (Free k) AbHom -> CokernelLiftableFree AbHom
abhCokernelFreeTo' (SliceTo k h) = CokernelLiftableFree (LimesInjective hCoker hUniv) lft where

  h' = amap FreeAbHom (amap AbHomFree h)
  -- h' has free start and end
  -- as end h is free it follows that, end h == end h' and
  -- unitRight abhFreeAdjunction (end h) == one (end h) and hence
  -- h == h' * unitRight abhFreeAdjunction (start h)

  h'Dgm = case someNatural (lengthN $ start h') of
    SomeNatural k' -> DiagramFree ks (cokernelDiagram h') where
      ks = SomeFree k:|SomeFree (Free k'):|Nil

  CokernelLiftableFree h'Coker lft = abhCokernelFreeDgmLftFree h'Dgm
  
  -- as unitRight abhFreeAdjunction (start h) is an epimorphism it follows
  -- that h and h' have the same cokernelFactor!
  hCoker = ConeCokernel (cokernelDiagram h) (cokernelFactor $ universalCone h'Coker)

  hUniv (ConeCokernel _ x) = universalFactor h'Coker (ConeCokernel (diagram h'Coker) x)

xSomeFreeSliceTo :: X (SomeFree AbHom) -> XOrtSite To AbHom -> X (SomeFreeSlice To AbHom)
xSomeFreeSliceTo xn xos = do
  SomeFree n <- xn
  f <- xSliceTo xos n
  return (SomeFreeSlice f)

vldAbhCokernelFreeTo :: Statement
vldAbhCokernelFreeTo = Forall xst (\(SomeFreeSlice s) -> valid $ abhCokernelFreeTo' s) where
  xst = xSomeFreeSliceTo (xn 10) xos
  
  xn :: N -> X (SomeFree AbHom)
  xn nMax = do
    SomeNatural n <- amap1 someNatural (xNB 0 nMax)
    return (SomeFree $ Free n)
    
  xos = xStandardOrtSite

--------------------------------------------------------------------------------
-- abhPullbackFree -

-- | the pullback with a free tip of its universal cone for the given free pullback diagram.
--
--  __Property__ Let @d = 'DiagramFree' _ d'@ be in @'PullbackDiagramFree' __n__ 'AbHom'@,
--  then holds: @'diagram' ('limesFree' p) = d'@ where @p = 'abhPullbackFree' d@.
abhPullbackFree :: PullbackDiagramFree n AbHom -> PullbackFree n AbHom
abhPullbackFree (DiagramFree _ d') = case freeTip p of
  SomeFree k -> LimesFree k p
  where
    -- if d = DiagramFree _ d' is valid, then the r (l d') == d' for the right
    -- and left adjoint of abhFreeAdjunction. Furthermore the tip of p is free!
    freeTip :: Pullback n AbHom -> SomeFree AbHom
    freeTip p = case someNatural n of
      SomeNatural n' -> SomeFree (Free n')
      where n = lengthN $ tip $ universalCone p

    p = lmPrjMap adj $ limes zmxPullbacks $ dgMap l d' where
      adj = abhFreeAdjunction
      Adjunction l _ _ _ = adj

someFree :: N -> SomeFree AbHom
someFree n = case someNatural n of
  SomeNatural n' -> SomeFree (Free n')

plbDgmFree :: PullbackDiagram n (Matrix Z) -> PullbackDiagramFree n AbHom
plbDgmFree d = DiagramFree (amap1 (someFree . lengthN) $ dgPoints d) (dgMap FreeAbHom d)


vldAbhPullbackFree :: Statement
vldAbhPullbackFree = Forall xd (valid . limesFree . abhPullbackFree) where
  xd = amap1 plbDgmFree (xStandard :: X (PullbackDiagram N3 (Matrix Z)))
  
--------------------------------------------------------------------------------
-- abhSplitCy -

-- | splits an abelian homomorphism @h@ into a list @hs@ where each
-- @h'@ in @hs@ has as start point equal to the start point of @h@ and end point a
-- cyclic group to the power of some order such that all  @h'@ /cover/ @h@.
--
-- __Properties__ Let @h@ be in 'AbHom' and @hs = 'abhSplitCy', then holds:
--
-- (1) For all @h'@ in @hs@ holds: @'orientation' h' '==' 'start' h ':>' 'abg' n '^' r@
-- for some @n@, @r@ in 'N'.
--
-- (2) For all @x@ in 'AbHom' with @'end' x '==' 'start' h@ holds: @h v'*' x '==' 0@
-- if and only if @h' v'*' x '==' 0@ for all @h'@ in @hs@.
abhSplitCy :: AbHom -> [AbHom]
abhSplitCy (AbHom m@(Matrix r _ _))
  = amap1 (\(m',_,_) -> AbHom m')
  $ etsxs
  $ mtxxs
  $ mtxGroupRow
  $ (RowTrafo (permute r' r p) *> m)
  where (r',p) = permuteBy nProxy compare id r
  
--------------------------------------------------------------------------------
-- abhFreeFromSplitCy -

-- | splits an abelian homomorphism @h@ into some finite list @hs@ where each
--  @h'@ in @hs@ has as end point a cyclic group to the power of some order such that all
--  @h'@ /cover/ @h@.
--
-- __Properties__ Let @s = 'SliceFrom' _ h@ be in @'Slice' 'From' ('Free' __k__) 'AbHom'@
-- and @hs = 'abhFreeFromSplitCy' s@, then holds:
--
-- (1) For all @'SliceFrom' _ h'@ in @hs@ exists a @n@, @r@ in 'N' such that
-- @'end' h' '==' 'abg' n '^' r@.
--
-- (2) For all @x@ in 'AbHom' with @'end' x '==' 'start' h@ holds: @h v'*' x '==' 0@ if
-- and only if @h' v'*' x '==' 0@ for all @'SliceFrom' _ h'@ in @hs@.
abhFreeFromSplitCy :: Slice From (Free k) AbHom -> SomeFinList (Slice From (Free k) AbHom)
abhFreeFromSplitCy (SliceFrom k h)
  = someFinList $ amap1 (SliceFrom k) $ abhSplitCy h 

--------------------------------------------------------------------------------
-- abhKernelFreeFromCy -

xFreeFromCy :: Free k AbHom -> X (Slice From (Free k) AbHom)
xFreeFromCy k@(Free k') = do
  n <- xNB 0 1000
  r <- xNB 0 10
  h <- xAbHom 0.3 (abg 0 ^ (lengthN k') :> abg n ^ r)
  return (SliceFrom k h)

pp2 :: Attestable k => Free k AbHom -> Statement
pp2 k = Forall xs (valid . abhKernelFreeFromCy) where
  xs = xFreeFromCy k
  
-- | free kernel where the end point is equal to some cyclic group to some order.
--
-- __Property__ Let @s = 'SliceFrom' _ h@ where @'end' h '==' abg n '^' r@ for some
-- @n@, @r@ in 'N', then holds:
-- @'diagram' ('limesFree' ker) '==' 'kernelDiagram' h@ where @ker = 'abhKernelFreeFromCy' s@.
abhKernelFreeFromCy :: Attestable k => Slice From (Free k) AbHom -> KernelFree N1 AbHom
abhKernelFreeFromCy s@(SliceFrom k h) = hKer $ fromWord $ dimwrd $ abgDim $ end h where

  freeTip :: Kernel N1 AbHom -> SomeFree AbHom
  freeTip k = case someNatural n of
    SomeNatural n' -> SomeFree (Free n')
    where n = lengthN $ tip $ universalCone k

  hKer [] = LimesFree k (kernelZero s (orientation h))
  -- h == 0

  hKer [(ZMod 0,_)] = case freeTip ker of
    SomeFree k' -> LimesFree k' ker
    where ker = lmPrjMapDst adj $ limes zmxKernels $ dgMap l (kernelDiagram h)
          adj = abhFreeAdjunction
          Adjunction l _ _ _ = adj

  hKer [(ZMod 1,_)] = hKer []

  hKer [(ZMod c,_)] = case freeTip ker of
    SomeFree k' -> LimesFree k' ker
    where
      ker = LimesProjective kCone kUniv

      DiagonalForm d _ (ColTrafo t) = zmxDiagonalForm (abhz h)
      -- d = (rt*>h)<*ct
    
      m = lengthN (start h)
      s = lengthN d
      r = m >- s

      Inv b bInv = amap GLTGL t

      dm = dim () ^ m
      kDgm = DiagramParallelLR (start h) (end h) (h:|Nil)
  
      k = map f d ++ takeN r (repeat 1)
      -- 0 < d
      f d = if d' == 0 then 1 else inj (lcm d' c) // d' where d' = prj (mod0 d c)

      kLim = zabh (b*diagonal dm dm k)
      kCone = ConeKernel kDgm kLim

      kUniv cn@(ConeKernel _ x) = AbHom $ Matrix (Dim e) (Dim sx) xs'' where
        -- note: from x valid and eligible follows that
        -- for all non zero (z,i,j) in x holds: orientation z = cy 0 :> cy 0
        AbGroup e = end kLim
        
        AbGroup sx = tip cn
        
        Matrix _ _ xs'  = bInv * abhz x
        xs'' = crets $ Col $ PSequence $ div' (list nProxy $ etscr xs') (k `zip` [0..])
  
        div' :: Ord i => [(Row j Z,i)] -> [(Z,i)] -> [(Row j ZModHom,i)]
        div' [] _             = []
        div' ((rw,i):rws') [] = (amap1 fromZ rw,i):div' rws' []
        div' rws@((rw,i):rws') ((k,i'):kis')
          | i' < i    = div' rws kis'
          | otherwise = (amap1 (fromZ . \z -> div z k) rw,i):div' rws' kis' 

  hKer _ = error "faild precondition"

--------------------------------------------------------------------------------
-- abhKernelFreeFrom -

xFreeFrom :: Free k AbHom -> X (Slice From (Free k) AbHom)
xFreeFrom k@(Free k') = do
  h <- xh (abg 0 ^ (lengthN k'))
  return (SliceFrom k h)
  where XStart _ xh = xStandardOrtSite :: XOrtSite From AbHom 

pp3 :: Attestable k => Free k AbHom -> Statement
pp3 k = Forall xs valid where xs = xFreeFrom k

-- | the kernel of a free site from.
--
-- @
--          h
--      a ------> b
--      
-- @ where @a@ is free of some order @k@.
--
-- __Property__ Let @s = 'SliceFrom' _ h@ be in @'Slice' 'From' ('Free' __k__)@ and
-- @ker = 'abhKernelFreeFrom' s@, then holds:
-- @'diagram' ('limesFree' ker) '==' 'kernelDiagram' h@.
abhKernelFreeFrom :: Attestable k => Slice From (Free k) AbHom -> KernelFree N1 AbHom
abhKernelFreeFrom s = ker s (amap1 abhKernelFreeFromCy $ abhFreeFromSplitCy s) where

  plbDgm :: Attestable k
    => Free k AbHom -> FinList n (KernelFree N1 AbHom) -> PullbackDiagramFree n AbHom
  plbDgm k kers = DiagramFree ks dgm where
    ks = SomeFree k :| amap1 (\(LimesFree k' _) -> SomeFree k') kers
    dgm = DiagramSink (slicePoint k)
      $ amap1 (kernelFactor . universalCone . limesFree)
      $ kers
  
  ker :: Attestable k
    => Slice From (Free k) AbHom -> SomeFinList (KernelFree N1 AbHom)
    -> KernelFree N1 AbHom
  ker s@(SliceFrom k _) (SomeFinList kers) = ker' s kers (abhPullbackFree $ plbDgm k kers)

  ker'
    :: Slice From (Free k) AbHom
    -> FinList n (KernelFree N1 AbHom)
    -> PullbackFree n AbHom
    -> KernelFree N1 AbHom
  ker' (SliceFrom _ h) kers (LimesFree kt plb)
    = LimesFree kt (LimesProjective hKer hUniv) where
    
    hDgm = kernelDiagram h
    hKer = ConeKernel hDgm (F.head $ shell $ universalCone plb)
    
    hUniv (ConeKernel _ x) = universalFactor plb plbCone where
      plbCone = ConeProjective (diagram plb) (start x) cs
      cs = x:|amap1
        (\(LimesFree _ ker)
         -> universalFactor ker (ConeKernel (diagram ker) x)
          -- the cone is eligible because of the property (2) of abhFreeFromSplitCy
        ) kers

--------------------------------------------------------------------------------
-- abhKernel -

-- | kernel for a given additive homomorphism.
--
-- __Properties__ Let @d@ be in @'KernelDiagram' 'N1' 'AbHom'@ and
-- @ker = 'abhKernel' d@, then holds:
--
-- (1) @'diagram' ker '==' d@.
--
-- (2) @'tip' ('universalCone' ker)@ is smith normal.
--
-- The construction follows the diagram below by using 'abgGeneratorTo':
--
-- @
--         k''         
--    r'' ------> s'' 
--     |           | 
--  q' |        p' | 
--     |           | 
--     v    k'     v
--    r' --------> s'
--     |           |
--  q  |         p | 
--     |           | 
--     v   hKer    v     h 
--     r --------> s -------> e
-- @
abhKernel :: KernelDiagram N1 AbHom -> Kernel N1 AbHom
abhKernel d = hKer d (finitePresentation abgFinPres $ start h) where

  DiagramParallelLR _ _ (h:|Nil) = d
  
  hKer :: KernelDiagram N1 AbHom -> FinitePresentation To Free AbHom -> Kernel N1 AbHom
  hKer
    d@(DiagramParallelLR _ _ (h:|Nil))
    g@(GeneratorTo (DiagramChainTo _ (p:|_:|Nil)) ns' _ _ _ _)
    = hKer' d g (abhKernelFreeFrom (SliceFrom ns' (h*p)))

  hKer'
    :: KernelDiagram N1 AbHom
    -> FinitePresentation To Free AbHom
    -> KernelFree N1 AbHom
    -> Kernel N1 AbHom
  hKer'
    d
    g@(GeneratorTo (DiagramChainTo _ (_:|p':|Nil)) ns' ns'' _ _ _)
    hpKerFree@(LimesFree nr' hpKer)
    = hKer'' d g hpKerFree k'p'Plb where

    k'p'Plb = abhPullbackFree
      (DiagramFree (SomeFree ns':|SomeFree nr':|SomeFree ns'':|Nil) k'p'PlbDgm)
    k'p'PlbDgm = DiagramSink (end k') (k':|p':|Nil)

    k' = kernelFactor $ universalCone hpKer
    
  hKer''
    :: KernelDiagram N1 AbHom
    -> FinitePresentation To Free AbHom
    -> KernelFree N1 AbHom
    -> PullbackFree N2 AbHom
    -> Kernel N1 AbHom
  hKer''
    d
    (GeneratorTo (DiagramChainTo _ (p:|_:|Nil)) _ _ _ _ lp)
    (LimesFree nr' hpKer)
    (LimesFree nr'' k'p'Plb)
    = LimesProjective hKer hUniv where

    _:|q':|_   = shell $ universalCone k'p'Plb
    q'CokerDgm = cokernelDiagram q' 
    q'Coker    = clfCokernel $ abhCokernelFreeDgmLftFree
      ( DiagramFree
         (SomeFree nr':|SomeFree nr'':|Nil)
         q'CokerDgm
      )
      
    hKer = ConeKernel d hKerFactor where
      hKerFactor = universalFactor q'Coker (ConeCokernel q'CokerDgm (p*k'))
      k' = kernelFactor $ universalCone hpKer
    
    hUniv cn@(ConeKernel _ x) = case finitePresentation abgFinPres $ start x of
      GeneratorTo (DiagramChainTo _ (t:|_)) nv' _ t'Coker _ _
        | not (d == cnDiagram cn) -> throw $ ConeNotEligible $ show cn
        | otherwise               -> universalFactor t'Coker t'Cone where
                
        t'Cone = ConeCokernel (diagram t'Coker) (q*u')
        q  = cokernelFactor $ universalCone q'Coker
        u' = universalFactor hpKer x'Cone

        x'Cone = ConeKernel (diagram hpKer) x'
        SliceFrom _ x' = lp (SliceFrom nv' (x*t))


--------------------------------------------------------------------------------
-- abhKernels -

-- | kernels for 'AbHom'. 
abhKernels :: Kernels N1 AbHom
abhKernels = Limits abhKernel

--------------------------------------------------------------------------------
-- AbHom - SliceCokernelTo -

instance Attestable k => SliceCokernelTo (Free k) AbHom where
  sliceCokernelTo = clfCokernel . abhCokernelFreeTo'
  -- do not change this definition, otherwise the liftable of abhCokernelLiftable has
  -- to be adapted.
  
--------------------------------------------------------------------------------
-- AbHom - SliceKernelFrom -

instance Attestable k => SliceKernelFrom (Free k) AbHom where
  sliceKernelFrom = limesFree . abhKernelFreeFrom

--------------------------------------------------------------------------------
-- abhSliceFreeAdjunction -

-- | the cokernel-kernel adjunction for a given @'Free' __k__@. 
abhSliceFreeAdjunction :: Attestable k
  => Free k AbHom
  -> Adjunction (SliceCokernelKernel (Free k) AbHom)
       (SliceFactor From (Free k) AbHom)
       (SliceFactor To (Free k) AbHom)
abhSliceFreeAdjunction = slcAdjunction


--------------------------------------------------------------------------------
-- abhCokernelLftFree -


-- | a liftable cokernel of a cokernel diagram.
--
--  __Properties__ Let @h@ be in @'CokernelDiagram' 'N1' 'AbHom'@ and
-- @cf = 'abhCokernelLftFree' h@, then holds: Let @c = 'clfCokernel' cf@ in
--
-- (1) @'diagram' c '==' h@.
--
-- (2) @'tip' ('universalCone' c)@ is smith normal (see t'AbGroup').
--
-- @
--           w          
--     c <------- e'' 
--     ^           | 
--   u |        q' | 
--     |           | 
--     |    h'     v    
--    s' --------> e' -----> h'L
--     |           |          |
--  p  |         q |          | u'
--     |           |          |
--     v     h     v    w'    v
--     s --------> e ------> c' = cCokerLft
-- @
abhCokernelLftFree :: CokernelDiagram N1 AbHom -> CokernelLiftableFree AbHom
abhCokernelLftFree d@(DiagramParallelRL _ _ (h:|Nil))
  = let fp = finitePresentation abgFinPres in case (fp $ start h,fp $ end h) of
  (   GeneratorTo (DiagramChainTo _ (p:|_)) ns' _ _ _ _
    , GeneratorTo (DiagramChainTo _ (q:|q':|Nil)) ne' _ q'Coker _ lq
    ) -> CokernelLiftableFree (LimesInjective w'Cn w'Univ) w'Lft where

    ----------------------------------------
    -- constructing c -
    SliceFrom _ h' = lq (SliceFrom ns' (h*p))
    h'SliceTo      = SliceTo ne' h'
    q'SliceTo      = SliceTo ne' q'

    cSum       = limes (slfLimitsInjective abhSums)
                   (DiagramDiscrete (h'SliceTo:|q'SliceTo:|Nil))
    cSliceTo   = tip $ universalCone cSum

    ----------------------------------------
    -- evaluating c' -
    cCokerLft = abhCokernelFreeTo' cSliceTo
    cCoker    = clfCokernel cCokerLft
    c'        = cokernelFactor $ universalCone cCoker

    ----------------------------------------
    -- evaluating w' -
    w' = universalFactor q'Coker (ConeCokernel (diagram q'Coker) c')
    w'Cn = ConeCokernel d w'

    ----------------------------------------
    -- universal property w' -
    w'Univ (ConeCokernel _ x) = universalFactor cCoker cCone where
      cCone = ConeCokernel (diagram cCoker) (x*q)

    w'Lft :: Any k -> Liftable From (Free k) AbHom
    w'Lft k = case ats k of
      Ats -> LiftableFrom w' w'SlcFromLft where
        w'SlcFromLft f = SliceFrom nk (q*f') where
          SliceFrom nk f' = lift (clfLiftableFree cCokerLft k) f

--------------------------------------------------------------------------------
-- abhCokersLftFree -

-- | liftable free cokernels.
abhCokersLftFree :: ClfCokernels N1 AbHom
abhCokersLftFree = ClfCokernels abhCokernelLftFree

--------------------------------------------------------------------------------
-- abhCokernel -

-- | cokernel for a given additive homomorphism.
abhCokernel :: CokernelDiagram N1 AbHom -> Cokernel N1 AbHom
abhCokernel = clfCokernel . abhCokernelLftFree

--------------------------------------------------------------------------------
-- abhCokernels -

-- | cokernels for 'AbHom'. 
abhCokernels :: Cokernels N1 AbHom
abhCokernels = Limits abhCokernel

--------------------------------------------------------------------------------
-- isoSmithNormal -

-- | isomorphism to its smith normal group.
--
-- __Properties__ Let @g@ be in 'AbGroup', then holds:
--
-- (1) @'start' ('isoSmithNormal' g) '==' g@.
--
-- (2) @'end' ('isoSmithNormal' g)@ is smith normal (see definition t'AbGroup').
isoSmithNormal :: AbGroup -> Inv AbHom
isoSmithNormal g = Inv h h' where
  c  = limes abhCokernels (cokernelDiagram (zero (one ():>g)))
  h  = cokernelFactor $ universalCone c
  h' = universalFactor c (ConeCokernel (diagram c) (one g))


