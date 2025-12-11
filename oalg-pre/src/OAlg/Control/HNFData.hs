
{-# LANGUAGE StandaloneDeriving #-} 
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}

-- |
-- Module      : OAlg.Control.HNFData
-- Description : reducing a value to head normal form
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- reducing a value to head normal form. This is much weaker then "Control.DeepSeq".
module OAlg.Control.HNFData
  ( HNFValue(..), fromHNFValue

  , HNFData(..), hnfValue
  )
  where

import Control.Exception

--------------------------------------------------------------------------------
-- HNFValue -

-- | values in head normal form.
data HNFValue x = HNFValue x | forall e . Exception e => Failure e

deriving instance Show x => Show (HNFValue x)

instance Functor HNFValue where
  fmap f (HNFValue x) = HNFValue (f x)
  fmap _ (Failure e)  = Failure e

--------------------------------------------------------------------------------
-- fromHNFValue -

-- | from head normal form.
--
-- __Property__ Let @x'@ be in @'HNFValue' __x__@ then holds:
--
-- (1) If @x'@ matches @'HNFValue' x@ then the result of @'fromHNFValue' x'@ is @x@.
--
-- (2) If @x'@ matches @'Failure' e@ then evaluation @'fromHNFValue' x'@ will end up
-- in a throwing @e@.
fromHNFValue :: HNFValue x -> x
fromHNFValue hvx = case hvx of
  HNFValue x -> x
  Failure e -> throw e

--------------------------------------------------------------------------------
-- HNFData -

-- | data reducible to head normal form.
class HNFData x where
  -- | tries to reduce a value to its head normal form, throwing an 'Exception' for
  --   undefined values.
  rhnf :: x -> ()

--------------------------------------------------------------------------------
-- hnfValue -

-- | tries to reduce a value @x@ to its head normal form. If the reduction ends up in a 'SomeException'
-- @e@ then this will be catched and @'Failure' e@ will be returned, otherwise @'HNFValue' will be
-- returned.
hnfValue :: HNFData x => x -> IO (HNFValue x)
hnfValue x = case rhnf x of
              () -> return (HNFValue x)
            `catch` (\(e :: SomeException) -> return (Failure e))


instance HNFData () where
  rhnf () = ()

instance HNFData Bool where
  rhnf False = ()
  rhnf _     = ()
  
instance HNFData [x] where
  rhnf xs = case xs of
              [] -> ()
              _  -> ()
