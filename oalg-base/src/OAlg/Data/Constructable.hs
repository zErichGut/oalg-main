
{-# LANGUAGE TypeFamilies #-}

-- | Constructable types.
module OAlg.Data.Constructable
  (
    -- * Constructable
    Constructable(..), cmap
    -- * Exposable
  , Exposable(..), restrict
    
  )
  where 


--------------------------------------------------------------------------------
-- Exposable -

-- | types with an associated /form/ type and a function 'form' which expose its values
--   to its /form/.
class Exposable x where
  -- | the form.
  type Form x

  -- | the associated form.
  form :: x -> Form x

--------------------------------------------------------------------------------
-- restrict -

-- | restriction of a @f@ in @'Form' __x__ -> y@.
restrict :: Exposable x => (Form x -> y) -> x -> y
restrict f = f . form

  
--------------------------------------------------------------------------------
-- Constructable -

-- | types with an associated /form/, which serves as a /blueprint/ to construct a
--   corresponding value.
--
--  A commen setting for this structure is a module with a reducible type __@f@__
--  (see @'OAlg.Data.Reducible'@) with public constructors - which serves as a form to be
--  filled out - and in the same module a type @e@ with a private constructor - lets say
--  @E@ - to hold the 'OAlg.Data.Reducible.reduced' @f@. Than an implementation would be
--
-- > make f = E (reduce f)
--
-- and
--
-- > form (E f) = f
--
--  __Property__ Let __@x@__ be an instance of the class 'Constructable' than holds:
--  For all @x@ in __@x@__ holds: @'make' ('form' x) '==' x@.
class Exposable x => Constructable x where
  -- | constructor.
  make :: Form x -> x

--------------------------------------------------------------------------------
-- cmap -

-- | restriction of a @f@ in @'Form' __x__ -> 'Form' __y__@. 
cmap :: (Constructable x, Constructable y) => (Form x -> Form y) -> x -> y
cmap f = make . f . form

