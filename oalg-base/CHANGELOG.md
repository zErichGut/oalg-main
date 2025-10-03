# Changelog for `oalg-base`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## [Unreleased]

## [1.1.1.0] - 2023-11-19

### Added
- type for ordered structures.
- Foldable for sets.

## [1.1.2.0] - 2023-11-22

### Added
- free sums.

## [1.1.3.0] - 2023-11-27

### Change
- interface of free sums. Replacing Word by LinearCombination.

## [1.1.4.0] - 2023-12-19

### Added
- OAlg.Entity.Matrix.Vector
- OAlg.Entity.Sequence.CSequence

### Change
- OAlg.Entity.Sequence.ProductSymbol moved OAlg.Entity.Product.ProductSymbol

## [1.2.0.0] - 2024-01-05

### Adapttion
- ghc 9.4.7

## [1.2.1.0] - 2024-01-22

### Added
- Order releation for natruals
- Any natural is attestable
- XStandard for matrices over Z
- Liftable and CokernelLiftableFree

## [1.2.2.0] - 2024-07-31

### Added
- mtxDensity

## [2.0.0.0] - 2024-09-07

### Changed
- operational structures no longer have to throw a NotApplicable exception if
the application is not well defined. They also are allowed to throw a NotMultiplicable
- the module OAlg.Data.Generator has been replaced by OAlg.Data.FinitelyPresentable and the
type Generator to FinitePresentation. Further more the slice index has been relaxed and
the type of the liftable has been refined. Last but not least the dual concept of a GenaratorTo
has been defined by EmbeddingFrom.

### Added
- vectorial structure for Slice From entities.
- liftable cokernels for CokernelLiftableFree.
- maybeFinList

## [2.0.0.2] - 2024-09-22
### Changed
- data type Closer in module OAlg.Data.Ord changed to Closure.

## [2.0.1.2] - 2024-10-08

### Added
- general mappings for PSequences.
- FSequence for total sequences with finite support.
- PTree for efficient retrieving values from a partially defiend sequence.
- Validation for data Closure
- trFilter in OAlg.Data.Tree
- VectorSheaf
- Projectible instances for Sheaf and Path

### Changed
- the function lookup in OAl.Data.Tree to trLookup

### Resolved
- Orphan instance for Projectible Sheaf and Path by removing the general definition to Sum and Product.

## [2.0.2.1] - 2025-01-13

### Added
- class Functorial1
- class Filterable in OAlg.Data.Filterable.
- structure EntOrd for ordered entities.
- module OAlg.Data.Logical
- module OAlg.Category.Map
- module OAlg.Boolean.Definition: class Logical as base class for Booleans, class Erasable.
- classes PartiallyOrdered, Empty, Full in OAlg.Structure.PartiallyOrdered.Definition
- class Lattice in OAlg.Structure.Lattice.Definition.
- module OAlg.Entity.Seqeuence.Set: setPower, setIsEmpty, setIntersection, setDifference, setTakeN
  setFilter, instance Erasable (Set x)
- module OAlg.Entity.Sequence.Graph: gphTakeN, gphset, setgph, gphUnion, gphIntersection,
gphSetFilter, gphDifference, isSubGraph, instance Ord (Graph i x), Lattice (Graph a (Set b)),
instance Filterable (Graph i).
- Propositions for lattices, see OAlg.Structure.Lattice.Proposition
- instances Ord and PartiallyOrdered for Op.

### Changed
- the class POrd has been renamed to PartiallyOrdered and moved to
OAl.Structure.PartiallyOrdered.Definition.
- in the module OAlg.Entity.Definition: Empty to EntEmpty, empty to fromEmpty,
Empty2 to EntEmpty2, empty2 to fromEmpty2.

## [2.0.2.2] - 2025-01-22

### Added
- module OAlg.Limes.Exact.ConsZero
- module OAlg.Limes.Exact.Deviation

### Changed
- show for FinList

## [2.1.0.0] - 2025-01-26

### Added
- AlgebraicSemiring in the module OAlg.Structure.Algebraic.Definition.
- mapping cnzMap and cnztMap in the module OAlg.Limes.Exact.ConsZero.

### Changed
- eliminated the constraint for HomOriented and HomFibred being an instance of Entity2

## [2.2.0.0] - 2025-01-30

### Added
- Structure2 and Struct2 in the module OAlg.Structure.Definition.
- The constraint AlgebraicRing, AlgebraicField in the module OAlg.Structure.Algebraic.Definition.
- Algebraic structure for ConsZeroTrafo in the module OAlg.Limes.Exact.ConsZero.

### Changed
- Redesign of Hom's: Adaption of the various class definition for Hom's to the idiom
'Transformable' such that the implementation of concrete Hom's is strait forward (see for example
'GLApp') and the implementation for parameterized Hom's over a structure index need only the idiom
'Transformable...' to circumvent undecidable instances (see for example 'IdHom').
- Elimination of the idioms 'Embeddable' and 'Forgetful' such that only the Idiom
'Transformable' and 'Transformable...' are needed.
- Constraints for Transformation being Vectorial.

## [2.3.0.0] - 2025-02-14

Indroducing generic limits.

### Added
- The class Uiversal and UniversalApplicative in the module OAlg.Limes.Universal for generic limits.

### Changed
- HomOp contains only the constructors FromOpOp and ToOpOp and as such IsoOp is generated
by isoToOpOp ans its inverse isoFromOpOp.

## [3.0.0.0] - 2025-09-10

### Changed
- Complete revision of the concept of duality (see OAlg.Data.Dualisable)
- Introduction of generic limits.
- Introduction of generic applications. (see OAlg.Category.Application)
- Indroduction of disjunctive homomorphisms.

### Added
- OAlg.Limes.Exact

