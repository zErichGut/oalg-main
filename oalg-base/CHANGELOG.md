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
