# Changelog for `oalg-base`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## [Unreleased]

## [1.1.1.0] - 2023-11-19

	Added
	- type for ordered structures.
	- Foldable for sets.

## [1.1.2.0] - 2023-11-22

	Added
	- free sums.

## [1.1.3.0] - 2023-11-27
	Change
	- interface of free sums. Replacing Word by LinearCombination.

## [1.1.4.0] - 2023-12-19
	Added
	- OAlg.Entity.Matrix.Vector
	- OAlg.Entity.Sequence.CSequence

	Change
	- OAlg.Entity.Sequence.ProductSymbol moved OAlg.Entity.Product.ProductSymbol

## [1.2.0.0] - 2024-01-05
	Adapttion
	- ghc 9.4.7

## [1.2.1.0] - 2024-01-22
	Added
	- Order releation for natruals
	- Any natural is attestable
        - XStandard for matrices over Z
