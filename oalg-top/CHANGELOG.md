# Changelog for `oalg-top`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

## [0.2.0.0] - 2023-11-19

### Added
- The class Simplical.

### Changed
- Making the type for Complexe more generic.

## [0.4.0.0] - 2024-08-07

### Elimination
- Generic class Simplical, such that complexes are always based on simplices.

### Added
- Liftable cokernels for the homology groups.

## [1.0.0.0] - 2024-09-09

## Added
- the data structure Variance to measure the deviation of beeing exact.

### Added Functionality
- the boundary for a cycle, see hmgBoundary.
- the homology class for a cycle, see homologyClass.
- evaluation of a generater set for cycles of a given dimension, see hmgCycleGenSet.
- evaluation of a generater set for the homology group of a given dimension, see hmgGroupGenSet.
