# Changelog for `oalg-abg`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

## [1.0.0.0] - 2024-01-06

## [1.1.0.0] - 2024-02-01

## [1.3.0.0] - 2024-07-31

### Added
- Liftable cokernels

## [1.4.1.0] - 2024-09-03
### Added
- Liftable Z-Matrices
- Elements of abelian groups

## [1.5.0.1] - 2024-09-08
### Changed
- adapted to oalg-base-2.0.0.0
- replaced abgGeneratorTo and abgFinPres
- replaced abhCokernelLftFree by abhCokersLftFree
### Added
- abhSplitable, xAbhSomeFreeSlice

## [1.5.0.2] - 2024-09-18
### Added
- AbElement is instance of Ord

## [1.5.0.3] - 2024-09-22
### Extended
- zMatrixLft returns - if possible - non trivial solutions.

## [1.5.1.0] - 2024-09-01
### Adaption
- adaption to oalg-base-2.0.2.0

## [1.6.0.0] - 2025-01-26
### Adaption
- adaption to oalg-base-2.1.0.0

## [1.7.0.0] - 2025-01-30

### Added
- Instance HomVectorial and HomAlgerbaic for AbHomFree.

### Adaption
- adaption to oalg-base-2.2.0.0

## [1.8.0.0] - 2025-02-14

### Adaption
- adaption to oalg-base-2.3.0.0

## [2.0.0.0] - 2025-10-03

### Adaption
- adaption to oalg-base-3.0.0.0

## [2.0.0.2] - 2025-10-13

### Added
- Functions for conversion between Z-Vectors and abelian elements: abges, abgevec, vecabge
- Instance OrientdOpl for AbElement.
- Functions abgSomeFree, abgxs

## [2.0.0.3] - 2025-10-18

### Added
- instances OrdPoint and OrdRoot for AbElement.
