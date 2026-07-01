# Library Overview

This page describes the retained surface of the `qnf-genus-core` branch.  The
branch is intentionally narrower than the main development: it keeps only the
Lean material needed for the MSc thesis section **Two Filters for Class Number
One**.

## Thesis Boundary

The retained formalisation supports two filters for imaginary quadratic
class-number-one questions:

1. the prime `2` filter, using splitting/ramification at `2`, principality under
   class number one, and explicit norm equations in the ring of integers;
2. the genus-theory filter, using prime discriminants, narrow class groups,
   genus characters, and the quotient by squares.

The branch stops at these filters.  It does not keep the binary-quadratic-form
class-group backend, reduced-form computations, notebooks, or the deep
Weber/CM and Baker--Heegner--Stark provider layer.

## Entry Points

```lean
import QuadraticNumberFields
import ImaginaryClassNumberOne
```

`QuadraticNumberFields` is the retained core library.  `ImaginaryClassNumberOne`
is a small application entry point for the two filters.

## Core Arithmetic

Files under `QuadraticNumberFields/Qsqrtd/` define the coordinate model
`Qsqrtd d := QuadraticAlgebra ℚ d 0`, together with trace, norm, conjugation,
automorphism, Galois, and infinite-place facts.

Files under `QuadraticNumberFields/QuadraticField/` provide the abstract
quadratic-field layer, squarefree parameter classification, transport across
`ℚ`-algebra equivalences, and ring-of-integers transport.

## Rings of Integers and Discriminants

Files under `QuadraticNumberFields/RingOfIntegers/` prove the integral-basis
classification for squarefree `d ≠ 1`:

- `ℤ[√d]` when `d % 4 ≠ 1`;
- `ℤ[(1+√d)/2]` when `d % 4 = 1`.

They also provide the discriminant formula
`Δ(ℚ(√d)) = if d % 4 = 1 then d else 4 * d` and the explicit norm APIs used by
the prime `2` filter.

## Prime Splitting

Files under `QuadraticNumberFields/Splitting/` contain splitting, inertia, and
ramification criteria for rational primes in quadratic fields.  The key retained
surface for Chapter 6 is the treatment of the prime `2`:

- `isSplit_two_of_mod_eight_eq_one`;
- `isInert_two_of_mod_eight_eq_five`;
- `isRamified_two_of_mod_four_ne_one`.

## Class Groups and Genus Theory

Files under `QuadraticNumberFields/ClassGroup/` keep the ideal-class interface,
Minkowski and small-norm tools, narrow class groups, and the genus-theory stack.
The genus-theory branch is organized around:

- prime-discriminant factors;
- genus characters;
- the narrow square quotient;
- ambiguous ideals;
- the class-number-one prime-discriminant sieve.

The public genus-theory entry point is
`QuadraticNumberFields/ClassGroup/GenusTheory.lean`.

## Two-Filter Application Layer

`ImaginaryClassNumberOne/IdealReductions.lean` contains the ideal-theoretic
class-number-one reductions used by the prime `2` filter:

- in the `d % 4 ≠ 1` branch, class number one forces `d = -1` or `d = -2`;
- in the `d % 8 = 1` branch, class number one forces `d = -7`;
- in the odd half-integral branch, ramified-prime norm obstructions reduce the
  class-number-one problem to a negative prime parameter.

The genus filter itself is retained in
`QuadraticNumberFields/ClassGroup/GenusTheory/Sieve.lean`.

## Removed Layers

The following layers are intentionally absent from this branch:

- `BinaryQuadraticForms/` and `FormClassGroup/`;
- `Examples/` and the notebook workflow;
- continued-fraction, Euclidean, unit, and real-family scaffolding;
- `ImaginaryClassNumberOne` files for the full Baker--Heegner--Stark provider
  route, including `StarkHeegner`, `Framework`, `Diophantine`, and `WeberData`;
- class-field, idèle, Cox-Euler, and Gaussian-integer support shims that were
  only used by the removed layers.
