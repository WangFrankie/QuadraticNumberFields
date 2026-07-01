# QuadraticNumberFields

[![License](https://img.shields.io/github/license/WangFrankie/QuadraticNumberFields)](LICENSE)

This is the `qnf-genus-core` thesis branch of the Lean 4 formalisation.  It is
trimmed to the material needed for Chapter 6 of the MSc thesis:

1. the prime `2` filter for imaginary quadratic class-number-one problems;
2. the genus-theory prime-discriminant filter.

The branch keeps the dependency closure needed to state and check those two
filters: explicit quadratic fields `ℚ(√d)`, rings of integers, discriminants,
prime splitting, ideal-class tools, narrow class groups, and genus theory.

## Imports

```lean
import QuadraticNumberFields
import ImaginaryClassNumberOne
```

`QuadraticNumberFields` re-exports the retained core arithmetic and genus-theory
modules.  `ImaginaryClassNumberOne` is the small application layer for the two
filters; it deliberately does not include the full Baker--Heegner--Stark
provider layer.

## Retained Surface

- `QNFMathlib/`: local mathlib-style support needed by the retained modules.
- `QuadraticNumberFields/Qsqrtd/`: the standard coordinate model.
- `QuadraticNumberFields/QuadraticField/`: the abstract quadratic-field layer.
- `QuadraticNumberFields/RingOfIntegers/`: integral bases, norm, and
  discriminant formulas.
- `QuadraticNumberFields/Splitting/`: splitting, inertia, ramification, and the
  prime `2` cases.
- `QuadraticNumberFields/ClassGroup/`: ideal-class, small-norm, narrow-class,
  and genus-theory material.
- `ImaginaryClassNumberOne/IdealReductions.lean`: ideal-theoretic class-number-one
  reductions used by the prime `2` filter.

Removed from this branch are the binary-quadratic-form backend, computed
examples, notebooks, unit/family/continued-fraction scaffolding, and the deep
Weber/CM or Baker--Heegner--Stark provider files.

## Build

The Lean, mathlib, and repl versions are pinned in `lean-toolchain` and
`lakefile.toml`.

```bash
lake exe cache get
lake build
```

## Documentation

- [Library overview](docs/library-overview.md)
- [Quadratic-field architecture](docs/design/quadratic-field-architecture.md)
- [Mathlib patch rules](docs/mathlib-patch-rules.md)

## Citation

If you use this Lean formalisation, cite the repository metadata in
[CITATION.cff](CITATION.cff).
