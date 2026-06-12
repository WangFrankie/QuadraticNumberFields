# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields `ℚ(√d)`, their rings of
integers, discriminants, splitting behavior, and related class-number
infrastructure. The project is built on mathlib's `QuadraticAlgebra`.

## Imports

The stable, sorry-free public entry point is:

```lean
import QuadraticNumberFields
```

Work-in-progress and research scaffolding are kept separate:

```lean
import QuadraticNumberFields.Sketch
```

## Highlights

- Classification of quadratic fields by squarefree integer parameters.
- Classification of rings of integers:
  `ℤ[√d]` when `d % 4 ≠ 1`, and `ℤ[(1+√d)/2]` when `d % 4 = 1`.
- Discriminant formula: `Δ(ℚ(√d)) = if d % 4 = 1 then d else 4 * d`.
- Dedekind-domain characterization for the project-owned `ℤ[√d]` model.
- Galois, conjugation, totally real/totally complex/CM, prime-splitting, and
  concrete `ℤ[√(-5)]` ideal-theory examples.
- A basic class-number interface for standard quadratic fields.

## Documentation

- [Blueprint](https://numbertheory.cc/QuadraticNumberFields/) (fallback:
  [GitHub Pages](https://wangfrankie.github.io/QuadraticNumberFields-blueprint))
- [Library overview and main results](docs/library-overview.md)
- [Quadratic-field architecture](docs/design/quadratic-field-architecture.md)
- [Mathlib patch rules](docs/mathlib-patch-rules.md)

## Core Objects

- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0`
- `QuadraticField K`, the abstract quadratic-field layer
- `Zsqrtd d := QuadraticAlgebra ℤ d 0`, the project-owned `ℤ[√d]` model
- `ZOnePlusSqrtOverTwo k`, the `ℤ[(1+√d)/2]` model

Parameters are usually carried by explicit instances such as
`[Fact (Squarefree d)] [Fact (d ≠ 1)]`.

## Build

The Lean, mathlib, and repl versions are pinned in `lean-toolchain` and
`lakefile.toml`.

```bash
lake exe cache get
lake build
```

## Development Notes

- `QuadraticNumberFields.lean` re-exports completed, sorry-free public modules.
- `QuadraticNumberFields/Sketch.lean` collects unfinished modules and theorem
  skeletons.
- General-purpose facts intended for mathlib live under
  `QuadraticNumberFields/Mathlib/`.
- The project-owned `Zsqrtd` model is separate from mathlib's `_root_.Zsqrtd`.
  Use `QuadraticNumberFields/Zsqrtd/MathlibBridge.lean` only when an interface
  with mathlib's model is genuinely required.

## Code Statistics

| Module | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `QuadraticNumberFields/Splitting` | 1480 | 450 | 2194 |
| `QuadraticNumberFields/Zsqrtd` | 661 | 212 | 1016 |
| `QuadraticNumberFields/QuadraticField` | 586 | 397 | 1183 |
| `QuadraticNumberFields/Mathlib` | 512 | 323 | 995 |
| `QuadraticNumberFields/RingOfIntegers` | 511 | 304 | 1017 |
| `QuadraticNumberFields/Qsqrtd` | 488 | 264 | 903 |
| `QuadraticNumberFields/Examples` | 410 | 233 | 793 |
| `QuadraticNumberFields/Units` | 303 | 148 | 546 |
| `QuadraticNumberFields` | 283 | 77 | 401 |
| `QuadraticNumberFields/Heegner` | 148 | 76 | 260 |
| `QuadraticNumberFields/ZOnePlusSqrtdOverTwo` | 103 | 50 | 183 |
| `QuadraticNumberFields/Counterexamples` | 82 | 24 | 130 |
| `QuadraticNumberFields/Euclidean` | 52 | 25 | 93 |
| `QuadraticNumberFields/ClassGroup` | 49 | 75 | 166 |
| `QuadraticNumberFields/Families` | 38 | 49 | 116 |
| `QuadraticNumberFields/ContinuedFraction` | 21 | 36 | 75 |
| `QuadraticNumberFields/Sketch` | 7 | 27 | 43 |
| **Total** | **5734** | **2770** | **10114** |

## History

This project was originally developed at
[ClassificationOfIntegersOfQuadraticNumberFields](https://github.com/FrankieeW/ClassificationOfIntegersOfQuadraticNumberFields).
It has since been restructured and expanded in this repository.

## Zulip

- [Z[(1+sqrt(1+4k))/2] discussion](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
- [Quadratic number fields discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/quadratic.20number.20fields/)
