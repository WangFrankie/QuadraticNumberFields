？

# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields `ℚ(√d)`, their rings of
integers, discriminants, splitting behavior, and related class-number
infrastructure. The project is built on mathlib's `QuadraticAlgebra`.

## Imports

The stable, sorry-free public entry point is:

```lean
import QuadraticNumberFields
```

App-layer entry points are separate Lake libraries:

```lean
import FormClassGroup
import ImaginaryClassNumberOne
import Examples
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

- `QuadraticNumberFields.lean` is the core quadratic-number-field entry point.
- `FormClassGroup.lean` re-exports the QNF-dependent binary-quadratic-form
  route to imaginary quadratic class groups.
- `ImaginaryClassNumberOne.lean` re-exports the Heegner class-number-one and
  Baker--Heegner--Stark app layer.
- `Examples.lean` re-exports concrete examples and computed class-group
  structure examples.
- `BinaryQuadraticForms.lean` re-exports the QNF-independent binary-quadratic-form
  machinery used by the class-group bridge.
- General-purpose facts intended for mathlib live under
  `QNFMathlib/`.
- The project-owned `Zsqrtd` model is separate from mathlib's `_root_.Zsqrtd`.
  Use `QuadraticNumberFields/Zsqrtd/MathlibBridge.lean` only when an interface
  with mathlib's model is genuinely required.

## Code Statistics

Counts exclude blank lines.

### Library Summary

| Library | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `QuadraticNumberFields` | 7298 | 2806 | 10104 |
| `FormClassGroup` | 4945 | 1044 | 5989 |
| `BinaryQuadraticForms` | 3330 | 701 | 4031 |
| `QNFMathlib` | 2521 | 693 | 3214 |
| `ImaginaryClassNumberOne` | 2494 | 704 | 3198 |
| `Examples` | 1159 | 584 | 1743 |
| **Total** | **21747** | **6532** | **28279** |

### Library Tree

<details>
<summary><code>QuadraticNumberFields</code> (7298 code, 2806 comments, 10104 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── QuadraticNumberFields.lean` | 44 | 21 | 65 |
| `├── ClassGroup/` | 1538 | 423 | 1961 |
| `├── ClassNumber/` | 411 | 92 | 503 |
| `├── ContinuedFraction/` | 21 | 36 | 57 |
| `├── Euclidean/` | 52 | 25 | 77 |
| `├── Families/` | 38 | 49 | 87 |
| `├── Qsqrtd/` | 531 | 283 | 814 |
| `├── QuadraticField/` | 586 | 397 | 983 |
| `├── QuadraticOrder.lean` | 3 | 9 | 12 |
| `├── QuadraticOrder/` | 139 | 126 | 265 |
| `├── RingOfIntegers/` | 847 | 375 | 1222 |
| `├── Splitting/` | 1679 | 502 | 2181 |
| `├── Units/` | 409 | 156 | 565 |
| `├── ZOnePlusSqrtdOverTwo/` | 270 | 77 | 347 |
| `└── Zsqrtd/` | 730 | 235 | 965 |
| **QuadraticNumberFields total** | **7298** | **2806** | **10104** |

</details>

<details>
<summary><code>FormClassGroup</code> (4945 code, 1044 comments, 5989 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── FormClassGroup.lean` | 13 | 10 | 23 |
| `├── ClassGroup/` | 852 | 208 | 1060 |
| `├── Computable/` | 927 | 205 | 1132 |
| `├── Computed.lean` | 126 | 56 | 182 |
| `├── Cox/` | 2927 | 527 | 3454 |
| `└── Gauss/` | 100 | 38 | 138 |
| **FormClassGroup total** | **4945** | **1044** | **5989** |

</details>

<details>
<summary><code>BinaryQuadraticForms</code> (3330 code, 701 comments, 4031 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── BinaryQuadraticForms.lean` | 14 | 10 | 24 |
| `├── Computable/` | 799 | 200 | 999 |
| `├── Core/` | 1612 | 285 | 1897 |
| `├── Cox/` | 289 | 64 | 353 |
| `└── Gauss/` | 616 | 142 | 758 |
| **BinaryQuadraticForms total** | **3330** | **701** | **4031** |

</details>

<details>
<summary><code>QNFMathlib</code> (2521 code, 693 comments, 3214 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── QNFMathlib.lean` | 25 | 12 | 37 |
| `├── Algebra/` | 161 | 90 | 251 |
| `├── Data/` | 605 | 156 | 761 |
| `├── FieldTheory/` | 41 | 19 | 60 |
| `├── GroupTheory/` | 18 | 13 | 31 |
| `├── NumberTheory/` | 1195 | 251 | 1446 |
| `└── RingTheory/` | 476 | 152 | 628 |
| **QNFMathlib total** | **2521** | **693** | **3214** |

</details>

<details>
<summary><code>ImaginaryClassNumberOne</code> (2494 code, 704 comments, 3198 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── ImaginaryClassNumberOne.lean` | 9 | 10 | 19 |
| `├── ClassNumberBridge.lean` | 26 | 20 | 46 |
| `├── ClassNumberOne.lean` | 132 | 52 | 184 |
| `├── ClassNumberOneByForms.lean` | 12 | 13 | 25 |
| `├── Diophantine.lean` | 399 | 65 | 464 |
| `├── Framework.lean` | 43 | 25 | 68 |
| `├── IdealReductions.lean` | 305 | 41 | 346 |
| `├── StarkHeegner.lean` | 102 | 75 | 177 |
| `└── WeberCM/` | 1466 | 403 | 1869 |
| **ImaginaryClassNumberOne total** | **2494** | **704** | **3198** |

</details>

<details>
<summary><code>Examples</code> (1159 code, 584 comments, 1743 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── Examples.lean` | 16 | 10 | 26 |
| `├── ClassGroupStructure.lean` | 3 | 11 | 14 |
| `├── ClassGroupStructure/` | 138 | 70 | 208 |
| `├── Counterexamples/` | 82 | 24 | 106 |
| `├── Smoke/` | 163 | 43 | 206 |
| `├── Sqrt17/` | 194 | 143 | 337 |
| `├── SqrtNeg21/` | 15 | 29 | 44 |
| `└── SqrtNeg5/` | 548 | 254 | 802 |
| **Examples total** | **1159** | **584** | **1743** |

</details>

## History

This project was originally developed at
[ClassificationOfIntegersOfQuadraticNumberFields](https://github.com/FrankieeW/ClassificationOfIntegersOfQuadraticNumberFields).
It has since been restructured and expanded in this repository.

## Zulip

- [Z[(1+sqrt(1+4k))/2] discussion](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
- [Quadratic number fields discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/quadratic.20number.20fields/)
