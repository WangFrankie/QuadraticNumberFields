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
- An ideal-theoretic class-number interface for standard quadratic fields, with
  form-based computation kept in a separate app-layer library.

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

## Notebook

The class-number reading notebook lives at `Examples/Notebook/ClassNumber.ipynb`.
It uses the Lean 4 Jupyter kernel and should be run from the repository root so
the pinned Lake environment is visible.

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements-notebook.txt
python -m lean4_jupyter.install --user
lake exe cache get
jupyter lab Examples/Notebook/ClassNumber.ipynb
```

## Development Notes

- `QuadraticNumberFields.lean` is the core quadratic-number-field entry point.
- `QuadraticNumberFields/ClassGroup/` owns the non-forms class-number,
  small-norm, Minkowski, and genus-theory interfaces.
- `FormClassGroup.lean` re-exports the QNF-dependent binary-quadratic-form
  route to imaginary quadratic class groups. It is a backend, not the core
  class-group layer.
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
| `QuadraticNumberFields` | 16874 | 3448 | 20322 |
| `FormClassGroup` | 4946 | 1044 | 5990 |
| `BinaryQuadraticForms` | 3126 | 664 | 3790 |
| `QNFMathlib` | 2743 | 801 | 3544 |
| `Examples` | 1179 | 579 | 1758 |
| `ImaginaryClassNumberOne` | 1117 | 395 | 1512 |
| **Total** | **29985** | **6931** | **36916** |

### Library Tree

<details>
<summary><code>QuadraticNumberFields</code> (16874 code, 3448 comments, 20322 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── QuadraticNumberFields.lean` | 48 | 21 | 69 |
| `├── ClassGroup/` | 11763 | 1287 | 13050 |
| `├── ContinuedFraction/` | 21 | 36 | 57 |
| `├── Euclidean/` | 52 | 25 | 77 |
| `├── Families/` | 38 | 49 | 87 |
| `├── Qsqrtd/` | 605 | 301 | 906 |
| `├── QuadraticField/` | 586 | 397 | 983 |
| `├── RingOfIntegers/` | 773 | 362 | 1135 |
| `├── Splitting/` | 1722 | 529 | 2251 |
| `├── Units/` | 409 | 156 | 565 |
| `├── ZOnePlusSqrtdOverTwo/` | 127 | 50 | 177 |
| `└── Zsqrtd/` | 730 | 235 | 965 |
| **QuadraticNumberFields total** | **16874** | **3448** | **20322** |

</details>

<details>
<summary><code>FormClassGroup</code> (4946 code, 1044 comments, 5990 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── FormClassGroup.lean` | 13 | 10 | 23 |
| `├── ClassGroup/` | 852 | 208 | 1060 |
| `├── Computable/` | 927 | 205 | 1132 |
| `├── Computed.lean` | 127 | 56 | 183 |
| `├── Cox/` | 2927 | 527 | 3454 |
| `└── Gauss/` | 100 | 38 | 138 |
| **FormClassGroup total** | **4946** | **1044** | **5990** |

</details>

<details>
<summary><code>BinaryQuadraticForms</code> (3126 code, 664 comments, 3790 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── BinaryQuadraticForms.lean` | 14 | 10 | 24 |
| `├── Computable/` | 812 | 201 | 1013 |
| `├── Core/` | 1395 | 247 | 1642 |
| `├── Cox/` | 289 | 64 | 353 |
| `└── Gauss/` | 616 | 142 | 758 |
| **BinaryQuadraticForms total** | **3126** | **664** | **3790** |

</details>

<details>
<summary><code>QNFMathlib</code> (2743 code, 801 comments, 3544 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── QNFMathlib.lean` | 30 | 12 | 42 |
| `├── Algebra/` | 151 | 88 | 239 |
| `├── Data/` | 578 | 144 | 722 |
| `├── FieldTheory/` | 41 | 19 | 60 |
| `├── GroupTheory/` | 18 | 13 | 31 |
| `├── NumberTheory/` | 1352 | 348 | 1700 |
| `└── RingTheory/` | 573 | 177 | 750 |
| **QNFMathlib total** | **2743** | **801** | **3544** |

</details>

<details>
<summary><code>Examples</code> (1179 code, 579 comments, 1758 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── Examples.lean` | 16 | 10 | 26 |
| `├── ClassGroupStructure.lean` | 3 | 11 | 14 |
| `├── ClassGroupStructure/` | 137 | 70 | 207 |
| `├── Counterexamples/` | 82 | 24 | 106 |
| `├── Smoke/` | 163 | 43 | 206 |
| `├── Sqrt17/` | 219 | 140 | 359 |
| `├── SqrtNeg21/` | 15 | 29 | 44 |
| `└── SqrtNeg5/` | 544 | 252 | 796 |
| **Examples total** | **1179** | **579** | **1758** |

</details>

<details>
<summary><code>ImaginaryClassNumberOne</code> (1117 code, 395 comments, 1512 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── ImaginaryClassNumberOne.lean` | 8 | 10 | 18 |
| `├── ClassNumberOne.lean` | 133 | 50 | 183 |
| `├── ClassNumberOneByForms.lean` | 12 | 13 | 25 |
| `├── Diophantine.lean` | 399 | 65 | 464 |
| `├── Framework.lean` | 43 | 25 | 68 |
| `├── IdealReductions.lean` | 305 | 41 | 346 |
| `├── StarkHeegner.lean` | 89 | 68 | 157 |
| `└── WeberData/` | 128 | 123 | 251 |
| **ImaginaryClassNumberOne total** | **1117** | **395** | **1512** |

</details>

## History

This project was originally developed at
[ClassificationOfIntegersOfQuadraticNumberFields](https://github.com/FrankieeW/ClassificationOfIntegersOfQuadraticNumberFields).
It has since been restructured and expanded in this repository.

## Zulip

- [Z[(1+sqrt(1+4k))/2] discussion](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
- [Quadratic number fields discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/quadratic.20number.20fields/)
