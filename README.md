# QuadraticNumberFields

[![DOI](https://zenodo.org/badge/1172123669.svg)](https://doi.org/10.5281/zenodo.21091163)
[![License](https://img.shields.io/github/license/WangFrankie/QuadraticNumberFields)](LICENSE)
[![Release](https://img.shields.io/github/v/release/WangFrankie/QuadraticNumberFields)](https://github.com/WangFrankie/QuadraticNumberFields/releases)

A Lean 4 formalization of quadratic number fields `ℚ(√d)`, their rings of
integers, discriminants, splitting behavior, and related class-number
infrastructure. The project is built on mathlib's `QuadraticAlgebra`.

> **Preserved Baker-Heegner-Stark development.** The branch
> `legacy/baker-heegner-stark` retains the partial class-number-one proof and its
> development history. The unconditional classification is still incomplete;
> further work is planned in a separate repository. See the
> [preservation record](docs/contributions.md#baker-heegner-stark-development)
> and [mathematical status](docs/design/class-number-one-roadmap.md).

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
- [Project implementations and upstream history](docs/contributions.md), including
  original proofs now covered by mathlib
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

The project uses Lean, mathlib, and repl `v4.35.0`, pinned in `lean-toolchain`
and `lakefile.toml`. The complete dependency revisions are recorded in
`lake-manifest.json`.

```bash
lake exe cache get
lake build
lake env lean scripts/check_core_axioms.lean
```

The axiom audit checks representative classification, discriminant, genus-theory,
form-class-group, and all nine Heegner class-number-one results. It rejects
dependencies on `sorryAx` or any axioms beyond `propext`, `Classical.choice`, and
`Quot.sound`. The conditional Baker--Heegner--Stark theorem is included in the
audit; its Weber existence hypothesis remains unproved.

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
| `QuadraticNumberFields` | 12182 | 3292 | 15474 |
| `FormClassGroup` | 4502 | 936 | 5438 |
| `QNFMathlib` | 4075 | 1063 | 5138 |
| `BinaryQuadraticForms` | 3125 | 668 | 3793 |
| `Examples` | 1258 | 577 | 1835 |
| `ImaginaryClassNumberOne` | 1109 | 394 | 1503 |
| **Total** | **26251** | **6930** | **33181** |

### Library Tree

<details>
<summary><code>QuadraticNumberFields</code> (12182 code, 3292 comments, 15474 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── QuadraticNumberFields.lean` | 59 | 21 | 80 |
| `├── ClassGroup/` | 6443 | 1032 | 7475 |
| `├── Euclidean/` | 52 | 25 | 77 |
| `├── Families/` | 18 | 24 | 42 |
| `├── Qsqrtd/` | 715 | 296 | 1011 |
| `├── QuadraticField/` | 609 | 449 | 1058 |
| `├── RingOfIntegers/` | 1053 | 417 | 1470 |
| `├── Splitting/` | 1965 | 582 | 2547 |
| `├── Units/` | 409 | 161 | 570 |
| `├── ZOnePlusSqrtdOverTwo/` | 128 | 50 | 178 |
| `└── Zsqrtd/` | 731 | 235 | 966 |
| **QuadraticNumberFields total** | **12182** | **3292** | **15474** |

</details>

<details>
<summary><code>FormClassGroup</code> (4502 code, 936 comments, 5438 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── FormClassGroup.lean` | 12 | 10 | 22 |
| `├── ClassGroup/` | 852 | 208 | 1060 |
| `├── Computable/` | 481 | 101 | 582 |
| `├── Computed.lean` | 103 | 49 | 152 |
| `├── Cox/` | 2954 | 530 | 3484 |
| `└── Gauss/` | 100 | 38 | 138 |
| **FormClassGroup total** | **4502** | **936** | **5438** |

</details>

<details>
<summary><code>QNFMathlib</code> (4075 code, 1063 comments, 5138 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── QNFMathlib.lean` | 32 | 12 | 44 |
| `├── Algebra/` | 146 | 87 | 233 |
| `├── Data/` | 578 | 144 | 722 |
| `├── FieldTheory/` | 38 | 21 | 59 |
| `├── GroupTheory/` | 97 | 34 | 131 |
| `├── NumberTheory/` | 1506 | 363 | 1869 |
| `└── RingTheory/` | 1678 | 402 | 2080 |
| **QNFMathlib total** | **4075** | **1063** | **5138** |

</details>

<details>
<summary><code>BinaryQuadraticForms</code> (3125 code, 668 comments, 3793 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── BinaryQuadraticForms.lean` | 14 | 10 | 24 |
| `├── Computable/` | 814 | 204 | 1018 |
| `├── Core/` | 1391 | 248 | 1639 |
| `├── Cox/` | 289 | 64 | 353 |
| `└── Gauss/` | 617 | 142 | 759 |
| **BinaryQuadraticForms total** | **3125** | **668** | **3793** |

</details>

<details>
<summary><code>Examples</code> (1258 code, 577 comments, 1835 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── Examples.lean` | 16 | 10 | 26 |
| `├── ClassGroupStructure.lean` | 2 | 11 | 13 |
| `├── ClassGroupStructure/` | 157 | 67 | 224 |
| `├── Counterexamples/` | 82 | 24 | 106 |
| `├── Smoke/` | 173 | 44 | 217 |
| `├── Sqrt17/` | 218 | 140 | 358 |
| `├── SqrtNeg21/` | 15 | 29 | 44 |
| `└── SqrtNeg5/` | 595 | 252 | 847 |
| **Examples total** | **1258** | **577** | **1835** |

</details>

<details>
<summary><code>ImaginaryClassNumberOne</code> (1109 code, 394 comments, 1503 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── ImaginaryClassNumberOne.lean` | 8 | 10 | 18 |
| `├── ClassNumberOne.lean` | 133 | 50 | 183 |
| `├── ClassNumberOneByForms.lean` | 12 | 13 | 25 |
| `├── Diophantine.lean` | 399 | 69 | 468 |
| `├── InertPrimes.lean` | 43 | 25 | 68 |
| `├── IdealReductions.lean` | 304 | 41 | 345 |
| `├── StarkHeegner.lean` | 80 | 63 | 143 |
| `└── Weber/` | 130 | 123 | 253 |
| **ImaginaryClassNumberOne total** | **1109** | **394** | **1503** |

</details>

## History

This project was originally developed at
[ClassificationOfIntegersOfQuadraticNumberFields](https://github.com/FrankieeW/ClassificationOfIntegersOfQuadraticNumberFields).
It has since been restructured and expanded in this repository.

## Zulip

- [Z[(1+sqrt(1+4k))/2] discussion](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
- [Quadratic number fields discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/quadratic.20number.20fields/)

## Citation

If you use this Lean formalization, please cite the Zenodo record or the
repository metadata in [CITATION.cff](CITATION.cff).

```bibtex
@software{wang_quadratic_number_fields_2026,
  author = {Wang, Frankie F.-C.},
  title = {{QuadraticNumberFields}: Lean 4 formalization of quadratic number fields},
  version = {v0.2.0},
  date = {2026-07-01},
  doi = {10.5281/zenodo.21091163},
  orcid = {0009-0003-3705-1549},
  url = {https://github.com/WangFrankie/QuadraticNumberFields},
}
```

Author ORCID:    <a
    id="cy-effective-orcid-url"
    class="underline"
     href="https://orcid.org/0009-0003-3705-1549"
     target="orcid.widget"
     rel="me noopener noreferrer"
     style="vertical-align: top">
     <img
        src="https://orcid.org/sites/default/files/images/orcid_16x16.png"
        style="width: 1em; margin-inline-start: 0.5em"
        alt="ORCID iD icon"/>
      https://orcid.org/0009-0003-3705-1549
    </a>
