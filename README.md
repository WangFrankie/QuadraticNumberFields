# QuadraticNumberFields

[![DOI](https://zenodo.org/badge/1172123669.svg)](https://doi.org/10.5281/zenodo.21091163)
[![License](https://img.shields.io/github/license/WangFrankie/QuadraticNumberFields)](LICENSE)
[![Release](https://img.shields.io/github/v/release/WangFrankie/QuadraticNumberFields)](https://github.com/WangFrankie/QuadraticNumberFields/releases)

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
| `QuadraticNumberFields` | 7587 | 2858 | 10445 |
| `FormClassGroup` | 4946 | 1044 | 5990 |
| `BinaryQuadraticForms` | 3126 | 664 | 3790 |
| `QNFMathlib` | 2894 | 844 | 3738 |
| `Examples` | 1171 | 579 | 1750 |
| `ImaginaryClassNumberOne` | 1130 | 398 | 1528 |
| **Total** | **20854** | **6387** | **27241** |

### Library Tree

<details>
<summary><code>QuadraticNumberFields</code> (7587 code, 2858 comments, 10445 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── QuadraticNumberFields.lean` | 48 | 21 | 69 |
| `├── ClassGroup/` | 2492 | 681 | 3173 |
| `├── ContinuedFraction/` | 21 | 36 | 57 |
| `├── Euclidean/` | 52 | 25 | 77 |
| `├── Families/` | 38 | 49 | 87 |
| `├── Qsqrtd/` | 598 | 286 | 884 |
| `├── QuadraticField/` | 610 | 449 | 1059 |
| `├── RingOfIntegers/` | 790 | 364 | 1154 |
| `├── Splitting/` | 1672 | 501 | 2173 |
| `├── Units/` | 409 | 161 | 570 |
| `├── ZOnePlusSqrtdOverTwo/` | 127 | 50 | 177 |
| `└── Zsqrtd/` | 730 | 235 | 965 |
| **QuadraticNumberFields total** | **7587** | **2858** | **10445** |

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
<summary><code>QNFMathlib</code> (2894 code, 844 comments, 3738 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── QNFMathlib.lean` | 28 | 12 | 40 |
| `├── Algebra/` | 151 | 88 | 239 |
| `├── Data/` | 578 | 144 | 722 |
| `├── FieldTheory/` | 41 | 19 | 60 |
| `├── GroupTheory/` | 18 | 13 | 31 |
| `├── NumberTheory/` | 1251 | 272 | 1523 |
| `└── RingTheory/` | 827 | 296 | 1123 |
| **QNFMathlib total** | **2894** | **844** | **3738** |

</details>

<details>
<summary><code>Examples</code> (1171 code, 579 comments, 1750 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── Examples.lean` | 16 | 10 | 26 |
| `├── ClassGroupStructure.lean` | 3 | 11 | 14 |
| `├── ClassGroupStructure/` | 134 | 70 | 204 |
| `├── Counterexamples/` | 82 | 24 | 106 |
| `├── Smoke/` | 163 | 43 | 206 |
| `├── Sqrt17/` | 218 | 140 | 358 |
| `├── SqrtNeg21/` | 15 | 29 | 44 |
| `└── SqrtNeg5/` | 540 | 252 | 792 |
| **Examples total** | **1171** | **579** | **1750** |

</details>

<details>
<summary><code>ImaginaryClassNumberOne</code> (1130 code, 398 comments, 1528 total)</summary>

| Subtree | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `├── ImaginaryClassNumberOne.lean` | 8 | 10 | 18 |
| `├── ClassNumberOne.lean` | 133 | 50 | 183 |
| `├── ClassNumberOneByForms.lean` | 12 | 13 | 25 |
| `├── Diophantine.lean` | 399 | 65 | 464 |
| `├── Framework.lean` | 43 | 25 | 68 |
| `├── IdealReductions.lean` | 305 | 41 | 346 |
| `├── StarkHeegner.lean` | 102 | 71 | 173 |
| `└── WeberData/` | 128 | 123 | 251 |
| **ImaginaryClassNumberOne total** | **1130** | **398** | **1528** |

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
