# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields `ℚ(√d)` and the classification
of their ring of integers, built on mathlib's `QuadraticAlgebra`.

## Main Results

### Ring of Integers Classification

(`RingOfIntegers/Classification.lean`)

For squarefree `d ≠ 1`, the ring of integers `𝓞 (ℚ(√d))` is classified as:

- If `d % 4 ≠ 1`, then `𝓞 (ℚ(√d)) ≃+* ℤ[√d]`.
- If `d % 4 = 1`, writing `d = 1 + 4k`, then `𝓞 (ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.

Key declarations: `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`,
`ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`,
`ringOfIntegers_classification`.

Classical examples:
- **Gaussian integers** (`d = -1`): `𝓞 (ℚ(√(-1))) ≃+* ℤ[i]`
- **Eisenstein integers** (`d = -3`): `𝓞 (ℚ(√(-3))) ≃+* ℤ[ω]` where `ω = (1+√(-3))/2`

### Discriminant Formula

(`RingOfIntegers/Discriminant.lean`)

The number field discriminant of `ℚ(√d)` is computed as:

- `discr_formula`: `Δ(ℚ(√d)) = if d % 4 = 1 then d else 4 * d`

Examples: `Δ(ℚ(√(-1))) = -4`, `Δ(ℚ(√(-3))) = -3`, `Δ(ℚ(√(-5))) = -20`.

### Dedekind Domain Characterization

(`RingOfIntegers/ZsqrtdMathlibInstances.lean`)

For squarefree `d ≠ 1`:

- `isDedekindDomain_iff_mod_four_ne_one`: `ℤ√d` is a Dedekind domain if and only if `d % 4 ≠ 1`

This follows from the ring of integers classification — `ℤ√d` is a Dedekind domain
precisely when it equals the full ring of integers `𝓞 (ℚ(√d))`.

## Core Lean Objects

- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0` — the quadratic field `ℚ(√d)`
  (`Basic.lean`)
- Parameters: `[Fact (Squarefree d)] [Fact (d ≠ 1)]` — explicit `Fact` instances
  (`Parameters.lean`, `RingOfIntegers/CommonInstances.lean`)
- `Zsqrtd d` and `ZOnePlusSqrtOverTwo k` — the two candidate integral models
  (`RingOfIntegers/Zsqrtd.lean`, `RingOfIntegers/ZOnePlusSqrtOverTwo.lean`)

## Module Organization

The project is organized around a small number of medium-sized files. In the
ring-of-integers development, closely related material is usually grouped into a
single file and separated with `section`s, rather than split into many tiny
modules.

In particular:
- `Integrality.lean` develops the main integrality transport and half-integer
  normal form arguments.
- `TraceNorm.lean` isolates the trace/norm preliminaries used by the
  classification proofs.
- `Classification.lean`, `Norm.lean`, and `Discriminant.lean` each collect one
  main narrative, with internal `section`s for subresults.

## Mathematical Content

This project formalizes:
- Quadratic number fields as `Qsqrtd d := QuadraticAlgebra ℚ d 0`
- Parametrization via squarefree integers and uniqueness of the parameter
- Ring of integers classification (`ringOfIntegers_classification`)
- Discriminant formula (`discr_formula`)
- Dedekind domain characterization (`isDedekindDomain_iff_mod_four_ne_one`)
- Totally real / totally complex / CM field classification
- Integrality criteria via trace and norm
- Norm multiplicativity and unit criterion (`N(z) = ±1`)
- Ideal theory in `ℤ[√d]`: quotient by prime ideals, ramification
- Concrete verified examples for `ℤ[√(-5)]`: ideal factorization, primality, ramification/inertia

## Project Structure

```text
QuadraticNumberFields/
├── lakefile.toml
├── lean-toolchain
├── QuadraticNumberFields.lean        # Root import module
├── QuadraticNumberFields/
│   ├── Basic.lean                    # Qsqrtd type, norm, trace, field instances
│   ├── Instances.lean                # NumberField instance for quadratic extensions
│   ├── Parameters.lean               # Rescaling, squarefree normalization, uniqueness
│   ├── FieldClassification.lean      # Quadratic field ↔ squarefree parameter
│   ├── TotallyRealComplex.lean       # Totally real / complex / CM classification
│   ├── RingEquiv.lean                # Dedekind domain transfer via ring equivalences
│   ├── Euclidean/
│   │   └── Basic.lean                # Norm-Euclidean classification framework
│   ├── Examples/
│   │   └── ZsqrtdNeg5/
│   │       ├── Ideals.lean           # Ideal factorization and primality in ℤ[√(-5)]
│   │       └── RamificationInertia.lean  # Ramification indices and inertia degrees
│   └── RingOfIntegers/
│       ├── Classification.lean       # Main classification theorem
│       ├── CommonInstances.lean      # Fact instances for d = -1, -3, -5
│       ├── Discriminant.lean         # Discriminant formula
│       ├── HalfInt.lean              # Half-integer normal form (a'+b'√d)/2
│       ├── Integrality.lean          # Integrality transport and normal forms
│       ├── ModFour.lean              # Modulo-4 arithmetic lemmas
│       ├── Norm.lean                 # Norm formulas and unit criteria
│       ├── TraceNorm.lean            # Trace/norm integrality preliminaries
│       ├── ZOnePlusSqrtOverTwo.lean  # ℤ[(1+√d)/2] ring model
│       ├── Zsqrtd.lean               # ℤ[√d] ring model and mathlib bridge
│       ├── ZsqrtdIdeals.lean         # Ideal theory: membership, primality, quotients
│       └── ZsqrtdMathlibInstances.lean  # Dedekind domain for mathlib's ℤ√d
```

## Prerequisites

- [Lean 4](https://leanprover.github.io/) `v4.29.0-rc2`
- [mathlib](https://github.com/leanprover-community/mathlib4) `v4.29.0-rc2`
- [elan](https://github.com/leanprover/elan) (Lean version manager)

## Build Instructions

```bash
lake exe cache get  # Download mathlib cache (required, speeds up build significantly)
lake build
```

## History

This project was originally developed at [ClassificationOfIntegersOfQuadraticNumberFields](https://github.com/FrankieeW/ClassificationOfIntegersOfQuadraticNumberFields). It has since been restructured and expanded in this repository.

## Contributions to mathlib

- [PR #36347](https://github.com/leanprover-community/mathlib4/pull/36347): Define quadratic number fields as `QuadraticAlgebra ℚ d 0`
- [PR #36387](https://github.com/leanprover-community/mathlib4/pull/36387): Parameter uniqueness for quadratic fields

## Zulip

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
- [Quadratic number fields discussion (mathlib4 Zulip)](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/quadratic.20number.20fields/)
