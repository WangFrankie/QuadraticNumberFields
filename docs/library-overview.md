# Library Overview

This document records the detailed result map for `QuadraticNumberFields`.
The repository README is intentionally short; this page carries the longer
module and declaration-level overview.

## Main Results

### Quadratic Field Classification

Files: `QuadraticNumberFields/QuadraticField/Classification.lean`,
`QuadraticNumberFields/QuadraticField/Parameters.lean`

The abstract layer classifies quadratic fields over `ℚ` by squarefree integer
parameters:

- every abstract quadratic field is isomorphic to `Qsqrtd (d : ℚ)` for some
  squarefree integer `d ≠ 1`;
- a field over `ℚ` is quadratic if and only if it is isomorphic to such a
  normalized standard model;
- squarefree parameters are unique up to the expected square-rescaling
  relation.

Key declarations:

- `exists_squarefree_int_param_of_isQuadraticField`
- `exists_algEquiv_qsqrtd`
- `exists_ringEquiv_qsqrtd`
- `exists_isStandardParameter`
- `isQuadraticField_iff_exists_squarefree_int_param`

### Abstract Quadratic-Field Infrastructure

Files: `QuadraticNumberFields/QuadraticField/Basic.lean`,
`QuadraticNumberFields/QuadraticField/Category.lean`,
`QuadraticNumberFields/QuadraticField/Conj.lean`,
`QuadraticNumberFields/QuadraticField/Transport.lean`

The project provides an abstract `QuadraticField K` layer and a bundled
`QuadraticFieldCat` category. It also includes:

- transport of quadratic-field structure across `ℚ`-algebra equivalences;
- transport of trace, norm, discriminants, rings of integers, Dedekind-domain
  properties, and infinite-place properties;
- abstract conjugation and trace/norm identities;
- the fact that the automorphism group of a quadratic field consists of the
  identity and conjugation.

Key declarations include `QuadraticField.finrank_eq_two`,
`QuadraticFieldCat`, `QuadraticField.ringOfIntegersEquivOfAlgEquiv`,
`QuadraticField.discr_eq_of_algEquiv`, `QuadraticField.univ_aut_eq_pair`,
`QuadraticField.add_conj_eq_trace_image`, and
`QuadraticField.mul_conj_eq_norm_image`.

### Standard Model API

Files under `QuadraticNumberFields/Qsqrtd/`

For the coordinate model `Qsqrtd d := QuadraticAlgebra ℚ d 0`, the library
develops:

- trace and norm formulas;
- norm as a monoid homomorphism and on units;
- non-field examples at `d = 0` and `d = 1`;
- parameter-rescaling equivalences;
- conjugation and the automorphism dichotomy.

Key declarations include `Qsqrtd.trace_eq_two_re`, `Qsqrtd.normHom_apply`,
`Qsqrtd.zero_not_isField`, `Qsqrtd.one_not_isField`,
`Qsqrtd.ringEquiv_param_rel`, `Qsqrtd.algEquiv_param_rel`, and
`Qsqrtd.algEquiv_self_eq_refl_or_star`.

### Ring of Integers Classification

File: `QuadraticNumberFields/RingOfIntegers/Classification.lean`

For squarefree `d ≠ 1`, the ring of integers of `ℚ(√d)` is classified as:

- If `d % 4 ≠ 1`, then `𝓞 (ℚ(√d)) ≃+* ℤ[√d]`.
- If `d % 4 = 1`, writing `d = 1 + 4k`, then
  `𝓞 (ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.

Key declarations:

- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`
- `ringOfIntegers_classification`
- `ringOfIntegers_classification_of_ringEquiv_qsqrtd`
- `exists_ringOfIntegers_classification_of_quadraticField`

Classical examples include:

- Gaussian integers, `d = -1`: `𝓞 (ℚ(√(-1))) ≃+* ℤ[i]`
- Eisenstein integers, `d = -3`:
  `𝓞 (ℚ(√(-3))) ≃+* ℤ[(1+√(-3))/2]`

### General Quadratic-Algebra Images, Conductors, and Indices

Files: `QNFMathlib/Algebra/QuadraticAlgebra/Conductor.lean`,
`QNFMathlib/Algebra/QuadraticAlgebra/Index.lean`

For any commutative ring `R` and `x : QuadraticAlgebra R a b`, membership in
`Algebra.adjoin R {x}` is equivalent to divisibility of the second coordinate
by `x.im`. Its conductor is `Ideal.span {algebraMap R _ x.im}`. No domain,
regularity, injectivity, or nonzero hypothesis is required.

For any algebra homomorphism between quadratic algebras, its range is generated
by the image of `omega`, and the same divisibility criterion describes it.
Over `ℤ`, its additive index is `Int.natAbs (f omega).im`, the absolute
determinant in the canonical bases. When the determinant is zero, the index
is zero, the convention for an infinite quotient.

Key declarations in namespace `QuadraticAlgebra`:

- `mem_adjoin_singleton_iff_dvd_im`, `conductor_eq_span_im`
- `range_algHom_eq_adjoin`, `mem_range_algHom_iff_dvd_im`
- `index_range_algHom`

These are mathlib-facing results, independent of the QNF coordinate models.
They reuse mathlib's existing quadratic-algebra, conductor, and determinant machinery.

`QNFMathlib/RingTheory/Order/Basic.lean` defines `Subalgebra.IsOrder`: finite generation
over the base ring and full span over the ambient scalar ring. It imposes no degree
or fraction-field hypothesis. `QNFMathlib/Algebra/QuadraticAlgebra/Order.lean` defines
`Subalgebra.IsQuadraticOrder` as a `ℤ`-order in a degree-two `ℚ`-algebra, including
split and reducible algebras.

The image of `ℤ[x]` under `QuadraticAlgebra.toRat` is a quadratic order iff `x.im ≠ 0`
(`isQuadraticOrder_map_adjoin_iff`). A model homomorphism's range gives a quadratic
order iff `(f omega).im ≠ 0` (`isQuadraticOrder_map_range_iff`), equivalently iff its
additive index is nonzero (`isQuadraticOrder_map_range_iff_index_ne_zero`).
The integral model itself is an order (`isQuadraticOrder_range_toRat`).

`QNFMathlib/NumberTheory/NumberField/Order.lean` proves
`NumberField.isOrder_integralClosure`: number-field rings of integers are `ℤ`-orders.
`QuadraticNumberFields/QuadraticField/RingOfIntegers.lean` specializes this to
`QuadraticField.isQuadraticOrder_integralClosure`, for any `ℚ`-algebra structure.

### Quadratic Suborder Inclusion and Conductor

Files: `QuadraticNumberFields/ZOnePlusSqrtdOverTwo/Inclusion.lean`,
`QuadraticNumberFields/ZOnePlusSqrtdOverTwo/Conductor.lean`

For arbitrary integers `d, k` with `d = 1 + 4*k`, the canonical algebra map
`ZOnePlusSqrtdOverTwo.fromZsqrtd` sends the square-root generator to `2ω - 1`.
In coordinates it sends `(a,b)` to `(a-b,2b)`. It is injective, its image
consists exactly of elements with even second coordinate, and its additive
index is two.
The map is an instantiation of mathlib's `QuadraticAlgebra.changeGenerator`,
and injectivity uses `changeGenerator_injective`. The image, conductor, and
index results specialize the general theorems above.

The image is `Algebra.adjoin ℤ {2ω - 1}`. Using mathlib's existing `conductor`
API, the conductor of this subalgebra in `ZOnePlusSqrtdOverTwo k` is
`Ideal.span {2}`; membership is equivalent to both coordinates being even.
These statements include real and reducible quadratic models. They neither
require nor establish that the model is a domain or a full ring of integers.
After mapping into the rational model, the image is a quadratic order.

Key declarations in namespace `ZOnePlusSqrtdOverTwo`:

- `fromZsqrtd`, `fromZsqrtd_re`, `fromZsqrtd_im`
- `fromZsqrtd_injective`, `mem_range_fromZsqrtd_iff`
- `range_fromZsqrtd`, `index_range_fromZsqrtd`
- `mem_conductor_iff_even_coordinates`, `conductor_eq_span_two`
- `isQuadraticOrder_range_fromZsqrtd`

The source and generalization history is recorded in
[Project implementations and upstream history](contributions.md#quadratic-model-suborder-inclusion-and-conductor).

### Discriminant Formula

File: `QuadraticNumberFields/RingOfIntegers/Discriminant.lean`

The number-field discriminant is computed by:

- `discr_formula`: `Δ(ℚ(√d)) = if d % 4 = 1 then d else 4 * d`
- `discr_formula_of_algEquiv_qsqrtd`
- `exists_discr_formula_of_quadraticField`

Examples: `Δ(ℚ(√(-1))) = -4`, `Δ(ℚ(√(-3))) = -3`, and
`Δ(ℚ(√(-5))) = -20`.

### Norms and Units

File: `QuadraticNumberFields/RingOfIntegers/Norm.lean`

The ring-of-integers development includes multiplicativity and unit criteria for
the explicit integral models:

- `norm_mul`
- `norm_zsqrtd`
- `norm_mul_zsqrtd`
- `norm_zOnePlusSqrtOverTwo`
- `isUnit_zsqrtd_iff_norm_eq_one_or_neg_one`
- `isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one`

### Dedekind Domain Characterization

Files: `QuadraticNumberFields/Zsqrtd/Dedekind.lean`,
`QuadraticNumberFields/Zsqrtd/MathlibInstances.lean`

For squarefree `d ≠ 1`:

- `QuadraticNumberFields.Zsqrtd.isDedekindDomain_iff_mod_four_ne_one`: the
  project model `ℤ[√d]` is a Dedekind domain if and only if `d % 4 ≠ 1`;
- `isDedekindDomain_iff_mod_four_ne_one`: mathlib's `ℤ√d` satisfies the same
  characterization after transport across the bridge.

The project owns its own `ℤ[√d]` model and keeps the bridge to mathlib's `ℤ√d`
thin and isolated in `QuadraticNumberFields/Zsqrtd/MathlibBridge.lean`.

### Galois Group of a Quadratic Field

Files: `QuadraticNumberFields/Qsqrtd/Automorphism.lean`,
`QuadraticNumberFields/Qsqrtd/Galois.lean`

For any abstract quadratic field, and for the standard model as a specialization,
the `ℚ`-automorphism group has order two and is cyclic:

- `QuadraticField.card_aut_eq_two`
- `QuadraticField.galEquivZMod2`
- `Qsqrtd.card_aut_eq_two`
- `Qsqrtd.galEquivZMod2`
- `Qsqrtd.algEquiv_self_eq_refl_or_star`

### Infinite Places and CM Behavior

File: `QuadraticNumberFields/Qsqrtd/TotallyRealComplex.lean`

The sign of the squarefree parameter controls the infinite-place behavior:

- if `0 < d`, then `Q(√d)` is totally real;
- if `d < 0`, then `Q(√d)` is totally complex and a CM field;
- every abstract quadratic field is transported to one of these two cases after
  choosing a standard parameter.

Key declarations:

- `Qsqrtd.isTotallyReal`
- `Qsqrtd.isTotallyComplex`
- `Qsqrtd.isCMField`
- `QuadraticField.exists_totallyReal_or_totallyComplex`

### Prime Splitting

Files under `QuadraticNumberFields/Splitting/`

The stable library includes a prime-splitting development for quadratic number
fields. The concrete `Qsqrtd d` layer gives explicit split, inert, and ramified
criteria, while the abstract quadratic-field layer records the general
quadratic-extension trichotomy for rings of integers.

Key declarations:

- `Ideal.split_or_inert_or_ramified`
- `QuadraticNumberFields.Splitting.split_or_inert_or_ramified`
- `QuadraticNumberFields.Splitting.splitting_classification`
- `QuadraticNumberFields.Splitting.isSplit_iff_legendreSym_eq_one`
- `QuadraticNumberFields.Splitting.isInert_iff_legendreSym_eq_neg_one`
- `QuadraticNumberFields.Splitting.isRamified_of_dvd`
- `QuadraticNumberFields.Splitting.isSplit_two_of_mod_eight_eq_one`
- `QuadraticNumberFields.Splitting.isInert_two_of_mod_eight_eq_five`
- `QuadraticNumberFields.Splitting.isRamified_two_of_mod_four_ne_one`

### Monogenicity of Rings of Integers

File: `QuadraticNumberFields/Splitting/Qsqrtd/Monogenic.lean`

The ring of integers of the standard model is packaged with a generator `θ`,
minimal-polynomial formulas for both congruence branches, and the
Kummer-Dedekind exponent condition:

- `QuadraticNumberFields.Splitting.adjoin_generator_eq_top`
- `QuadraticNumberFields.Splitting.exponent_generator_eq_one`
- `QuadraticNumberFields.Splitting.not_dvd_exponent_generator`
- `QuadraticNumberFields.Splitting.minpoly_generator`

### Ideal Theory in `ℤ[√d]`

File: `QuadraticNumberFields/Zsqrtd/Ideals.lean`

For a prime `p` with `p ∣ (d - 1)`, the project proves membership criteria,
quotient descriptions, comap formulas, and primality for the ideals
`(p, 1-√d)` and `(p, 1+√d)`.

Key declarations:

- `Zsqrtd.Ideal.mem_span_p_one_minus_sqrtd_iff`
- `Zsqrtd.Ideal.mem_span_p_one_plus_sqrtd_iff`
- `Zsqrtd.Ideal.isPrime_span_p_one_minus_sqrtd`
- `Zsqrtd.Ideal.isPrime_span_p_one_plus_sqrtd`
- `Zsqrtd.Ideal.quotEquivZModP`
- `Zsqrtd.Ideal.quotEquivZModPNeg`
- `Zsqrtd.Ideal.comap_span_p_one_minus_sqrtd`
- `Zsqrtd.Ideal.comap_span_p_one_plus_sqrtd`

### Concrete `ℤ[√(-5)]` Examples

Files under `Examples/SqrtNeg5/`

The library includes verified computations in `ℤ[√(-5)]`, including:

- `(2) = (2, 1+√(-5))²`;
- `(3) = (3, 1+√(-5)) · (3, 1-√(-5))`;
- factorizations of `(1+√(-5))` and `(1-√(-5))`;
- primality of the relevant ideals above `2` and `3`;
- ramification and inertia degrees for the selected primes.

Key declarations include `factorization_of_two`,
`factorization_of_three`, `factorization_of_one_plus_sqrtd`,
`factorization_of_one_minus_sqrtd`, `ramificationIdx_P2`,
`ramificationIdx_P3₁`, `ramificationIdx_P3₂`, `inertiaDeg_P2`,
`inertiaDeg_P3₁`, and `inertiaDeg_P3₂`.

### Class-Number Interface

File: `QuadraticNumberFields/ClassNumber.lean`

The stable library specializes mathlib's Minkowski ideal-class representative
bound to `Qsqrtd d` and owns the unified class-number interface:

- `classNumberQsqrtd`
- `Qsqrtd.minkowskiBound`
- `Qsqrtd.exists_ideal_in_class_of_norm_le`
- `Qsqrtd.exists_ideal_in_class_of_norm_le_imaginary`
- `Qsqrtd.exists_ideal_in_class_of_norm_le_real`

The Heegner wrappers for this interface live in
`ImaginaryClassNumberOne/ClassNumberBridge.lean`, while the reduced-form
cardinality bridge lives under `FormClassGroup/ClassGroup/`.

### Genus Theory

Files under `QuadraticNumberFields/ClassGroup/GenusTheory/`

The library develops the classical genus theory of quadratic fields from
signed prime discriminants and Kronecker characters. It proves surjectivity of
the genus-character map, the narrow `2`-rank formula, the principal genus
theorem, and the corresponding ordinary class-group formulas. The resulting
prime-shape sieve is used by the Baker--Heegner--Stark forward direction. The
same two-torsion count separates the order-four class groups of `ℚ(√-14)`
(cyclic) and `ℚ(√-21)` (Klein four) in
`Examples/ClassGroupStructure/Computations.lean`.

Key declarations:

- `genusCharacterMap_surjective`
- `twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one`
- `genusCharacterMap_ker_eq_square`
- `twoRank_classGroup_eq_ramifiedPrimeCount_sub_two_of_fundamentalUnit_norm_one`
- `classNumber_eq_one_imp_parameter_prime_shape`

## Core Lean Objects

- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0`
  (`QuadraticNumberFields/Qsqrtd/Basic.lean`)
- `QuadraticField K`, the abstract quadratic-field layer
  (`QuadraticNumberFields/QuadraticField/`)
- `Zsqrtd d := QuadraticAlgebra ℤ d 0`, the project-owned `ℤ[√d]` model
  (`QuadraticNumberFields/Zsqrtd/Basic.lean`)
- `ZOnePlusSqrtOverTwo k`, the `ℤ[(1+√d)/2]` model
  (`QuadraticNumberFields/ZOnePlusSqrtOverTwo/Basic.lean`)
- Parameters are usually carried by explicit instances such as
  `[Fact (Squarefree d)] [Fact (d ≠ 1)]`.

The intended architecture is:

- `QuadraticField K` is the abstract object of study.
- `Qsqrtd d` is the standard coordinate model used for calculation.
- `QuadraticFieldCat` organizes isomorphisms, functors, transport, and
  classification.

See `design/quadratic-field-architecture.md` for the design notes.

## Mathematical Content

The completed public library currently includes:

- basic `Qsqrtd` definitions, trace, norm, conjugation, automorphisms, and
  Galois facts
- parametrization of quadratic fields by squarefree integers
- classification and transport for abstract quadratic fields
- ring-of-integers classification
- discriminant formula
- Dedekind-domain characterization for `ℤ[√d]`
- ideal theory and quotient computations for `ℤ[√d]`
- prime splitting in quadratic number fields
- totally real, totally complex, and CM behavior
- concrete verified examples for `ℤ[√(-5)]`
- a basic class-number interface
- narrow and ordinary genus theory for quadratic fields

App-layer libraries contain form-class-group computations, class-number-one
results, examples, and remaining research-oriented scaffolding.

## Project Structure

```text
.
├── lakefile.toml
├── lean-toolchain
├── QNFMathlib.lean                   # shared local mathlib-shim re-exports
├── QNFMathlib/                       # temporary material destined for mathlib
├── BinaryQuadraticForms.lean         # pure binary-quadratic-form entry point
├── BinaryQuadraticForms/             # QNF-independent BQF machinery
│   ├── Core/                         # action, reduction, classes, enumeration
│   ├── Cox/                          # pure ideal-relation arithmetic
│   ├── Gauss/                        # pure Gauss composition
│   └── Computable/                   # executable composition/reduction
├── QuadraticNumberFields.lean        # stable, sorry-free public entry point
├── QuadraticNumberFields/
│   ├── Qsqrtd/                       # concrete ℚ(√d) coordinate model
│   │   ├── Basic.lean
│   │   ├── TraceNorm.lean
│   │   ├── Automorphism.lean
│   │   ├── Galois.lean
│   │   ├── Equiv.lean
│   │   └── TotallyRealComplex.lean
│   ├── QuadraticField/               # abstract quadratic-field layer
│   │   ├── Basic.lean
│   │   ├── Parameters.lean
│   │   ├── SqfreeParam.lean
│   │   ├── Classification.lean
│   │   ├── Category.lean
│   │   ├── Conj.lean
│   │   ├── Transport.lean
│   │   └── RingOfIntegers.lean
│   ├── RingOfIntegers/               # integer-ring classification
│   │   ├── Basic.lean
│   │   ├── ModFour.lean
│   │   ├── HalfInt.lean
│   │   ├── CommonInstances.lean
│   │   ├── Integrality.lean
│   │   ├── Classification.lean
│   │   ├── Norm.lean
│   │   └── Discriminant.lean
│   ├── Zsqrtd/                       # project-owned ℤ[√d] model
│   │   ├── Basic.lean
│   │   ├── Dedekind.lean
│   │   ├── Ideals.lean
│   │   ├── MathlibBridge.lean
│   │   └── MathlibInstances.lean
│   ├── ZOnePlusSqrtOverTwo/
│   │   └── Basic.lean
│   ├── Splitting/                    # prime splitting
│   ├── ClassNumber/                  # core class-number interface
│   ├── ClassGroup/                   # class groups, ambiguous ideals, genus theory
│   ├── Units/                        # unit and Pell scaffolding
│   ├── Families/                     # real-quadratic family scaffolding
│   └── Euclidean/                    # norm-Euclidean skeleton
├── FormClassGroup.lean               # QNF-dependent BQF/class-group bridge
├── FormClassGroup/
│   ├── Cox/
│   ├── Gauss/
│   ├── ClassGroup/
│   └── Computable/
├── ImaginaryClassNumberOne.lean      # Heegner and Baker--Heegner--Stark layer
├── ImaginaryClassNumberOne/
│   └── WeberData/
├── Examples.lean                     # concrete examples entry point
├── Examples/
│   └── SqrtNeg5/                     # verified ℤ[√(-5)] examples
└── docs/
    ├── design/
    ├── contributions.md
    ├── library-overview.md
    └── mathlib-patch-rules.md
```

## Contributions to mathlib

Project implementations of general-purpose facts intended for mathlib live under
`QNFMathlib/`. The project depends on upstream mathlib through Lake. When an
upstream implementation replaces a local one, the original statement, proof,
author, and source remain documented in
[Project implementations and upstream history](contributions.md). This includes
independent project implementations as well as submissions to mathlib.

The following submissions by Frankie Wang remain open as of 2026-10-16:

- [PR #36347](https://github.com/leanprover-community/mathlib4/pull/36347):
  Define quadratic number fields as `QuadraticAlgebra ℚ d 0`
- [PR #36387](https://github.com/leanprover-community/mathlib4/pull/36387):
  Parameter uniqueness for quadratic fields (draft)
