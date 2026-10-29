# Project implementations and upstream history

This record preserves work implemented in QuadraticNumberFields, including
independent implementations later covered by mathlib. A result remains part of
the project's implementation history when its active implementation moves to a
dependency. Contributions submitted to mathlib are recorded separately below.

Each replacement records the project author, original statement and proof,
immutable source, current provider, and surviving project application. The
historical excerpts retain their original context and the project's Apache 2.0
license; they are documentation rather than additional registered instances.
See the [project citation](../README.md#citation) when citing this formalization.

## Quadratic algebras as quadratic extensions

**Project implementation:** Frankie Wang (`WangFrankie`), generalized on
2026-06-02 in
[commit `ce5cbcb`](https://github.com/WangFrankie/QuadraticNumberFields/commit/ce5cbcb594cee1cddb42f03e25dbcaeedb4d9abc).
An earlier rational-base implementation is preserved in
[commit `abcfe47`](https://github.com/WangFrankie/QuadraticNumberFields/blob/abcfe47b270675137e917eae1ad672992399d297/Lean/QuadraticNumberFields/Instances.lean#L58-L66).

The generalized implementation established
`Algebra.IsQuadraticExtension R (QuadraticAlgebra R a b)` over a commutative
semiring with the strong rank condition. Its
[original source](https://github.com/WangFrankie/QuadraticNumberFields/blob/ce5cbcb594cee1cddb42f03e25dbcaeedb4d9abc/QuadraticNumberFields/Mathlib/Algebra/QuadraticAlgebra/Defs.lean#L21-L30)
is preserved here, within the original `namespace QuadraticAlgebra`:

```lean
section IsQuadraticExtension

variable {R : Type*} [CommSemiring R] [StrongRankCondition R] (a b : R)

/-- A quadratic algebra is a quadratic extension of its base ring. -/
instance instIsQuadraticExtension :
    Algebra.IsQuadraticExtension R (QuadraticAlgebra R a b) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two a b

end IsQuadraticExtension
```

**Current provider:** mathlib's `QuadraticAlgebra.instIsQuadraticExtension` in
[`Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/QuadraticAlgebra/IsQuadraticExtension.lean#L28-L38).
That upstream implementation is credited to Xavier Roblot and was added in
[commit `cda8086`](https://github.com/leanprover-community/mathlib4/commit/cda8086284838a2432f0a2b6687eb9bdb6496576)
([mathlib PR #42554](https://github.com/leanprover-community/mathlib4/pull/42554)).
This entry records the project's own earlier implementation and the upstream
implementation's attribution separately.

The v4.35.0 migration imports that provider from
[`QNFMathlib/Algebra/QuadraticAlgebra/Defs.lean`](../QNFMathlib/Algebra/QuadraticAlgebra/Defs.lean),
preserving the declaration name and its use through `Qsqrtd`. The project's
matrix, trace, discriminant, and quadratic-field results remain in active source.

## Integral ideals as free integer modules

**Project implementation:** Frankie F.-C. Wang, included in the Cox equivalence
implementation on 2026-06-18 in
[commit `ef9b3d6`](https://github.com/WangFrankie/QuadraticNumberFields/commit/ef9b3d65aad4e29e6ffd32da6c9f93b69cffe7b7)
([project PR #54](https://github.com/WangFrankie/QuadraticNumberFields/pull/54)).

The project supplied the following instance in the imaginary quadratic-field
context, where `𝓞K` denotes its ring of integers. It specializes mathlib's PID
freeness theorem to an integral ideal. The
[original implementation](https://github.com/WangFrankie/QuadraticNumberFields/blob/ef9b3d65aad4e29e6ffd32da6c9f93b69cffe7b7/QuadraticNumberFields/Forms/Cox/Inverse.lean#L85-L89)
is preserved verbatim:

```lean
/-- Nonzero ideals of `𝓞K` are free `ℤ`-modules of rank 2, so they have bases. -/
noncomputable instance (I : Ideal 𝓞K) (_hI : I ≠ 0) : Module.Free ℤ I := by
  have hfin : Module.Finite ℤ I := inferInstance
  have htors : IsTorsionFree ℤ I := inferInstance
  exact Module.free_of_finite_type_torsion_free' (R := ℤ) (M := I)
```

The instance itself establishes freeness. The rank-two basis is constructed
separately by `idealFin2Basis'`, which remains in
[`FormClassGroup/Cox/Inverse.lean`](../FormClassGroup/Cox/Inverse.lean), together
with the oriented-basis and norm-form constructions.

**Current provider:** the general ideal instance and
`Module.free_of_finite_type_torsion_free'` in
[`Mathlib.LinearAlgebra.FreeModule.PID`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/FreeModule/PID.lean#L380-L395).
The project specialization is retained here as implementation history; the
active Cox construction now obtains freeness from those upstream instances.

## Quadratic-model suborder inclusion and conductor

**Project implementation:** Frankie Wang, originally proved for the imaginary
quadratic realizations in
[`BakerHeegnerStark/ComplexMultiplication/Orders/HalfIntegral.lean`](https://github.com/WangFrankie/BakerHeegnerStark/blob/42c273b84c375c93258ca00774d7d3efe314d7ef/BakerHeegnerStark/ComplexMultiplication/Orders/HalfIntegral.lean)
at immutable BHS commit `42c273b84c375c93258ca00774d7d3efe314d7ef`.

**Current implementation:** the general algebraic API is in
[`ZOnePlusSqrtdOverTwo/Inclusion.lean`](../QuadraticNumberFields/ZOnePlusSqrtdOverTwo/Inclusion.lean)
and
[`ZOnePlusSqrtdOverTwo/Conductor.lean`](../QuadraticNumberFields/ZOnePlusSqrtdOverTwo/Conductor.lean).
For every `d = 1 + 4*k`, the inclusion has coordinate formula
`(a,b) ↦ (a-b,2b)`, even-second-coordinate image, and additive index two.
The conductor is `Ideal.span {2}`, stated using mathlib's existing conductor.

The injectivity and index arguments are now purely algebraic, removing the
original dependence on a faithful complex realization. No imaginary-quadratic,
domain, or squarefreeness hypothesis is needed for these model statements.
The generalized API and its proofs retain the original Apache 2.0 attribution.
BHS's complex-realization and class-number-one applications remain downstream;
they are not imported into the QNF core.

## Submissions to mathlib

The following submissions by Frankie Wang (`FrankieeW`) are linked from this
project. Status was checked on 2026-10-16; neither is recorded here as an already
merged contribution.

| Submission | Project work | Status at verification |
| --- | --- | --- |
| [mathlib #36347](https://github.com/leanprover-community/mathlib4/pull/36347) | Quadratic number fields as `QuadraticAlgebra ℚ d 0`, trace, norm, and field/extension instances | Open |
| [mathlib #36387](https://github.com/leanprover-community/mathlib4/pull/36387) | Normalization and uniqueness of squarefree integer parameters | Open draft |

The independent implementation history above is retained regardless of whether
these submissions are merged. For future replacements, follow the
[preservation rules](mathlib-patch-rules.md#preserving-implementation-history).
