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

## Baker-Heegner-Stark development

The class-number-one development is preserved on
[`legacy/baker-heegner-stark`](https://github.com/WangFrankie/QuadraticNumberFields/tree/legacy/baker-heegner-stark)
as of 2026-10-28. Completion of the proof is planned in a separate repository.
The source retains its existing Frankie Wang authorship and Apache 2.0 license,
and the branch retains the original commits without rebasing or squashing.

The immutable mathematical snapshot is
[`e74827d`](https://github.com/WangFrankie/QuadraticNumberFields/commit/e74827d99de2db74feba6f66d27336e430ef6ee4).
Its history includes the conductor-two reduced-form count, the correction of
the earlier Weber assumption, the eta-quotient definitions, and the two
symmetric identities for the translates of the modular discriminant. The
subsequent work proves Weber's cubic and the level-two modular equation in
[`5ed698b`](https://github.com/WangFrankie/QuadraticNumberFields/commit/5ed698bb25ae068041c91c058941a78867fba263),
then gives the conditional classification its mathematical names.

The preserved results include:

- the genus-theory and ideal-theoretic reductions, and the nine individual
  class-number-one results;
- the count of three primitive reduced forms of discriminant `-4p` in the
  non-exceptional inert prime case;
- the integral-point classification for `Y² = 2X(X³ + 1)`;
- Weber's transformation and product identities, its cubic factorization,
  the three rational expressions for `j`, the three `γ₂`-identities, and the
  level-two modular equation at `2τ`, `τ/2`, and `(τ+1)/2`.

The full classification still assumes `ConductorTwoWeberHypothesis`.
The relation with actual CM values, their integrality and rationality, the
quadratic-order interpretation of the reduced-form count, and the remaining
Weber identities are unfinished. `IsAssociatedHeegnerGamma` is a finite-table
relation; its identification with the analytic CM values still needs a proof.
The [roadmap](design/class-number-one-roadmap.md) separates the proved results
from these remaining statements.

Validation of the mathematical snapshot passed with Lean/mathlib `v4.35.0`:
the complete `lake build`, lint for all six libraries, and the core axiom audit
for 37 declarations. The audit permits only `propext`, `Classical.choice`, and
`Quot.sound`; it does not turn an explicit mathematical hypothesis into a proof.
The pinned revisions are recorded in `lean-toolchain` and `lake-manifest.json`.

The separate proof repository can refer to this immutable snapshot when
reusing results or documenting their origin.

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
