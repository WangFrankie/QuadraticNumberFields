# Forms Subsystem

This directory owns the binary-quadratic-form route to imaginary quadratic
class groups.

## Architecture

- `Basic.lean` defines the project-owned computable `(a, b, c)` model of
  integral binary quadratic forms.
- `Action.lean`, `UpperHalfPlane.lean`, `Reduction.lean`, and
  `ReducedUniqueness.lean` provide the `SL₂(ℤ)` action and Gauss reduction
  facts.
- `Bridge.lean`, `InverseCox.lean`, `CoxLeftInverse.lean`,
  `CoxRightInverse.lean`, and `CoxEquivalence.lean` assemble the Cox 7.7
  equivalence between primitive positive definite form classes and ideal class
  groups.
- `Structure.lean` and `ClassGroupLaw.lean` transport the group structure to
  reduced-form representatives.
- `Computable*` and `GaussComposition*` files are the explicit computation and
  regression surface; keep examples there or under `QuadraticNumberFields/Examples`
  rather than in core bridge files.

## Local Rules

- Keep `FormClass` restricted to primitive positive definite forms for the
  imaginary Cox 7.7 correspondence.
- Preserve the distinction between the stable transported class-group law and
  the explicit Gauss-composition computation layer.
- The custom `BinaryQuadraticForm` coordinate model is intentional for
  computable reduced-form enumeration and `native_decide`; add explicit bridge
  lemmas to mathlib `QuadraticForm` when structural APIs are needed.
- `ClassGroupStructure.lean` depends on the sibling `../FiniteAbelianSmith`
  project for certified finite-abelian standard targets. Keep that dependency
  isolated to the standard-output layer and its examples.
- Prefer moving concrete discriminant computations to
  `QuadraticNumberFields/Examples/` once they are no longer part of a proof's
  local explanation.

## Verification

- For documentation-only edits, run `lake env lean` on the touched Lean files.
- For API or import edits, run the touched module builds and then
  `lake build QuadraticNumberFields.Forms.<Module>` or `lake build` when the
  public surface changes.
