# Forms Subsystem

This directory owns the binary-quadratic-form route to imaginary quadratic
class groups.

## Architecture

The module graph is layered:

```text
Core -> Cox -> Gauss -> ClassGroup -> Computable
```

- `Core/` defines the project-owned computable `(a, b, c)` model, the
  `SL₂(ℤ)` action, reduction facts, enumeration, and the form-class carrier
  (`PrimitivePositiveDefiniteForm`, `FormClass`, `fieldDiscriminant`) in
  `Core/Class.lean` and `Core/ClassReduced.lean`.
- `Cox/` assembles the Cox 7.7 equivalence between primitive positive definite
  form classes and ideal class groups.
- `Gauss/` contains the explicit representative-level Gauss composition layer.
- `ClassGroup/` transports the ideal class-group structure to form classes and
  reduced-form representatives.
- `Computable/` contains the executable composition/reduction pipeline,
  reduced-form multiplication, and standard finite-abelian output.

## Local Rules

- Keep `FormClass` restricted to primitive positive definite forms for the
  imaginary Cox 7.7 correspondence.
- Do not add top-level re-export shell files such as `Forms/Core.lean` or
  `Forms/Cox.lean`; import concrete submodules directly.
- Keep `Core/` self-contained: it may import other `Core/` modules and external
  mathlib/project-Mathlib modules, but not `Cox/`, `Gauss/`, `ClassGroup/`, or
  `Computable/`.
- Preserve the distinction between the stable transported class-group law and
  the explicit Gauss-composition computation layer.
- The custom `BinaryQuadraticForm` coordinate model is intentional for
  computable reduced-form enumeration and `native_decide`; add explicit bridge
  lemmas to mathlib `QuadraticForm` when structural APIs are needed.
- `Computable/Structure.lean` depends on the sibling `../FiniteAbelianSmith`
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
