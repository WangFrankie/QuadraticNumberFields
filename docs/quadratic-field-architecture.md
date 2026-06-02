# Quadratic Field Architecture

This project should be read as a formalization of quadratic fields in general,
not only as a study of the concrete model `Qsqrtd d`.

The central design is the interaction between three layers:

- `QuadraticField K`: the abstract mathematical property that `K` is a
  quadratic field over `ℚ`.
- `QuadraticFieldCat`: the categorical packaging of all fields satisfying
  `QuadraticField`, with morphisms organizing isomorphisms, functors, transport,
  and classification.
- `Qsqrtd d`: the standard coordinate model `ℚ(√d)`.

The project uses `Qsqrtd d` as a coordinate system for understanding arbitrary
quadratic fields. The core workflow is:

```text
arbitrary QuadraticField K
        ↓ classification / normalization
there exists squarefree d ≠ 1 with K ≃ₐ[ℚ] Qsqrtd d
        ↓ parameter uniqueness
d is unique
        ↓ concrete computation in the standard model
ring of integers, discriminant, real/imaginary behavior,
prime splitting, Dedekind properties
        ↓ transport
results for arbitrary QuadraticField K
```

In this architecture:

- `QuadraticField` is the abstract object of study.
- `Qsqrtd d` is the computational coordinate system.
- `QuadraticFieldCat` is the language for organizing isomorphisms, functors,
  transport, and classification.

This means that concrete results should usually be proved first in the standard
model `Qsqrtd d`, where trace, norm, integrality, discriminants, and splitting
criteria are computable. The classification and uniqueness theory should then
transport those results back to arbitrary quadratic fields.

Avoid treating `Qsqrtd d` as the final scope of the project. It is the standard
model used to calculate; the final mathematical target is the abstract theory of
all quadratic `ℚ`-fields.
