/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Instances

/-!
# Abstract Quadratic Fields

This file defines the project-level abstraction for quadratic number fields.

The concrete model `Qsqrtd d` remains the standard coordinate model for
calculation, while `QuadraticField K` is the abstract hypothesis used by
statements that should apply to any quadratic field over `ℚ`.

## Main definitions

* `QuadraticField K`: a field `K` with a `ℚ`-algebra structure whose
  dimension over `ℚ` is two.
-/

/-- A quadratic field over `ℚ`.

This is the project-level wrapper around mathlib's
`Algebra.IsQuadraticExtension ℚ K`. Keeping it as a class lets application
theorems state their abstract-field input directly as `[QuadraticField K]`,
while the instance below exposes the underlying mathlib predicate whenever
existing APIs need it.
-/
class QuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop where
  /-- The underlying degree-two extension predicate. -/
  isQuadratic : Algebra.IsQuadraticExtension ℚ K

instance (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℚ K :=
  QuadraticField.isQuadratic

namespace Qsqrtd

/-- The standard model `ℚ(√d)` is an abstract quadratic field for squarefree
integer parameters `d ≠ 1`. -/
instance instQuadraticField (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    QuadraticField (Qsqrtd (d : ℚ)) where
  isQuadratic := inferInstance

end Qsqrtd
