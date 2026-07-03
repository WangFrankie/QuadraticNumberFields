/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Qsqrtd.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Abstract Quadratic Fields

This file defines an abstraction for quadratic number fields.

The concrete model `Qsqrtd d` remains the standard coordinate model for
calculation, while `QuadraticField K` is the abstract hypothesis used by
statements that should apply to any quadratic field over `ℚ`.

## Main definitions

* `QuadraticField K`: a field `K` with a `ℚ`-algebra structure whose
  dimension over `ℚ` is two.
-/

-- Use the canonical `QuadraticAlgebra` algebra structure on `Qsqrtd` in this file.
-- Otherwise `DivisionRing.toRatAlgebra` competes with it once `Qsqrtd d` is a field.
attribute [-instance] DivisionRing.toRatAlgebra

/-- A quadratic field over `ℚ`.

This wraps `Algebra.IsQuadraticExtension ℚ K` as a class so that theorems can
state their abstract-field input directly as `[QuadraticField K]`, while the
instance below exposes the underlying mathlib predicate whenever existing APIs
need it.
-/
class QuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop where
  /-- The underlying degree-two extension predicate. -/
  isQuadratic : Algebra.IsQuadraticExtension ℚ K

instance (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℚ K :=
  QuadraticField.isQuadratic

namespace QuadraticField

/-- A quadratic field has degree two over `ℚ`. -/
theorem finrank_eq_two (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Module.finrank ℚ K = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

end QuadraticField

/-- A quadratic field is a number field: it has characteristic zero
and is finite-dimensional over `ℚ`. -/
instance QuadraticField.instNumberField (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] : NumberField K where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  to_finiteDimensional := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    -- A quadratic field has `ℚ`-dimension exactly `2`, hence positive finite dimension.
    convert FiniteDimensional.of_finrank_pos (K := ℚ) (V := K) (by
      rw [QuadraticField.finrank_eq_two K]; omega) using 1
    congr 1
    exact Subsingleton.elim _ _

namespace Qsqrtd

/-- The standard model `ℚ(√d)` is an abstract quadratic field when `d` is not a square. -/
instance instQuadraticField (d : ℚ) [Fact (¬ IsSquare d)] :
    QuadraticField (Qsqrtd d) where
  isQuadratic := inferInstance

section RatAlgebra

attribute [local instance] DivisionRing.toRatAlgebra

/-- `Qsqrtd d` is a `QuadraticField` for the `DivisionRing.toRatAlgebra` structure. -/
instance instRatAlgebraQuadraticField (d : ℚ) [Fact (¬ IsSquare d)] :
    QuadraticField (Qsqrtd d) where
  isQuadratic := @Qsqrtd.instRatAlgebraIsQuadraticExtension d _

end RatAlgebra

end Qsqrtd
