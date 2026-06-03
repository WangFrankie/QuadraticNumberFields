/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QuadraticNumberFields.Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Class Number Transport

This file gives project-level wrappers for transporting the class-number-one
criterion across ring equivalences. It deliberately focuses on `classNumber = 1`,
where mathlib already identifies the condition with principality of the ring of
integers.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace ClassNumber

variable {K : Type*} [Field K] [NumberField K]

/-- Class number one is equivalent to the ring of integers being a principal
ideal ring. This is the project-level entry point to mathlib's class-number API. -/
theorem eq_one_iff_ringOfIntegers_isPrincipalIdealRing :
    NumberField.classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  NumberField.classNumber_eq_one_iff

/-- Transport the class-number-one criterion from `𝓞 K` to any ring equivalent
to it. -/
theorem eq_one_iff_of_ringOfIntegers_equiv
    {R : Type*} [CommRing R] (e : 𝓞 K ≃+* R) :
    NumberField.classNumber K = 1 ↔ IsPrincipalIdealRing R := by
  rw [eq_one_iff_ringOfIntegers_isPrincipalIdealRing]
  exact RingEquiv.isPrincipalIdealRing_iff e

end ClassNumber
end QuadraticNumberFields
