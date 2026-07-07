/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Ambiguous Ideals

This file contains the ideal-level fixedness predicate used in the ambiguous
class-group layer. For a ring automorphism `σ`, an ideal is ambiguous when
mapping it along `σ` fixes it.
-/
namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

section FixedIdeals

variable {B : Type*} [CommRing B]

/-- An ideal `I` is ambiguous with respect to a ring automorphism `σ` if `σ`
fixes `I`. -/
def IsAmbiguousIdeal (σ : B ≃+* B) (I : Ideal B) : Prop :=
  Ideal.map (σ : B →+* B) I = I

/-- Ambiguous ideals are exactly fixed points of the induced ideal map. -/
theorem isAmbiguousIdeal_iff_isFixedPt (σ : B ≃+* B) (I : Ideal B) :
    IsAmbiguousIdeal σ I ↔ Function.IsFixedPt (Ideal.map (σ : B →+* B)) I :=
  Iff.rfl

/-- The top ideal is ambiguous. -/
@[simp]
theorem isAmbiguousIdeal_top (σ : B ≃+* B) : IsAmbiguousIdeal σ (⊤ : Ideal B) := by
  rw [IsAmbiguousIdeal, Ideal.map_top]

/-- The product of ambiguous ideals is ambiguous. -/
theorem IsAmbiguousIdeal.mul {σ : B ≃+* B} {I J : Ideal B}
    (hI : IsAmbiguousIdeal σ I) (hJ : IsAmbiguousIdeal σ J) :
    IsAmbiguousIdeal σ (I * J) := by
  unfold IsAmbiguousIdeal at hI hJ ⊢
  rw [Ideal.map_mul, hI, hJ]

end FixedIdeals

end Ambiguous
end ClassGroup
end QuadraticNumberFields
