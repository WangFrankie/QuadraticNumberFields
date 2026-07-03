/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QNFMathlib.RingTheory.ClassGroup.Narrow

/-!
# Narrow Class Groups of Number Fields

This file connects the generic narrow class group API with rings of integers of
number fields.
-/

open scoped NumberField nonZeroDivisors

namespace NarrowClassGroup

namespace RingOfIntegers

variable (K : Type*) [Field K] [NumberField K]

/-- Real embeddings of the fraction field of `𝓞 K` form a finite type. -/
noncomputable instance instFintypeRingOfIntegersFractionRingRealEmbeddings :
    Fintype (FractionRing (𝓞 K) →+* ℝ) := by
  let e := IsLocalization.algEquiv (nonZeroDivisors (𝓞 K)) (FractionRing (𝓞 K)) K
  exact Fintype.ofInjective
    (fun σ : FractionRing (𝓞 K) →+* ℝ => σ.comp e.symm.toRingHom)
    (by
      intro σ τ hστ
      ext x
      obtain ⟨y, rfl⟩ := e.symm.surjective x
      exact RingHom.congr_fun hστ y)

/-- The narrow class group of `𝓞 K` is a finite type. -/
noncomputable instance instFintypeRingOfIntegersNarrowClassGroup :
    Fintype (NarrowClassGroup (𝓞 K)) :=
  Fintype.ofFinite _

end RingOfIntegers

end NarrowClassGroup

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The narrow class number of a number field. -/
noncomputable def narrowClassNumber : ℕ :=
  NarrowClassGroup.narrowClassNumber (𝓞 K)

/-- The narrow class number of a number field is nonzero. -/
theorem narrowClassNumber_ne_zero : narrowClassNumber K ≠ 0 := Fintype.card_ne_zero

/-- The narrow class number of a number field is positive. -/
theorem narrowClassNumber_pos : 0 < narrowClassNumber K := Fintype.card_pos

end NumberField
