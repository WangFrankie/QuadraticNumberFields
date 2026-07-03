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

/-- If a domain has a number field as a fraction field, its chosen
`FractionRing` has finitely many real embeddings. -/
theorem finite_fractionRing_realEmbeddings_of_isFractionRing
    (R K : Type*) [CommRing R] [IsDomain R] [Field K] [NumberField K]
    [Algebra R K] [IsFractionRing R K] :
    Finite (FractionRing R →+* ℝ) := by
  let e := IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R) K
  let f : (FractionRing R →+* ℝ) → (K →+* ℝ) := fun σ => σ.comp e.symm.toRingHom
  refine Finite.of_injective f ?_
  intro σ τ hστ
  ext x
  obtain ⟨y, rfl⟩ := e.symm.surjective x
  exact RingHom.congr_fun hστ y

namespace RingOfIntegers

variable (K : Type*) [Field K] [NumberField K]

/-- The fraction field of `𝓞 K` has finitely many real embeddings. -/
instance instFiniteRingOfIntegersFractionRingRealEmbeddings : Finite (FractionRing (𝓞 K) →+* ℝ) :=
  finite_fractionRing_realEmbeddings_of_isFractionRing (𝓞 K) K

/-- The narrow class group of `𝓞 K` is finite. -/
instance instFiniteRingOfIntegersNarrowClassGroup :
    Finite (NarrowClassGroup (𝓞 K)) := by
  infer_instance

end RingOfIntegers

end NarrowClassGroup

namespace NumberField

/-- The narrow class number of a number field. -/
noncomputable def narrowClassNumber (K : Type*) [Field K] [NumberField K] : ℕ :=
  NarrowClassGroup.narrowClassNumber (𝓞 K)

end NumberField
