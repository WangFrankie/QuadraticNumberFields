/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring

/-!
# Conductor action on extended ideals

Material destined for mathlib.

A conductor element carries an extended ideal into the original ideal's image,
without requiring the extension homomorphism to be injective or surjective.

Extracted from
`BakerHeegnerStark/ComplexMultiplication/Orders/ConductorTwoIdeals.lean:25–51`
at BakerHeegnerStark commit `b9abaa376f5da0a80e8321af6aa5db20851aa910`.
-/

namespace Ideal

/-- A conductor element carries an extended ideal into the original ideal's
image, even when the extension homomorphism is not surjective. -/
theorem conductor_mul_mem_map {R S : Type*} [CommRing R] [CommRing S]
    (j : R →+* S) (c : S) (hc : ∀ s : S, c * s ∈ j.range)
    (A : Ideal R) (y : S) (hy : y ∈ Ideal.map j A) :
    ∃ x ∈ A, j x = c * y := by
  have hstrong : ∀ w : S, ∃ x ∈ A, j x = c * w * y := by
    refine Submodule.span_induction (hx := hy) ?_ ?_ ?_ ?_
    · rintro z ⟨a, ha, rfl⟩ w
      obtain ⟨r, hr⟩ := hc w
      refine ⟨r * a, A.mul_mem_left r ha, ?_⟩
      rw [map_mul, hr]
    · intro w
      exact ⟨0, A.zero_mem, by simp⟩
    · intro z t hz ht ihz iht w
      obtain ⟨a, ha, hea⟩ := ihz w
      obtain ⟨b, hb, heb⟩ := iht w
      refine ⟨a + b, A.add_mem ha hb, ?_⟩
      rw [map_add, hea, heb]
      ring
    · intro s z hz ih w
      obtain ⟨a, ha, hea⟩ := ih (w * s)
      refine ⟨a, ha, ?_⟩
      rw [hea]
      simp only [smul_eq_mul]
      ring
  simpa only [mul_one] using hstrong 1

end Ideal
