/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Krull-Dimension Transport Across Ring Equivalences

Material destined for mathlib.
-/

namespace RingEquiv

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Transport `Ring.DimensionLEOne` across a ring equivalence.

The proof pulls back prime ideals via `Ideal.comap`, applies `DimensionLEOne` on
the source ring, then pushes forward via `Ideal.map`. -/
theorem dimensionLEOne (e : R ≃+* S) [Ring.DimensionLEOne R] :
    Ring.DimensionLEOne S := by
  refine ⟨?_⟩
  intro p hp0 _
  have hcomapNeBot : Ideal.comap e p ≠ ⊥ := by
    intro hbot
    have hmap := Ideal.map_comap_eq_self_of_equiv e p
    rw [hbot, Ideal.map_bot] at hmap
    exact hp0 hmap.symm
  have hcomapMax : (Ideal.comap e p).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hcomapNeBot (Ideal.comap_isPrime e p)
  have hmapMax : (Ideal.map e (Ideal.comap e p)).IsMaximal :=
    Ideal.map_isMaximal_of_equiv e
  simpa [Ideal.map_comap_eq_self_of_equiv] using hmapMax

end CommRing

end RingEquiv
