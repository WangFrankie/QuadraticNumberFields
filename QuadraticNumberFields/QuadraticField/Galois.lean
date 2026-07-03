/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import QuadraticNumberFields.QuadraticField.Basic

/-!
# The Galois Group of an Abstract Quadratic Field

A quadratic field `K` over `ℚ` is a Galois extension whose Galois group has
order two.  Being a group of prime order, it is cyclic, hence isomorphic to
`ZMod 2` (written multiplicatively as `Multiplicative (ZMod 2)`).

## Main definitions

* `QuadraticField.card_aut_eq_two`: the `ℚ`-automorphism group has order two.
* `QuadraticField.galEquivZMod2`: the multiplicative isomorphism between the
  `ℚ`-automorphism group and `Multiplicative (ZMod 2)`.

## Implementation notes

The automorphism group is a multiplicative group, so the natural target of a
`MulEquiv` is `Multiplicative (ZMod 2)` rather than `ZMod 2` itself, whose
multiplicative monoid is not a group.
-/

namespace QuadraticField

section Galois

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K]

/-- The order of the `ℚ`-automorphism group of a quadratic field is two. -/
theorem card_aut_eq_two : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
  haveI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]

/-- The `ℚ`-automorphism group of a quadratic field is isomorphic, as a group,
to `Multiplicative (ZMod 2)`. -/
noncomputable def galEquivZMod2 : (K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2) := by
  haveI : IsCyclic (K ≃ₐ[ℚ] K) := isCyclic_of_prime_card (card_aut_eq_two K)
  exact (card_aut_eq_two K) ▸ (zmodCyclicMulEquiv inferInstance).symm

end Galois

end QuadraticField
