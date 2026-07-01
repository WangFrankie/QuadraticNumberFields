/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import QuadraticNumberFields.QuadraticField.Conj

/-!
# The Galois Group of a Quadratic Field

A quadratic field `K` over `ℚ` is a Galois extension whose Galois group has
order two.  Being a group of prime order, it is cyclic, hence isomorphic to
`ZMod 2` (written multiplicatively as `Multiplicative (ZMod 2)`).

This file proves the statement abstractly for any `QuadraticField K`
(`QuadraticField.galEquivZMod2`) and records the standard-model specialization
(`Qsqrtd.galEquivZMod2`).

## Main definitions

* `QuadraticField.galEquivZMod2`: the multiplicative isomorphism between the
  `ℚ`-automorphism group of a quadratic field and `Multiplicative (ZMod 2)`.
* `Qsqrtd.galEquivZMod2`: the standard-model specialization.

## Implementation notes

The automorphism group is a *multiplicative* group, so the natural target of a
`MulEquiv` is `Multiplicative (ZMod 2)` rather than `ZMod 2` itself (whose
multiplicative monoid is not a group).  The two-element dichotomy of `Task 5`
(`Qsqrtd.algEquiv_self_eq_refl_or_star`) is consistent with this: the standard
model's group is `{refl, starAlgEquiv}` of order two.
-/

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd` models.
attribute [-instance] DivisionRing.toRatAlgebra

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

namespace Qsqrtd

section Galois

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The order of the `ℚ`-automorphism group of the standard model `ℚ(√d)` is
two. -/
theorem card_aut_eq_two :
    Nat.card (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (d : ℚ)) = 2 :=
  QuadraticField.card_aut_eq_two (Qsqrtd (d : ℚ))

/-- The `ℚ`-automorphism group of the standard model `ℚ(√d)` is isomorphic, as
a group, to `Multiplicative (ZMod 2)`. -/
noncomputable def galEquivZMod2 :
    (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (d : ℚ)) ≃* Multiplicative (ZMod 2) :=
  QuadraticField.galEquivZMod2 (Qsqrtd (d : ℚ))

end Galois

end Qsqrtd
