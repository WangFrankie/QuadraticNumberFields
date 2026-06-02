/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import QuadraticNumberFields.QuadraticField.Conj

/-!
# The Galois Group of the Standard Model `Q(√d)`

For a squarefree integer parameter `d ≠ 1`, the standard model `ℚ(√d)` is a
Galois extension of `ℚ` whose Galois group has order two.  Being a group of
prime order, it is cyclic, hence isomorphic to `ZMod 2` (written
multiplicatively as `Multiplicative (ZMod 2)`).

## Main definitions

* `Qsqrtd.galEquivZMod2`: the multiplicative isomorphism between the
  `ℚ`-automorphism group of `ℚ(√d)` and `Multiplicative (ZMod 2)`.

## Implementation notes

The automorphism group is a *multiplicative* group, so the natural target of a
`MulEquiv` is `Multiplicative (ZMod 2)` rather than `ZMod 2` itself (whose
multiplicative monoid is not a group).  The two-element dichotomy of `Task 5`
(`Qsqrtd.algEquiv_self_eq_refl_or_star`) is consistent with this: the group is
`{refl, starAlgEquiv}` of order two.
-/

namespace Qsqrtd

section Galois

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The order of the `ℚ`-automorphism group of `ℚ(√d)` is two. -/
theorem card_aut_eq_two :
    Nat.card (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (d : ℚ)) = 2 := by
  haveI : Algebra.IsSeparable ℚ (Qsqrtd (d : ℚ)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ (Qsqrtd (d : ℚ)) := Algebra.IsQuadraticExtension.isGalois ℚ _
  rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]

/-- The `ℚ`-automorphism group of the standard model `ℚ(√d)` is isomorphic, as
a group, to `Multiplicative (ZMod 2)`. -/
noncomputable def galEquivZMod2 :
    (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (d : ℚ)) ≃* Multiplicative (ZMod 2) := by
  haveI : IsCyclic (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (d : ℚ)) :=
    isCyclic_of_prime_card (card_aut_eq_two d)
  exact (card_aut_eq_two d) ▸ (zmodCyclicMulEquiv inferInstance).symm

end Galois

end Qsqrtd
