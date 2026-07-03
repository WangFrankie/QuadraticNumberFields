/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.QuadraticField.Galois

/-!
# The Galois Group of the Standard Model `Q(√d)`

This file records the standard-model specializations of the abstract quadratic
field Galois-group statements from `QuadraticNumberFields.QuadraticField.Galois`.

For a squarefree integer parameter `d ≠ 1`, the `ℚ`-automorphism group of
`Qsqrtd (d : ℚ)` has order two and is isomorphic to `Multiplicative (ZMod 2)`.

## Main definitions

* `Qsqrtd.card_aut_eq_two`: the standard-model automorphism group has order two.
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
