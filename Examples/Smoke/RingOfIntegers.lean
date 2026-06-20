/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.RingOfIntegers.Classification

/-!
# Ring-of-integers Smoke Examples

Concrete examples for the ring-of-integers classification.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers
namespace SquarefreeIntegerParameter

/-! ## Boxer Example 2.8: Gaussian and Eisenstein integers -/

/-- **Gaussian integers**: `𝓞(ℚ(√(-1))) ≃+* ℤ[i]`.

Since `-1 ≡ 3 (mod 4)`, the ring of integers is `ℤ[√(-1)] = ℤ[i]`. -/
noncomputable example : 𝓞 (Qsqrtd ((-1 : ℤ) : ℚ)) ≃+* Zsqrtd (-1) :=
  ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (-1) (by decide)

/-- **Eisenstein integers**: `𝓞(ℚ(√(-3))) ≃+* ℤ[(1+√(-3))/2]`.

Since `-3 ≡ 1 (mod 4)`, the ring of integers is `ℤ[ω]` where `ω = (1+√(-3))/2`
is a primitive cube root of unity. Here `-3 = 1 + 4 * (-1)`, so `k = -1`. -/
noncomputable example : 𝓞 (Qsqrtd ((-3 : ℤ) : ℚ)) ≃+* ZOnePlusSqrtdOverTwo (-1) :=
  ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq (-3) (-1) (by decide)

end SquarefreeIntegerParameter
end RingOfIntegers
end QuadraticNumberFields
