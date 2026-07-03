/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.QuadraticField.Conj

/-!
# Principal Narrow Class Group Results for Quadratic Fields

This file specializes the positive-principal exact sequence to `𝓞(ℚ(√d))`.
-/

open scoped NumberField nonZeroDivisors

-- Use the canonical `QuadraticAlgebra` algebra structure on standard `Qsqrtd`
-- models in the real-positive Hilbert 90 wrapper.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields

namespace Qsqrtd

open _root_.Qsqrtd

open scoped QuadraticNumberFields.ClassGroup

section PositivePrincipal

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞 (Qsqrtd (d : ℚ))

/-- The totally positive unit subgroup `𝓞(ℚ(√d))ˣ⁺`. -/
noncomputable abbrev positiveUnits : Subgroup OKˣ :=
  NarrowClassGroup.totallyPositiveRingUnits OK (FractionRing OK)

/-- The inclusion `𝓞(ℚ(√d))ˣ⁺ → (Frac 𝓞(ℚ(√d)))ˣ⁺`. -/
noncomputable abbrev positiveUnitsToFractionRing :
    positiveUnits d →* NarrowClassGroup.totallyPositiveUnits (FractionRing OK) :=
  NarrowClassGroup.totallyPositiveRingUnitsToField OK (FractionRing OK)

/-- The positive principal fractional ideals `P_K⁺` for `K = ℚ(√d)`. -/
noncomputable abbrev positivePrincipalIdeals :
    Subgroup ((FractionalIdeal OK⁰ (FractionRing OK))ˣ) :=
  NarrowClassGroup.narrowPrincipalIdeals OK (FractionRing OK)

/-- The map `(Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺`. -/
noncomputable abbrev toPositivePrincipalIdeals :
    NarrowClassGroup.totallyPositiveUnits (FractionRing OK) →* positivePrincipalIdeals d :=
  NarrowClassGroup.toPositivePrincipalIdeals OK (FractionRing OK)

/-- The map `(Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺` is surjective. -/
theorem toPositivePrincipalIdeals_surjective :
    Function.Surjective (toPositivePrincipalIdeals d) :=
  NarrowClassGroup.toPositivePrincipalIdeals_surjective OK (FractionRing OK)

/-- Exactness at `(Frac 𝓞(ℚ(√d)))ˣ⁺` in
`1 → 𝓞(ℚ(√d))ˣ⁺ → (Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺ → 1`. -/
theorem positiveUnitsToFractionRing_mulExact_toPositivePrincipalIdeals :
    Function.MulExact (positiveUnitsToFractionRing d) (toPositivePrincipalIdeals d) :=
  NarrowClassGroup.totallyPositiveRingUnitsToField_mulExact_toPositivePrincipalIdeals
    OK (FractionRing OK)

end PositivePrincipal

namespace Real

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- Concrete positive Hilbert 90 for the real quadratic standard model.

This is the `H¹(G, (Lˣ)⁺) = 1` part of Emerton's item 10, written without a
group-cohomology wrapper: if `a` is totally positive and satisfies
`a * conjugate a = 1`, then `a = b / conjugate b` for a totally positive unit
`b`. The proof is the explicit choice `b = 1 + a`. -/
theorem exists_positive_coboundary_of_mul_star_eq_one
    (hd : 0 < d)
    {a : (Qsqrtd (d : ℚ))ˣ}
    (ha_pos : NarrowClassGroup.IsTotallyPositive (a : Qsqrtd (d : ℚ)))
    (ha_norm : (a : Qsqrtd (d : ℚ)) * star (a : Qsqrtd (d : ℚ)) = 1) :
    ∃ b : (Qsqrtd (d : ℚ))ˣ,
      NarrowClassGroup.IsTotallyPositive (b : Qsqrtd (d : ℚ)) ∧
        (a : Qsqrtd (d : ℚ)) = (b : Qsqrtd (d : ℚ)) / star (b : Qsqrtd (d : ℚ)) := by
  have hdR : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  letI : Nonempty (Qsqrtd (d : ℚ) →+* ℝ) :=
    ⟨(realEmbeddingPos d hdR).toRingHom⟩
  simpa [Qsqrtd.starAlgEquiv_apply] using
    (NarrowClassGroup.exists_positive_coboundary_of_mul_apply_eq_one
      (τ := (starAlgEquiv (d : ℚ)).toRingEquiv)
      (a := a) ha_pos (by simpa [Qsqrtd.starAlgEquiv_apply] using ha_norm))

end Real

end Qsqrtd

end QuadraticNumberFields
