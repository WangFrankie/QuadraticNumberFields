/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Principal Narrow Class Group Results for Quadratic Fields

This file specializes the positive-principal exact sequence to `𝓞(ℚ(√d))`.
-/

open scoped NumberField nonZeroDivisors

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

end Qsqrtd

end QuadraticNumberFields
