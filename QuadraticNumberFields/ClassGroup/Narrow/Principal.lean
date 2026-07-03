/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Positive Principal Ideals

This file packages the positive-principal exact-sequence surface

`1 → O_Kˣ⁺ → K₊ˣ → P_K⁺ → 1`.
-/

open scoped nonZeroDivisors

namespace NarrowClassGroup

section PositivePrincipal

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]

/-- The map from ring units to fraction-field units. -/
noncomputable abbrev ringUnitToFractionRing :
    Rˣ →* Kˣ :=
  Units.map (algebraMap R K).toMonoidHom

/-- The subgroup `O_Kˣ⁺` of ring units whose image in the fraction field is
totally positive. -/
def totallyPositiveRingUnits : Subgroup Rˣ where
  carrier := {u | IsTotallyPositive ((ringUnitToFractionRing R K u : Kˣ) : K)}
  one_mem' := by
    intro σ
    simp [ringUnitToFractionRing]
  mul_mem' := by
    intro u v hu hv σ
    simpa [ringUnitToFractionRing] using mul_pos (hu σ) (hv σ)
  inv_mem' := by
    intro u hu σ
    simpa [ringUnitToFractionRing] using inv_pos.mpr (hu σ)

/-- Membership in `O_Kˣ⁺`. -/
theorem mem_totallyPositiveRingUnits_iff (u : Rˣ) :
    u ∈ totallyPositiveRingUnits R K ↔
      IsTotallyPositive ((ringUnitToFractionRing R K u : Kˣ) : K) :=
  Iff.rfl

/-- The inclusion `O_Kˣ⁺ → K₊ˣ`. -/
noncomputable def totallyPositiveRingUnitsToField :
    totallyPositiveRingUnits R K →* totallyPositiveUnits K :=
  ((ringUnitToFractionRing R K).comp (totallyPositiveRingUnits R K).subtype).codRestrict
    (totallyPositiveUnits K) (by
      intro u
      exact u.2)

variable [IsFractionRing R K]

/-- The quotient map `K₊ˣ → P_K⁺`, with codomain restricted to its image. -/
noncomputable def toPositivePrincipalIdeals :
    totallyPositiveUnits K →* narrowPrincipalIdeals R K :=
  (toNarrowPrincipalIdeal R K).rangeRestrict

/-- The map `K₊ˣ → P_K⁺` is surjective by definition of `P_K⁺`. -/
theorem toPositivePrincipalIdeals_surjective :
    Function.Surjective (toPositivePrincipalIdeals R K) := by
  intro I
  rcases I.2 with ⟨x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

/-- Exactness at `K₊ˣ` in `1 → O_Kˣ⁺ → K₊ˣ → P_K⁺ → 1`. -/
theorem totallyPositiveRingUnitsToField_mulExact_toPositivePrincipalIdeals
    [IsDomain R] [IsDedekindDomain R] :
    Function.MulExact (totallyPositiveRingUnitsToField R K) (toPositivePrincipalIdeals R K) := by
  rw [MonoidHom.mulExact_iff]
  ext q
  rw [MonoidHom.mem_ker]
  constructor<;> intro hq
  · sorry
  · rcases hq with ⟨u, rfl⟩
    apply Subtype.ext
    sorry







end PositivePrincipal

end NarrowClassGroup
