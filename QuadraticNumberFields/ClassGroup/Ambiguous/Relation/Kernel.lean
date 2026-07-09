/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Ambiguous.RamifiedParity
import QuadraticNumberFields.ClassGroup.Ambiguous.Relation.Imaginary
import QuadraticNumberFields.ClassGroup.Ambiguous.Relation.PellUnit
import QuadraticNumberFields.ClassGroup.Narrow.Principal

/-!
# Kernel-Assembly Layer for the Ramified-Parity Relation

This file proves the `fullRamifiedParityNarrowClassHom` kernel-membership criteria
and the nontrivial-kernel input `fullRamifiedParityNarrowClassHom_ker_ne_bot`
used by the strict two-torsion upper bound in `UpperBound.lean`.

It is the single assembly point for the real and imaginary relation inputs:
`PellUnit.lean` supplies the real branch, and `Imaginary.lean` supplies the
imaginary branch.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped NumberField nonZeroDivisors
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra

section Qsqrtd

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
local notation "conjOK" => conjAutRingOfIntegers (Qsqrtd (d : ℚ))

private theorem fullRamifiedParityNarrowClassHom_ker_ne_bot_of_nonzero_mem
    {r : RamifiedParityVector d}
    (hrnonzero : ∃ p, r p ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker) :
    (fullRamifiedParityNarrowClassHom d).ker ≠ ⊥ := by
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  exact ⟨⟨Multiplicative.ofAdd r, hrker⟩,
    fun hrone => Multiplicative.ofAdd_ne_one_of_exists_apply_ne_zero r hrnonzero
      (Subtype.ext_iff.mp hrone)⟩

private theorem fullRamifiedParityNarrowClassHom_ker_ne_bot_of_exists_ambiguous_narrowPrincipal
    (h :
      ∃ J : (Ideal OK)⁰,
        IsAmbiguousIdeal conjOK (J : Ideal OK) ∧
          NarrowClassGroup.mk0 J = (1 : NarrowClassGroup OK) ∧
            ∃ p, fullRamifiedParityVector d J p ≠ 0) :
    (fullRamifiedParityNarrowClassHom d).ker ≠ ⊥ := by
  obtain ⟨J, hJamb, hJnarrow, hJparity⟩ := h
  let r := fullRamifiedParityVector d J
  have hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker := by
    simpa [fullRamifiedParityNarrowClassHom_mem_ker_iff] using
      (ambiguousIdeal_mk0_eq_fullRamifiedParityNarrowClassHom d J hJamb).symm.trans
      hJnarrow
  exact fullRamifiedParityNarrowClassHom_ker_ne_bot_of_nonzero_mem d
    (by simpa [r] using hJparity) hrker

private theorem fullRamifiedParityNarrowClassHom_ker_ne_bot_of_real (hd : 0 < d) :
    (fullRamifiedParityNarrowClassHom d).ker ≠ ⊥ :=
  fullRamifiedParityNarrowClassHom_ker_ne_bot_of_exists_ambiguous_narrowPrincipal d
    (exists_ambiguous_narrowPrincipal_with_nonzero_fullRamifiedParityVector_of_real d hd)


/-- A parity vector lies in the kernel of the full ramified parity hom exactly
when the associated integral ideal product is killed by a totally positive
principal fractional ideal. -/
private theorem fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal
    (r : RamifiedParityVector d) :
    Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker ↔
      ∃ x : (FractionRing OK)ˣ,
        NarrowClassGroup.IsTotallyPositive (x : FractionRing OK) ∧
          FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r) *
            toPrincipalIdeal OK (FractionRing OK) x = 1 := by
  rw [fullRamifiedParityNarrowClassHom_mem_ker_iff]
  rw [← mk0_fullRamifiedParityIdealProduct d r]
  exact NarrowClassGroup.mk0_eq_one_iff_exists_fraction_ring

/-- Generator form of
`fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal`.

The positive principal multiplier in the kernel criterion is inverted to give a
generator for the associated ramified-parity ideal product. -/
private theorem fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_tp_generator
    (r : RamifiedParityVector d) :
    Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker ↔
      ∃ γ : (FractionRing OK)ˣ,
        NarrowClassGroup.IsTotallyPositive (γ : FractionRing OK) ∧
          toPrincipalIdeal OK (FractionRing OK) γ =
            FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r) := by
  constructor
  · intro hr
    obtain ⟨x, hxpos, hx⟩ :=
      (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mp hr
    exact
      ⟨x⁻¹,
        (NarrowClassGroup.totallyPositiveUnits (FractionRing OK)).inv_mem hxpos,
          by simpa [map_inv] using (eq_inv_of_mul_eq_one_left hx).symm⟩
  · rintro ⟨γ, hγpos, hγ⟩
    exact (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mpr
      ⟨γ⁻¹,
        (NarrowClassGroup.totallyPositiveUnits (FractionRing OK)).inv_mem hγpos,
        by
          rw [map_inv, hγ, mul_inv_cancel]⟩

/-- A nonzero positive-principal ramified parity generator gives a nontrivial
kernel for the full ramified-parity homomorphism. -/
private theorem fullRamifiedParityNarrowClassHom_ker_ne_bot_of_exists_tp_generator
    (h :
      ∃ r : RamifiedParityVector d,
        (∃ p, r p ≠ 0) ∧
          ∃ γ : (FractionRing OK)ˣ,
            NarrowClassGroup.IsTotallyPositive (γ : FractionRing OK) ∧
              toPrincipalIdeal OK (FractionRing OK) γ =
                FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r)) :
    (fullRamifiedParityNarrowClassHom d).ker ≠ ⊥ := by
  obtain ⟨r, hrnonzero, γ, hγpos, hγ⟩ := h
  exact fullRamifiedParityNarrowClassHom_ker_ne_bot_of_nonzero_mem d hrnonzero
    ((fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_tp_generator d r).mpr
      ⟨γ, hγpos, hγ⟩)

/-- The full ramified-parity homomorphism has nontrivial kernel.

This is the positive-principal ramified relation used in the weak strict
two-torsion upper bound. The imaginary branch uses vacuous positivity, while
the real branch uses the Pell fundamental-unit construction imported from
`PellUnit`. -/
theorem fullRamifiedParityNarrowClassHom_ker_ne_bot :
    (fullRamifiedParityNarrowClassHom d).ker ≠ ⊥ := by
  classical
  by_cases hdneg : d < 0
  · exact fullRamifiedParityNarrowClassHom_ker_ne_bot_of_exists_tp_generator d
      (exists_nonzero_ramifiedParity_tp_generator_of_imaginary d hdneg)
  · have hdpos : 0 < d :=
      lt_of_le_of_ne (le_of_not_gt hdneg)
        (Ne.symm (Squarefree.ne_zero (Fact.out : Squarefree d)))
    exact fullRamifiedParityNarrowClassHom_ker_ne_bot_of_real d hdpos


end Qsqrtd

end Ambiguous
end ClassGroup
end QuadraticNumberFields
