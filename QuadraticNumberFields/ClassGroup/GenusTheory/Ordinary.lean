/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.MainTheorem
import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Ordinary Square Classes and the Narrow-to-Wide Correction

This file compares the square-class quotients of the narrow and ordinary class
groups of `ℚ(√d)`.  The ordinary genus formula differs from the uniform narrow
formula only by the kernel of the induced map

`Cl⁺(d) / Cl⁺(d)² → Cl(d) / Cl(d)²`.

The finite ramification contribution remains expressed uniformly by
`ramifiedPrimeCount d`; no congruence-class expansion of the radicand is needed.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup
open CommGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" =>
  NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

private theorem comap_square_eq_square_sup_ker_of_surjective
    {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) (hf : Function.Surjective f) :
    (Subgroup.square H).comap f = Subgroup.square G ⊔ f.ker := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_square_iff] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨a, ha⟩ := hf y
    rw [Subgroup.mem_sup]
    refine ⟨a ^ 2, ?_, x * (a ^ 2)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_square_iff]
      exact ⟨a, rfl⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, ha, hy]
      group
    · simp [pow_two, mul_assoc, mul_left_comm]
  · intro x hx
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_sup] at hx
    obtain ⟨y, hy, z, hz, hxy⟩ := hx
    rw [← hxy, map_mul, MonoidHom.mem_ker.mp hz, mul_one]
    obtain ⟨w, hw⟩ := (Subgroup.mem_square_iff y).mp hy
    rw [Subgroup.mem_square_iff]
    exact ⟨f w, by rw [← map_pow, hw]⟩

private theorem squareQuotientMap_ker_eq_map_ker_of_surjective
    {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) (hf : Function.Surjective f)
    (hmap : Subgroup.square G ≤ (Subgroup.square H).comap f) :
    (QuotientGroup.map (Subgroup.square G) (Subgroup.square H) f hmap).ker =
      Subgroup.map (QuotientGroup.mk' (Subgroup.square G)) f.ker := by
  rw [QuotientGroup.ker_map]
  rw [comap_square_eq_square_sup_ker_of_surjective f hf]
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

/-- The map on square quotients induced by the natural map `Cl⁺(d) → Cl(d)`. -/
noncomputable def narrowSquareQuotientToClassGroup :
    squareQuotient (Cl⁺(d)) →* squareQuotient (Cl(d)) :=
  QuotientGroup.map (Subgroup.square (Cl⁺(d))) (Subgroup.square (Cl(d)))
    (Qsqrtd.narrowToClassGroup d) (by
      intro C hC
      rw [Subgroup.mem_comap]
      rw [Subgroup.mem_square_iff] at hC ⊢
      obtain ⟨D, hD⟩ := hC
      refine ⟨Qsqrtd.narrowToClassGroup d D, ?_⟩
      rw [← map_pow, hD])

@[simp]
theorem narrowSquareQuotientToClassGroup_mk' (C : Cl⁺(d)) :
    narrowSquareQuotientToClassGroup d
        (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C) =
      QuotientGroup.mk' (Subgroup.square (Cl(d))) (Qsqrtd.narrowToClassGroup d C) :=
  QuotientGroup.map_mk' (Subgroup.square (Cl⁺(d))) (Subgroup.square (Cl(d)))
    (Qsqrtd.narrowToClassGroup d) _ C

/-- The map on square quotients induced by `Cl⁺(d) → Cl(d)` is surjective. -/
theorem narrowSquareQuotientToClassGroup_surjective :
    Function.Surjective (narrowSquareQuotientToClassGroup d) := by
  apply QuotientGroup.map_surjective_of_surjective
  intro C
  obtain ⟨C₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.square (Cl(d))) C
  obtain ⟨D, hD⟩ := NarrowClassGroup.toClassGroup_surjective OK C₀
  exact ⟨D, by simp [hD]⟩

/-- The correction kernel is the image of `ker(Cl⁺(d) → Cl(d))` in the narrow
square-class quotient. -/
theorem narrowSquareQuotientToClassGroup_ker_eq_map_narrowToClassGroup_ker :
    (narrowSquareQuotientToClassGroup d).ker =
      Subgroup.map (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))))
        (Qsqrtd.narrowToClassGroup d).ker :=
  squareQuotientMap_ker_eq_map_ker_of_surjective
    (Qsqrtd.narrowToClassGroup d) (NarrowClassGroup.toClassGroup_surjective OK) _

/-- Exact correction formula comparing narrow and ordinary square-class
quotients. The correction term is the kernel of
`Cl⁺(d) / Cl⁺(d)² → Cl(d) / Cl(d)²`. -/
theorem card_squareClassGroup_mul_correction_eq_two_pow_sub_one :
    Nat.card (narrowSquareQuotientToClassGroup d).ker *
        Nat.card (squareQuotient (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  have hcard :=
    MonoidHom.nat_card_eq_card_ker_mul_card_of_surjective
      (narrowSquareQuotientToClassGroup d)
      (narrowSquareQuotientToClassGroup_surjective d)
  rw [card_narrowSquareClassGroup_eq_two_pow_sub_one d] at hcard
  exact hcard.symm

end GenusTheory
end ClassGroup
end QuadraticNumberFields
