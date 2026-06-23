/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.Genus.Index
import QuadraticNumberFields.ClassGroup.Narrow

/-!
# Genus Characters

This file states the character target and the genus-character map for the new
narrow-class-group genus-theory layer.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The finite product of sign groups indexed by the ramified rational primes. -/
abbrev genusCharacterTarget (d : ℤ) :=
  (p : {p // p ∈ ramifiedPrimes d}) → ℤˣ

/-- The product of all ramified-prime signs. -/
noncomputable def genusSignProductHom (d : ℤ) :
    genusCharacterTarget d →* ℤˣ where
  toFun χ := Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} => χ p
  map_one' := by
    simp
  map_mul' χ ψ := by
    simp [genusCharacterTarget, Finset.prod_mul_distrib]

/-- The relation subgroup of sign vectors whose total product is `1`. -/
noncomputable def genusCharacterTargetRelation (d : ℤ) :
    Subgroup (genusCharacterTarget d) :=
  (genusSignProductHom d).ker

/-- Membership in the relation subgroup is the product-one condition. -/
theorem mem_genusCharacterTargetRelation_iff
    (d : ℤ) (χ : genusCharacterTarget d) :
    χ ∈ genusCharacterTargetRelation d ↔
      Finset.univ.prod (fun p : {p // p ∈ ramifiedPrimes d} => χ p) = 1 :=
  Iff.rfl

/-- If there is at least one ramified prime, the coordinate-product map from sign
vectors to `ℤˣ` is surjective. -/
theorem genusSignProductHom_surjective_of_nonempty
    (d : ℤ) (hS : (ramifiedPrimes d).Nonempty) :
    Function.Surjective (genusSignProductHom d) := by
  classical
  obtain ⟨p, hp⟩ := hS
  let P : {p // p ∈ ramifiedPrimes d} := ⟨p, hp⟩
  intro u
  refine ⟨fun Q => if Q = P then u else 1, ?_⟩
  dsimp [genusSignProductHom]
  rw [Finset.prod_ite_eq']
  simp

/-- The full genus-character sign-vector space has cardinality `2 ^ t`, where
`t = ramifiedPrimeCount d`. -/
theorem card_genusCharacterTarget (d : ℤ) :
    Nat.card (genusCharacterTarget d) = 2 ^ ramifiedPrimeCount d := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  rw [Fintype.card_units_int, Fintype.card_coe, ramifiedPrimeCount_eq_card]

/-- If the ramified-prime set is nonempty, the product-one sign relation has
cardinality `2 ^ (t - 1)`. -/
theorem card_genusCharacterTargetRelation_of_nonempty
    (d : ℤ) (hS : (ramifiedPrimes d).Nonempty) :
    Nat.card (genusCharacterTargetRelation d) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  have hsurj := genusSignProductHom_surjective_of_nonempty d hS
  have hindex : (genusCharacterTargetRelation d).index = 2 := by
    calc
      (genusCharacterTargetRelation d).index = Nat.card (genusSignProductHom d).range := by
        rw [genusCharacterTargetRelation, Subgroup.index_ker]
      _ = Nat.card (⊤ : Subgroup ℤˣ) := by
        rw [MonoidHom.range_eq_top.mpr hsurj]
      _ = 2 := by
        rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hmul := (genusCharacterTargetRelation d).card_mul_index
  rw [hindex, card_genusCharacterTarget d] at hmul
  have hcard_pos : 0 < ramifiedPrimeCount d := by
    rw [ramifiedPrimeCount_eq_card]
    exact Finset.card_pos.mpr hS
  have hpow : 2 ^ ramifiedPrimeCount d = 2 ^ (ramifiedPrimeCount d - 1) * 2 := by
    have hsucc : ramifiedPrimeCount d = (ramifiedPrimeCount d - 1) + 1 := by omega
    calc
      2 ^ ramifiedPrimeCount d = 2 ^ ((ramifiedPrimeCount d - 1) + 1) := by
        rw [← hsucc]
      _ = 2 ^ (ramifiedPrimeCount d - 1) * 2 := by rw [pow_succ]
  rw [hpow] at hmul
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) hmul

/-- The product-one genus-character target has cardinality `2 ^ (t - 1)`, where
`t = ramifiedPrimeCount d`. -/
theorem card_genusCharacterTargetRelation (d : ℤ) :
    Nat.card (genusCharacterTargetRelation d) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  by_cases hS : (ramifiedPrimes d).Nonempty
  · exact card_genusCharacterTargetRelation_of_nonempty d hS
  · have hempty : ramifiedPrimes d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hrel_top : genusCharacterTargetRelation d = ⊤ := by
      haveI : IsEmpty {p // p ∈ ramifiedPrimes d} := by
        refine ⟨?_⟩
        intro P
        have hp_empty : P.1 ∈ (∅ : Finset ℕ) := by
          simpa [hempty] using P.property
        simp at hp_empty
      ext χ
      simp [genusCharacterTargetRelation, genusSignProductHom]
    rw [hrel_top, Subgroup.card_top, card_genusCharacterTarget d]
    rw [ramifiedPrimeCount_eq_card, hempty]
    norm_num

/-- The genus-character map from the narrow class group to the product-one sign
relation subgroup. This is the main construction boundary for genus theory. -/
noncomputable def genusCharacterMap
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) →* genusCharacterTargetRelation d := by
  sorry

end Genus
end ClassGroup
end QuadraticNumberFields
