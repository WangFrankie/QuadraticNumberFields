/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.Genus.PrimeDiscriminant
import QuadraticNumberFields.ClassGroup.Narrow
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker
/-!
# Genus Characters

This file states the character target and the genus-character map for the new
narrow-class-group genus-theory layer. The character target is indexed by signed
prime-discriminant factors rather than bare ramified rational primes.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The finite product of sign groups indexed by signed prime-discriminant factors. -/
abbrev genusCharacterTarget :=
  (q : {q // q ∈ signedPrimeDiscriminantFactors d}) → ℤˣ

/-- The product of all signed prime-discriminant signs. -/
noncomputable def genusSignProductHom :
    genusCharacterTarget d →* ℤˣ where
  toFun χ := Finset.univ.prod fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => χ q
  map_one' := by
    simp
  map_mul' χ ψ := by
    simp [genusCharacterTarget, Finset.prod_mul_distrib]

/-- The relation subgroup of sign vectors whose total product is `1`. -/
noncomputable def genusCharacterTargetRelation :
    Subgroup (genusCharacterTarget d) :=
  (genusSignProductHom d).ker

/-- Membership in the relation subgroup is the product-one condition. -/
theorem mem_genusCharacterTargetRelation_iff
    (χ : genusCharacterTarget d) :
    χ ∈ genusCharacterTargetRelation d ↔
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => χ q) = 1 :=
  Iff.rfl

/-- If there is at least one signed prime-discriminant factor, the coordinate-product
map from sign vectors to `ℤˣ` is surjective. -/
theorem genusSignProductHom_surjective_of_nonempty
    (hS : (signedPrimeDiscriminantFactors d).Nonempty) :
    Function.Surjective (genusSignProductHom d) := by
  classical
  obtain ⟨q, hq⟩ := hS
  let Q : {q // q ∈ signedPrimeDiscriminantFactors d} := ⟨q, hq⟩
  intro u
  refine ⟨fun R => if R = Q then u else 1, ?_⟩
  dsimp [genusSignProductHom]
  rw [Finset.prod_ite_eq']
  simp

/-- The full genus-character sign-vector space has cardinality `2 ^ t`, where
`t = ramifiedPrimeCount d`. -/
theorem card_genusCharacterTarget :
    Nat.card (genusCharacterTarget d) = 2 ^ ramifiedPrimeCount d := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  rw [Fintype.card_units_int, Fintype.card_coe,
    card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount]

/-- If the signed prime-discriminant factor set is nonempty, the product-one sign
relation has cardinality `2 ^ (t - 1)`. -/
theorem card_genusCharacterTargetRelation_of_nonempty
    (hS : (signedPrimeDiscriminantFactors d).Nonempty) :
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
    rw [← card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount]
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
theorem card_genusCharacterTargetRelation :
    Nat.card (genusCharacterTargetRelation d) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  by_cases hS : (signedPrimeDiscriminantFactors d).Nonempty
  · exact card_genusCharacterTargetRelation_of_nonempty d hS
  · have hempty : signedPrimeDiscriminantFactors d = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hS
    have hrel_top : genusCharacterTargetRelation d = ⊤ := by
      haveI : IsEmpty {q // q ∈ signedPrimeDiscriminantFactors d} := by
        refine ⟨?_⟩
        intro Q
        have hq_empty : Q.1 ∈ (∅ : Finset ℤ) := by
          simpa [hempty] using Q.property
        simp at hq_empty
      ext χ
      simp [genusCharacterTargetRelation, genusSignProductHom]
    rw [hrel_top, Subgroup.card_top, card_genusCharacterTarget d]
    rw [← card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount d, hempty]
    norm_num

def signedFactorCoprimeIdealSubmonoid
        (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
        Submonoid (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :=
      { carrier := {I | Nat.Coprime (Ideal.absNorm I) q.1.natAbs}
        one_mem' := by
          simp
        mul_mem' := by
          intro I J hI hJ
          simp only [Set.mem_setOf_eq, map_mul]
          exact Nat.Coprime.mul_left hI hJ
      }

noncomputable def genusCharacterOfSignedFactorRaw
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I : signedFactorCoprimeIdealSubmonoid d q) : ℤˣ := by
    let x : ℤ :=
      kroneckerSymNat q.1
        (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    refine
      { val := x
        inv := x
        val_inv := ?_
        inv_val := ?_ }
    · change x * x = 1
      simpa [x, pow_two] using kroneckerSymNat_sq_one_of_coprime q.1 I.property
    · change x * x = 1
      simpa [x, pow_two] using kroneckerSymNat_sq_one_of_coprime q.1 I.property

/-- The genus character attached to one signed prime-discriminant factor.
On a class represented by an ideal `I` whose norm is coprime to `q`, this should
evaluate as `kroneckerSymNat q.1 (Ideal.absNorm I)`. -/
noncomputable def genusCharacterOfSignedFactor
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      Cl⁺(d) →* ℤˣ := by
    refine
      { toFun := fun C => by
          -- choose I with mk0 I = C and norm coprime to q
          -- return genusCharacterOfSignedFactorRaw d q I
          sorry
        map_one' := by
          sorry
        map_mul' := by
          intro C D
          sorry }

/-- The genus-character map from the narrow class group to the product-one sign
relation subgroup. This is the main construction boundary for genus theory. -/
noncomputable def genusCharacterMap :
    Cl⁺(d) →* genusCharacterTargetRelation d := by
  refine
    { toFun := fun C =>
        ⟨fun q => genusCharacterOfSignedFactor d q C, by
          -- product-one relation
          sorry⟩
      map_one' := by
        ext q
        simp
      map_mul' := by
        intro C D
        ext q
        simp }

@[simp]
theorem genusCharacterMap_apply
    (C : Cl⁺(d))
    (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
    (genusCharacterMap d C : genusCharacterTarget d) q =
      genusCharacterOfSignedFactor d q C := by
  rfl

end Genus
end ClassGroup
end QuadraticNumberFields
