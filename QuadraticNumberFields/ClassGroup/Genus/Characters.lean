/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.Genus.PrimeDiscriminant
import QuadraticNumberFields.ClassGroup.Narrow
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
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

open scoped NumberField nonZeroDivisors QuadraticNumberFields.ClassGroup

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

/-- If an ideal is coprime to the principal ideal generated by the absolute value
of a signed prime-discriminant factor, then it lies in the signed-factor coprime
ideal submonoid. -/
theorem mem_signedFactorCoprimeIdealSubmonoid_of_sup_span_natAbs_eq_top
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      {I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
      (hI_ne : I ≠ ⊥)
      (hcop : I ⊔ Ideal.span
        ({(q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
          Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = ⊤) :
      I ∈ signedFactorCoprimeIdealSubmonoid d q := by
  exact Ideal.absNorm_coprime_of_sup_span_natCast_eq_top I q.1.natAbs hI_ne hcop

/-- Ideals in the signed-factor coprime submonoid have nonzero absolute norm. -/
theorem absNorm_ne_zero_of_mem_signedFactorCoprimeIdealSubmonoid
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I : signedFactorCoprimeIdealSubmonoid d q) :
      Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≠ 0 := by
  intro hzero
  have hcop := I.property
  change Nat.Coprime
      (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
        q.1.natAbs at hcop
  have hq1 : q.1.natAbs = 1 := by
    simpa [Nat.Coprime, hzero] using hcop
  exact (natAbs_ne_one_of_mem_signedPrimeDiscriminantFactors d q.property) hq1

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

/-- The raw genus character at a signed prime-discriminant factor as a monoid
homomorphism on ideals whose absolute norm is coprime to that signed factor. -/
noncomputable def genusCharacterOfSignedFactorRawOnCoprimeIdeals
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      signedFactorCoprimeIdealSubmonoid d q →* ℤˣ where
  toFun I := genusCharacterOfSignedFactorRaw d q I
  map_one' := by
    ext
    simp [genusCharacterOfSignedFactorRaw, Ideal.absNorm_top, kroneckerSymNat]
  map_mul' I J := by
    ext
    dsimp [genusCharacterOfSignedFactorRaw]
    rw [Ideal.absNorm.map_mul]
    rw [kroneckerSymNat_mul]
    · exact absNorm_ne_zero_of_mem_signedFactorCoprimeIdealSubmonoid d q I
    · exact absNorm_ne_zero_of_mem_signedFactorCoprimeIdealSubmonoid d q J

/-- The forgetful monoid hom from ideals with norm coprime to a signed
prime-discriminant factor to nonzero integral ideals. -/
def signedFactorCoprimeIdealNonzeroMonoidHom
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      signedFactorCoprimeIdealSubmonoid d q →*
        (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰ where
  toFun I := ⟨I, by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hbot
    exact absNorm_ne_zero_of_mem_signedFactorCoprimeIdealSubmonoid d q I (by
      simp [hbot, Ideal.absNorm_bot])⟩
  map_one' := by
    ext
    rfl
  map_mul' I J := by
    ext
    rfl

/-- The narrow class-group map restricted to ideals whose absolute norm is coprime
to a signed prime-discriminant factor. -/
noncomputable def narrowMk0OnSignedFactorCoprimeIdeals
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      signedFactorCoprimeIdealSubmonoid d q →* Cl⁺(d) :=
  NarrowClassGroup.mk0.comp (signedFactorCoprimeIdealNonzeroMonoidHom d q)

/-- To prove surjectivity of the restricted narrow class-group map, it suffices to
choose, in every narrow class, a nonzero integral ideal representative whose
absolute norm is coprime to the signed factor. -/
theorem narrowMk0OnSignedFactorCoprimeIdeals_surjective_of_exists_absNorm_coprime_representative
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (hrep : ∀ C : Cl⁺(d),
        ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
          NarrowClassGroup.mk0 I = C ∧
            Nat.Coprime
              (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
              q.1.natAbs) :
      Function.Surjective (narrowMk0OnSignedFactorCoprimeIdeals d q) := by
  intro C
  rcases hrep C with ⟨I, hC, hI⟩
  refine ⟨⟨(I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))), hI⟩, ?_⟩
  simpa [narrowMk0OnSignedFactorCoprimeIdeals,
    signedFactorCoprimeIdealNonzeroMonoidHom] using hC

/-- Ideal-avoidance/approximation input: every narrow class has an integral ideal
representative whose absolute norm is coprime to a fixed signed discriminant
factor. -/
theorem exists_absNorm_coprime_representative_of_signedFactor
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (C : Cl⁺(d)) :
      ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
        NarrowClassGroup.mk0 I = C ∧
          Nat.Coprime
            (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
            q.1.natAbs := by
  sorry

/-- The restricted narrow class-group map from ideals whose norms are coprime to a
signed discriminant factor is surjective. -/
theorem narrowMk0OnSignedFactorCoprimeIdeals_surjective
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      Function.Surjective (narrowMk0OnSignedFactorCoprimeIdeals d q) :=
  narrowMk0OnSignedFactorCoprimeIdeals_surjective_of_exists_absNorm_coprime_representative
    d q (exists_absNorm_coprime_representative_of_signedFactor d q)

/-- If the restricted narrow class-group map is surjective and the raw character is
constant on its fibers, then the raw signed-factor character induces a genuine
narrow class-group character. -/
noncomputable def genusCharacterOfSignedFactorDescent
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (hsurj : Function.Surjective (narrowMk0OnSignedFactorCoprimeIdeals d q))
      (hdesc : ∀ I J : signedFactorCoprimeIdealSubmonoid d q,
        narrowMk0OnSignedFactorCoprimeIdeals d q I =
          narrowMk0OnSignedFactorCoprimeIdeals d q J →
            genusCharacterOfSignedFactorRaw d q I = genusCharacterOfSignedFactorRaw d q J) :
      Cl⁺(d) →* ℤˣ where
  toFun C := genusCharacterOfSignedFactorRaw d q (Classical.choose (hsurj C))
  map_one' := by
    have hmk :
        narrowMk0OnSignedFactorCoprimeIdeals d q (Classical.choose (hsurj 1)) =
          narrowMk0OnSignedFactorCoprimeIdeals d q 1 := by
      rw [Classical.choose_spec (hsurj 1)]
      simp
    calc
      genusCharacterOfSignedFactorRaw d q (Classical.choose (hsurj 1)) =
          genusCharacterOfSignedFactorRaw d q 1 :=
        hdesc (Classical.choose (hsurj 1)) 1 hmk
      _ = 1 := by
        exact map_one (genusCharacterOfSignedFactorRawOnCoprimeIdeals d q)
  map_mul' C D := by
    have hmk :
        narrowMk0OnSignedFactorCoprimeIdeals d q (Classical.choose (hsurj (C * D))) =
          narrowMk0OnSignedFactorCoprimeIdeals d q
            (Classical.choose (hsurj C) * Classical.choose (hsurj D)) := by
      rw [Classical.choose_spec (hsurj (C * D))]
      rw [map_mul]
      rw [Classical.choose_spec (hsurj C), Classical.choose_spec (hsurj D)]
    calc
      genusCharacterOfSignedFactorRaw d q (Classical.choose (hsurj (C * D))) =
          genusCharacterOfSignedFactorRaw d q
            (Classical.choose (hsurj C) * Classical.choose (hsurj D)) :=
        hdesc (Classical.choose (hsurj (C * D)))
          (Classical.choose (hsurj C) * Classical.choose (hsurj D)) hmk
      _ = genusCharacterOfSignedFactorRaw d q (Classical.choose (hsurj C)) *
          genusCharacterOfSignedFactorRaw d q (Classical.choose (hsurj D)) := by
        exact map_mul (genusCharacterOfSignedFactorRawOnCoprimeIdeals d q)
          (Classical.choose (hsurj C)) (Classical.choose (hsurj D))

/-- The descended signed-factor genus character agrees with the raw character on a
class represented by an ideal whose norm is coprime to the signed factor. -/
theorem genusCharacterOfSignedFactorDescent_apply_narrowMk0OnSignedFactorCoprimeIdeals
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (hsurj : Function.Surjective (narrowMk0OnSignedFactorCoprimeIdeals d q))
      (hdesc : ∀ I J : signedFactorCoprimeIdealSubmonoid d q,
        narrowMk0OnSignedFactorCoprimeIdeals d q I =
          narrowMk0OnSignedFactorCoprimeIdeals d q J →
            genusCharacterOfSignedFactorRaw d q I = genusCharacterOfSignedFactorRaw d q J)
      (I : signedFactorCoprimeIdealSubmonoid d q) :
      genusCharacterOfSignedFactorDescent d q hsurj hdesc
          (narrowMk0OnSignedFactorCoprimeIdeals d q I) =
        genusCharacterOfSignedFactorRaw d q I :=
  hdesc (Classical.choose (hsurj (narrowMk0OnSignedFactorCoprimeIdeals d q I))) I
    (Classical.choose_spec (hsurj (narrowMk0OnSignedFactorCoprimeIdeals d q I)))

/-- Well-definedness input for signed-factor genus characters: the raw Kronecker
value is constant on fibers of the restricted narrow class-group map. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_narrowMk0OnSignedFactorCoprimeIdeals_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      (hIJ : narrowMk0OnSignedFactorCoprimeIdeals d q I =
        narrowMk0OnSignedFactorCoprimeIdeals d q J) :
      genusCharacterOfSignedFactorRaw d q I = genusCharacterOfSignedFactorRaw d q J := by
  sorry

/-- The genus character attached to one signed prime-discriminant factor.
On a class represented by an ideal `I` whose norm is coprime to `q`, this should
evaluate as `kroneckerSymNat q.1 (Ideal.absNorm I)`. -/
noncomputable def genusCharacterOfSignedFactor
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      Cl⁺(d) →* ℤˣ :=
  genusCharacterOfSignedFactorDescent d q
    (narrowMk0OnSignedFactorCoprimeIdeals_surjective d q)
    (genusCharacterOfSignedFactorRaw_eq_of_narrowMk0OnSignedFactorCoprimeIdeals_eq d q)

/-- Product formula input for genus characters: the signed-factor characters
attached to a narrow ideal class have product `1`. -/
theorem genusCharacterMap_product_one
      (C : Cl⁺(d)) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactor d q C) = 1 := by
  sorry

/-- The genus-character map from the narrow class group to the product-one sign
relation subgroup. This is the main construction boundary for genus theory. -/
noncomputable def genusCharacterMap :
    Cl⁺(d) →* genusCharacterTargetRelation d := by
  refine
    { toFun := fun C =>
        ⟨fun q => genusCharacterOfSignedFactor d q C, by
          exact genusCharacterMap_product_one d C⟩
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
