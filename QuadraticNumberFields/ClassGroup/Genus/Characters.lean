/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.Genus.PrimeDiscriminant
import QuadraticNumberFields.ClassGroup.Narrow
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QNFMathlib.RingTheory.ClassGroup
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

/-- The submonoid of ideals whose absolute norm is coprime to every signed
prime-discriminant factor. -/
def signedFactorsCoprimeIdealSubmonoid :
      Submonoid (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :=
    { carrier := {I | ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
        I ∈ signedFactorCoprimeIdealSubmonoid d q}
      one_mem' := by
        intro q
        exact one_mem (signedFactorCoprimeIdealSubmonoid d q)
      mul_mem' := by
        intro I J hI hJ q
        exact mul_mem (hI q) (hJ q)
    }

/-- Membership in the all-signed-factors coprime submonoid is membership in each
single signed-factor coprime submonoid. -/
theorem mem_signedFactorsCoprimeIdealSubmonoid_iff
      {I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
      I ∈ signedFactorsCoprimeIdealSubmonoid d ↔
        ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
          I ∈ signedFactorCoprimeIdealSubmonoid d q :=
  Iff.rfl

/-- Forget from ideals coprime to all signed factors to ideals coprime to one
chosen signed factor. -/
def signedFactorsCoprimeIdealToSignedFactor
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      signedFactorsCoprimeIdealSubmonoid d →*
        signedFactorCoprimeIdealSubmonoid d q where
  toFun I := ⟨I, I.property q⟩
  map_one' := rfl
  map_mul' _ _ := rfl

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

/-- If an ideal is coprime to each principal ideal generated by the absolute value
of a signed prime-discriminant factor, then it lies in the all-signed-factors
coprime ideal submonoid. -/
theorem mem_signedFactorsCoprimeIdealSubmonoid_of_forall_sup_span_natAbs_eq_top
      {I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
      (hI_ne : I ≠ ⊥)
      (hcop : ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
        I ⊔ Ideal.span
          ({(q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = ⊤) :
      I ∈ signedFactorsCoprimeIdealSubmonoid d := by
  intro q
  exact mem_signedFactorCoprimeIdealSubmonoid_of_sup_span_natAbs_eq_top d q hI_ne (hcop q)

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

/-- The raw signed-factor character has underlying integer value
`kroneckerSymNat q.1 (Ideal.absNorm I)`. -/
@[simp]
theorem genusCharacterOfSignedFactorRaw_val
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I : signedFactorCoprimeIdealSubmonoid d q) :
      (genusCharacterOfSignedFactorRaw d q I : ℤ) =
        kroneckerSymNat q.1
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
  rfl

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

/-- The raw character cancels equal multipliers with equal raw value. This is the
formal part of reducing descent to principal-multiplier invariance. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_mul_eq_of_raw_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J K L : signedFactorCoprimeIdealSubmonoid d q)
      (hprod : I * K = J * L)
      (hKL : genusCharacterOfSignedFactorRaw d q K =
        genusCharacterOfSignedFactorRaw d q L) :
      genusCharacterOfSignedFactorRaw d q I =
        genusCharacterOfSignedFactorRaw d q J := by
  have hmap := congrArg (genusCharacterOfSignedFactorRawOnCoprimeIdeals d q) hprod
  have hmul :
      genusCharacterOfSignedFactorRaw d q I * genusCharacterOfSignedFactorRaw d q K =
        genusCharacterOfSignedFactorRaw d q J * genusCharacterOfSignedFactorRaw d q L := by
    simpa using hmap
  rw [hKL] at hmul
  exact mul_right_cancel hmul

/-- The raw signed-factor character is unchanged by multiplication by a square in
the signed-factor-coprime ideal monoid. -/
theorem genusCharacterOfSignedFactorRaw_mul_sq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I K : signedFactorCoprimeIdealSubmonoid d q) :
      genusCharacterOfSignedFactorRaw d q (I * K ^ 2) =
        genusCharacterOfSignedFactorRaw d q I := by
  change (genusCharacterOfSignedFactorRawOnCoprimeIdeals d q) (I * K ^ 2) =
    (genusCharacterOfSignedFactorRawOnCoprimeIdeals d q) I
  rw [map_mul, map_pow]
  ext
  simp [pow_two]

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

/-- To prove surjectivity of the restricted narrow class-group map, it suffices to
choose representatives coprime to the principal ideal generated by the absolute
value of the signed discriminant factor. -/
theorem narrowMk0OnSignedFactorCoprimeIdeals_surjective_of_exists_ideal_coprime_representative
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (hrep : ∀ C : Cl⁺(d),
        ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
          NarrowClassGroup.mk0 I = C ∧
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ⊔ Ideal.span
              ({(q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
                Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = ⊤) :
      Function.Surjective (narrowMk0OnSignedFactorCoprimeIdeals d q) := by
  refine narrowMk0OnSignedFactorCoprimeIdeals_surjective_of_exists_absNorm_coprime_representative
    d q ?_
  intro C
  rcases hrep C with ⟨I, hC, hIcop⟩
  refine ⟨I, hC, ?_⟩
  have hI_ne : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≠ ⊥ := by
    have hI_nonzero := I.2
    rw [mem_nonZeroDivisors_iff_ne_zero] at hI_nonzero
    rwa [Ideal.zero_eq_bot] at hI_nonzero
  exact mem_signedFactorCoprimeIdealSubmonoid_of_sup_span_natAbs_eq_top d q hI_ne hIcop

/-- If the natural map from the narrow class group to the ordinary class group is
injective, the ordinary coprime-representative theorem gives narrow
representatives coprime to every signed prime-discriminant factor. -/
theorem exists_forall_ideal_coprime_representative_of_signedFactors_of_narrowToClassGroup_injective
      (hinj : Function.Injective (Qsqrtd.narrowToClassGroup d))
      (C : Cl⁺(d)) :
      ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
        NarrowClassGroup.mk0 I = C ∧
          ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ⊔ Ideal.span
              ({(q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
                Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = ⊤ := by
  let M : ℕ := Finset.univ.prod
    (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => q.1.natAbs)
  have hM_ne : M ≠ 0 := by
    dsimp [M]
    exact Finset.prod_ne_zero_iff.mpr fun q _ =>
      natAbs_ne_zero_of_mem_signedPrimeDiscriminantFactors d q.property
  have hM_cast_ne :
      (M : NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ≠ 0 :=
    Nat.cast_ne_zero.mpr hM_ne
  have hM_span_ne :
      Ideal.span ({(M : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
        Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hM_cast_ne
  obtain ⟨I, hI_wide, hIcop⟩ :=
    _root_.ClassGroup.exists_integralRep_isCoprime (Qsqrtd.narrowToClassGroup d C)
      (Ideal.span ({(M : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
        Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) hM_span_ne
  refine ⟨I, ?_, ?_⟩
  · apply hinj
    simpa [Qsqrtd.narrowToClassGroup] using hI_wide
  · intro q
    have hsup_M :
        (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ⊔
            Ideal.span ({(M : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
              Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = ⊤ :=
      Ideal.isCoprime_iff_sup_eq.mp hIcop
    have hq_dvd_M :
        (q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∣
          (M : NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := by
      have hq_dvd_M_nat : q.1.natAbs ∣ M := by
        dsimp [M]
        exact Finset.dvd_prod_of_mem
          (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => q.1.natAbs)
          (Finset.mem_univ q)
      exact_mod_cast Nat.cast_dvd_cast hq_dvd_M_nat
    have hspan_le :
        Ideal.span ({(M : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≤
          Ideal.span
            ({(q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
              Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :=
      Ideal.span_singleton_le_span_singleton.mpr hq_dvd_M
    have htop_le :=
      sup_le_sup_left hspan_le (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
    rw [hsup_M] at htop_le
    exact top_le_iff.mp htop_le

/-- In the imaginary quadratic case, narrow and ordinary class groups coincide, so
ordinary coprime representatives give signed-factor-coprime narrow
representatives. -/
theorem exists_forall_ideal_coprime_representative_of_signedFactors_of_imaginary
      (hd : d < 0) (C : Cl⁺(d)) :
      ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
        NarrowClassGroup.mk0 I = C ∧
          ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ⊔ Ideal.span
              ({(q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
                Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = ⊤ :=
  exists_forall_ideal_coprime_representative_of_signedFactors_of_narrowToClassGroup_injective
    d (Qsqrtd.Imaginary.narrowToClassGroup_bijective d hd).1 C

/-- Finite ideal-avoidance/approximation input: every narrow class has an integral
ideal representative coprime to every principal ideal generated by the absolute
value of a signed discriminant factor. -/
theorem exists_forall_ideal_coprime_representative_of_signedFactors
      (C : Cl⁺(d)) :
      ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
        NarrowClassGroup.mk0 I = C ∧
          ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ⊔ Ideal.span
              ({(q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
                Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = ⊤ := by
  by_cases hinj : Function.Injective (Qsqrtd.narrowToClassGroup d)
  · exact
      exists_forall_ideal_coprime_representative_of_signedFactors_of_narrowToClassGroup_injective
        d hinj C
  sorry

/-- Ideal-avoidance/approximation input: every narrow class has an integral ideal
representative coprime to the principal ideal generated by the absolute value of
a fixed signed discriminant factor. -/
theorem exists_ideal_coprime_representative_of_signedFactor
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (C : Cl⁺(d)) :
      ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
        NarrowClassGroup.mk0 I = C ∧
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ⊔ Ideal.span
            ({(q.1.natAbs : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
              Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = ⊤ := by
  rcases exists_forall_ideal_coprime_representative_of_signedFactors d C with
    ⟨I, hC, hIcop⟩
  exact ⟨I, hC, hIcop q⟩

/-- Every narrow class has an integral ideal representative whose absolute norm
is coprime to every signed discriminant factor. -/
theorem exists_signedFactorsCoprime_representative
      (C : Cl⁺(d)) :
      ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
        NarrowClassGroup.mk0 I = C ∧
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
            signedFactorsCoprimeIdealSubmonoid d := by
  rcases exists_forall_ideal_coprime_representative_of_signedFactors d C with
    ⟨I, hC, hIcop⟩
  refine ⟨I, hC, ?_⟩
  have hI_ne : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≠ ⊥ := by
    have hI_nonzero := I.2
    rw [mem_nonZeroDivisors_iff_ne_zero] at hI_nonzero
    rwa [Ideal.zero_eq_bot] at hI_nonzero
  exact mem_signedFactorsCoprimeIdealSubmonoid_of_forall_sup_span_natAbs_eq_top d hI_ne hIcop

/-- Every narrow class has an integral ideal representative whose absolute norm
is coprime to a fixed signed discriminant factor. -/
theorem exists_absNorm_coprime_representative_of_signedFactor
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (C : Cl⁺(d)) :
      ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
        NarrowClassGroup.mk0 I = C ∧
          Nat.Coprime
            (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
            q.1.natAbs := by
  rcases exists_ideal_coprime_representative_of_signedFactor d q C with ⟨I, hC, hIcop⟩
  refine ⟨I, hC, ?_⟩
  have hI_ne : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≠ ⊥ := by
    have hI_nonzero := I.2
    rw [mem_nonZeroDivisors_iff_ne_zero] at hI_nonzero
    rwa [Ideal.zero_eq_bot] at hI_nonzero
  exact mem_signedFactorCoprimeIdealSubmonoid_of_sup_span_natAbs_eq_top d q hI_ne hIcop

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

/-- Equality in the restricted narrow class-group map is equality after
multiplication by a totally positive principal fractional ideal. -/
theorem narrowMk0OnSignedFactorCoprimeIdeals_eq_iff_exists_fraction_ring
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q) :
      narrowMk0OnSignedFactorCoprimeIdeals d q I =
          narrowMk0OnSignedFactorCoprimeIdeals d q J ↔
        ∃ x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
          NarrowClassGroup.IsTotallyPositive
              (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
            FractionalIdeal.mk0
                (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
                (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
              toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
                (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
                FractionalIdeal.mk0
                  (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
                  (signedFactorCoprimeIdealNonzeroMonoidHom d q J) := by
  simpa [narrowMk0OnSignedFactorCoprimeIdeals] using
    (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring
      (I := signedFactorCoprimeIdealNonzeroMonoidHom d q I)
      (J := signedFactorCoprimeIdealNonzeroMonoidHom d q J))

/-- Well-definedness input for signed-factor genus characters: the raw Kronecker
value is constant on fibers of the restricted narrow class-group map. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_narrowMk0OnSignedFactorCoprimeIdeals_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      (hIJ : narrowMk0OnSignedFactorCoprimeIdeals d q I =
        narrowMk0OnSignedFactorCoprimeIdeals d q J) :
      genusCharacterOfSignedFactorRaw d q I = genusCharacterOfSignedFactorRaw d q J := by
  rcases (narrowMk0OnSignedFactorCoprimeIdeals_eq_iff_exists_fraction_ring d q I J).mp hIJ with
    ⟨x, hxpos, hxIJ⟩
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

/-- The descended signed-factor character evaluates as the raw Kronecker character
on a narrow class represented by an ideal whose norm is coprime to that factor. -/
theorem genusCharacterOfSignedFactor_apply_narrowMk0OnSignedFactorCoprimeIdeals
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I : signedFactorCoprimeIdealSubmonoid d q) :
      genusCharacterOfSignedFactor d q (narrowMk0OnSignedFactorCoprimeIdeals d q I) =
        genusCharacterOfSignedFactorRaw d q I := by
  simpa [genusCharacterOfSignedFactor] using
    genusCharacterOfSignedFactorDescent_apply_narrowMk0OnSignedFactorCoprimeIdeals
      d q (narrowMk0OnSignedFactorCoprimeIdeals_surjective d q)
      (genusCharacterOfSignedFactorRaw_eq_of_narrowMk0OnSignedFactorCoprimeIdeals_eq d q) I

/-- If a nonzero integral ideal is coprime to every signed factor, then each
descended signed-factor character on its narrow class is computed by the raw
Kronecker character at that ideal. -/
theorem genusCharacterOfSignedFactor_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d) :
      genusCharacterOfSignedFactor d q (NarrowClassGroup.mk0 I) =
        genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩ := by
  let J : signedFactorCoprimeIdealSubmonoid d q := ⟨I, hI q⟩
  have hJ :
      narrowMk0OnSignedFactorCoprimeIdeals d q J = NarrowClassGroup.mk0 I := by
    simp [J, narrowMk0OnSignedFactorCoprimeIdeals, signedFactorCoprimeIdealNonzeroMonoidHom]
  rw [← hJ]
  simpa [J] using genusCharacterOfSignedFactor_apply_narrowMk0OnSignedFactorCoprimeIdeals d q J

/-- If an ideal is coprime to every signed prime-discriminant factor, then its
absolute norm has field-discriminant Kronecker value `1`. -/
theorem kroneckerSymNat_discr_absNorm_eq_one_of_mem_signedFactorsCoprimeIdealSubmonoid
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d) :
      kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ)))
        (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) = 1 := by
  have hI_ne : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≠ ⊥ := by
    have hI_nonzero := I.2
    rw [mem_nonZeroDivisors_iff_ne_zero] at hI_nonzero
    rwa [Ideal.zero_eq_bot] at hI_nonzero
  refine Splitting.kroneckerSymNat_discr_absNorm_eq_one_of_forall_prime_dvd_not_isRamifiedIn
    d hI_ne ?_
  intro p hp_prime hp_dvd hram
  have hp_ram : p ∈ ramifiedPrimes d :=
    (mem_ramifiedPrimes_iff_isRamifiedIn d p).mpr ⟨hp_prime, hram⟩
  let q : {q // q ∈ signedPrimeDiscriminantFactors d} :=
    ⟨primeDiscriminantFactor d p, mem_signedPrimeDiscriminantFactors_of_mem_ramifiedPrimes d hp_ram⟩
  have hcop := hI q
  change Nat.Coprime
    (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
      (primeDiscriminantFactor d p).natAbs at hcop
  have hp_dvd_q : p ∣ (primeDiscriminantFactor d p).natAbs :=
    dvd_natAbs_primeDiscriminantFactor_of_mem_ramifiedPrimes hp_ram
  have hp_dvd_one : p ∣ 1 := by
    have hp_dvd_gcd :
        p ∣ Nat.gcd
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
          (primeDiscriminantFactor d p).natAbs :=
      Nat.dvd_gcd hp_dvd hp_dvd_q
    have hgcd :
        Nat.gcd
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
          (primeDiscriminantFactor d p).natAbs = 1 := hcop
    rwa [hgcd] at hp_dvd_gcd
  have hp_le_one : p ≤ 1 := Nat.le_of_dvd (by norm_num) hp_dvd_one
  have hp_two_le : 2 ≤ p := hp_prime.two_le
  omega

/-- Pure Kronecker product formula on a common representative: if one nonzero
integral ideal is coprime to every signed factor, the product of the
signed-factor Kronecker values is `1`. -/
theorem signedFactorKroneckerProduct_one_of_mem_signedFactorsCoprimeIdealSubmonoid
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        kroneckerSymNat q.1
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) = 1 := by
  let n := Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
  have hn : n ≠ 0 := by
    have hI_nonzero := I.2
    rw [mem_nonZeroDivisors_iff_ne_zero] at hI_nonzero
    dsimp [n]
    intro hzero
    rw [Ideal.absNorm_eq_zero_iff] at hzero
    rw [Ideal.zero_eq_bot] at hI_nonzero
    exact hI_nonzero hzero
  have hdisc :=
    kroneckerSymNat_discr_absNorm_eq_one_of_mem_signedFactorsCoprimeIdealSubmonoid d I hI
  change Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
      kroneckerSymNat q.1 n) = 1
  calc
    Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        kroneckerSymNat q.1 n) =
        (signedPrimeDiscriminantFactors d).attach.prod (fun q => kroneckerSymNat q.1 n) := by
      simp
    _ = kroneckerSymNat ((signedPrimeDiscriminantFactors d).attach.prod fun q => q.1) n := by
      rw [← kroneckerSymNat_prod_left _ _ hn]
    _ = kroneckerSymNat ((signedPrimeDiscriminantFactors d).prod id) n := by
      congr 1
      exact Finset.prod_attach (signedPrimeDiscriminantFactors d) id
    _ = kroneckerSymNat (RingOfIntegers.discrFormula d) n := by
      rw [prod_signedPrimeDiscriminantFactors_eq_discrFormula d]
    _ = kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ))) n := by
      rw [← RingOfIntegers.discr_formula d]
    _ = 1 := by
      simpa [n] using hdisc

/-- The raw unit-valued product formula follows from the corresponding integer
Kronecker product formula. -/
theorem signedFactorRawCharacters_product_one_of_kroneckerProduct
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d)
      (hprod : Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        kroneckerSymNat q.1
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) = 1) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩) = 1 := by
  ext
  simpa using hprod

/-- Raw Kronecker product formula on a common representative: if one nonzero
integral ideal is coprime to every signed factor, the product of the raw
signed-factor values is `1`. -/
theorem signedFactorRawCharacters_product_one_of_mem_signedFactorsCoprimeIdealSubmonoid
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩) = 1 :=
  signedFactorRawCharacters_product_one_of_kroneckerProduct d I hI
    (signedFactorKroneckerProduct_one_of_mem_signedFactorsCoprimeIdealSubmonoid d I hI)

/-- Product formula input for genus characters: the signed-factor characters
attached to a narrow ideal class have product `1`. -/
theorem genusCharacterMap_product_one
      (C : Cl⁺(d)) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactor d q C) = 1 := by
  rcases exists_signedFactorsCoprime_representative d C with ⟨I, hC, hI⟩
  rw [← hC]
  calc
    Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactor d q (NarrowClassGroup.mk0 I)) =
        Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
          genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩) := by
      apply Finset.prod_congr rfl
      intro q hq
      exact genusCharacterOfSignedFactor_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid
        d q I hI
    _ = 1 :=
      signedFactorRawCharacters_product_one_of_mem_signedFactorsCoprimeIdealSubmonoid d I hI

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

/-- Coordinate form of `genusCharacterMap` on a narrow class represented by an
ideal coprime to every signed prime-discriminant factor. -/
theorem genusCharacterMap_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d)
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      (genusCharacterMap d (NarrowClassGroup.mk0 I) : genusCharacterTarget d) q =
        genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩ := by
  rw [genusCharacterMap_apply]
  exact genusCharacterOfSignedFactor_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid d q I hI

end Genus
end ClassGroup
end QuadraticNumberFields
