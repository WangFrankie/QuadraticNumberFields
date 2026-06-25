/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.Genus.PrimeDiscriminant
import QuadraticNumberFields.ClassGroup.Narrow
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.RingOfIntegers.Norm
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

/-- The raw signed-factor character is trivial on squares in the
signed-factor-coprime ideal monoid. -/
theorem genusCharacterOfSignedFactorRaw_sq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (K : signedFactorCoprimeIdealSubmonoid d q) :
      genusCharacterOfSignedFactorRaw d q (K ^ 2) = 1 := by
  change (genusCharacterOfSignedFactorRawOnCoprimeIdeals d q) (K ^ 2) = 1
  rw [map_pow]
  ext
  simp [pow_two]

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

/-- If two coprime ideal representatives become equal after multiplying by square
coprime ideals, then their raw signed-factor characters agree. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_mul_sq_eq_mul_sq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J K L : signedFactorCoprimeIdealSubmonoid d q)
      (hprod : I * K ^ 2 = J * L ^ 2) :
      genusCharacterOfSignedFactorRaw d q I =
        genusCharacterOfSignedFactorRaw d q J :=
  genusCharacterOfSignedFactorRaw_eq_of_mul_eq_of_raw_eq d q I J (K ^ 2) (L ^ 2)
    hprod (by rw [genusCharacterOfSignedFactorRaw_sq d q K,
      genusCharacterOfSignedFactorRaw_sq d q L])

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

/-- Multiplication by a square principal fractional ideal preserves the restricted
narrow class, when the result is again represented by an ideal whose norm is
coprime to the signed factor. -/
theorem narrowMk0OnSignedFactorCoprimeIdeals_eq_of_mul_toPrincipalIdeal_sq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      {x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} (hx : x ≠ 0)
      (hJ : FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (Units.mk0 (x ^ 2) (pow_ne_zero 2 hx)) =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q J)) :
      narrowMk0OnSignedFactorCoprimeIdeals d q I =
        narrowMk0OnSignedFactorCoprimeIdeals d q J := by
  simpa [narrowMk0OnSignedFactorCoprimeIdeals] using
    (NarrowClassGroup.mk0_eq_mk0_of_mul_toPrincipalIdeal_sq
      (R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
      (I := signedFactorCoprimeIdealNonzeroMonoidHom d q I)
      (J := signedFactorCoprimeIdealNonzeroMonoidHom d q J) hx hJ)

/-- Clear denominators in a principal fractional multiplier relating two
signed-factor-coprime ideal representatives. -/
theorem exists_integral_multipliers_of_mul_toPrincipalIdeal_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
      (hJ : FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q J)) :
      ∃ a b : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)), b ≠ 0 ∧
        Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
          Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  have hfrac : FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
        ((signedFactorCoprimeIdealNonzeroMonoidHom d q I :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      ((signedFactorCoprimeIdealNonzeroMonoidHom d q J :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
    have hJ_val := congrArg
      (fun U : (FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))ˣ =>
          (U : FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) hJ
    simpa [coe_toPrincipalIdeal, mul_comm] using hJ_val
  simpa using
    (FractionalIdeal.exists_span_mul_eq_span_mul_of_spanSingleton_mul_coeIdeal_eq_coeIdeal
      (R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) hfrac)

/-- Clear denominators in a principal fractional multiplier while retaining the
fraction-field element represented by the numerator and denominator. -/
theorem exists_integral_multipliers_with_mk'_of_mul_toPrincipalIdeal_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
      (hJ : FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q J)) :
      ∃ a b : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)), ∃ hb : b ≠ 0,
        IsLocalization.mk'
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) a
            ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
          (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
          Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  have hfrac : FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
        ((signedFactorCoprimeIdealNonzeroMonoidHom d q I :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      ((signedFactorCoprimeIdealNonzeroMonoidHom d q J :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
    have hJ_val := congrArg
      (fun U : (FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))ˣ =>
          (U : FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) hJ
    simpa [coe_toPrincipalIdeal, mul_comm] using hJ_val
  rcases
    FractionalIdeal.exists_mk'_span_mul_eq_span_mul_of_spanSingleton_mul_coeIdeal_eq_coeIdeal
      (R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) hfrac with
    ⟨a, b, hxb, hclear⟩
  refine ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp b.property, ?_, hclear⟩
  simpa using hxb

/-- Clear denominators in a square principal fractional multiplier relating two
signed-factor-coprime ideal representatives. -/
theorem exists_integral_square_multipliers_of_mul_toPrincipalIdeal_sq_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      {x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} (hx : x ≠ 0)
      (hJ : FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (Units.mk0 (x ^ 2) (pow_ne_zero 2 hx)) =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q J)) :
      ∃ a b : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)), a ≠ 0 ∧ b ≠ 0 ∧
        Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
          Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  have hfrac : FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) (x ^ 2) *
        ((signedFactorCoprimeIdealNonzeroMonoidHom d q I :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      ((signedFactorCoprimeIdealNonzeroMonoidHom d q J :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
    have hJ_val := congrArg
      (fun U : (FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))ˣ =>
          (U : FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) hJ
    simpa [coe_toPrincipalIdeal, mul_comm] using hJ_val
  simpa using
    (FractionalIdeal.exists_span_mul_span_mul_eq_of_spanSingleton_sq_mul_coeIdeal_eq_coeIdeal
      (R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) hx hfrac)

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

private theorem int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd
    {m : ℤ} {N : ℕ} (hm : 0 ≤ m) (hcop : Nat.Coprime m.natAbs N)
    (h2N : 2 ∣ N) :
    m % 2 = 1 := by
  have hcop2 : Nat.Coprime m.natAbs 2 :=
    Nat.Coprime.coprime_dvd_right h2N hcop
  have hnot_two : ¬ 2 ∣ m.natAbs :=
    (Nat.prime_two.coprime_iff_not_dvd).mp hcop2.symm
  have hnat : m.natAbs % 2 = 1 := by omega
  have habs : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg hm
  omega

private theorem sq_emod_eight_of_odd (n : ℤ) (hn : ¬ 2 ∣ n) :
    n ^ 2 % 8 = 1 := by
  have hn2 : n % 2 = 1 := by omega
  have hn8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hn8 with h1 | h3 | h5 | h7
  · have hmod : n ≡ 1 [ZMOD 8] := by exact h1
    simpa using (hmod.pow 2).eq
  · have hmod : n ≡ 3 [ZMOD 8] := by exact h3
    simpa using (hmod.pow 2).eq
  · have hmod : n ≡ 5 [ZMOD 8] := by exact h5
    simpa using (hmod.pow 2).eq
  · have hmod : n ≡ 7 [ZMOD 8] := by exact h7
    simpa using (hmod.pow 2).eq

private theorem zsqrtd_norm_emod_four_eq_one_of_param_mod_four_three
    {D : ℤ} (z : Zsqrtd D) (hd4 : D % 4 = 3)
    (hnodd : (Zsqrtd.norm z) % 2 = 1) :
    Zsqrtd.norm z % 4 = 1 := by
  rw [RingOfIntegers.norm_zsqrtd]
  by_cases ha2 : 2 ∣ z.re
  · have ha4 : z.re ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 0 [ZMOD 4] := by
        simpa using ha4.sub ((Int.ModEq.refl D).mul hb4)
      have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
        have h := hnorm4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
        simpa using h.eq
      rw [RingOfIntegers.norm_zsqrtd] at hnodd
      omega
    · have hb4 : z.im ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.im hb2
      have hd4mod : D ≡ 3 [ZMOD 4] := by exact hd4
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 1 [ZMOD 4] := by
        calc
          z.re ^ 2 - D * z.im ^ 2 ≡ 0 - 3 * 1 [ZMOD 4] := ha4.sub (hd4mod.mul hb4)
          _ ≡ 1 [ZMOD 4] := by decide +revert
      exact hnorm4
  · have ha4 : z.re ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 1 [ZMOD 4] := by
        simpa using ha4.sub ((Int.ModEq.refl D).mul hb4)
      exact hnorm4
    · have hb4 : z.im ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.im hb2
      have hd4mod : D ≡ 3 [ZMOD 4] := by exact hd4
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 2 [ZMOD 4] := by
        calc
          z.re ^ 2 - D * z.im ^ 2 ≡ 1 - 3 * 1 [ZMOD 4] := ha4.sub (hd4mod.mul hb4)
          _ ≡ 2 [ZMOD 4] := by decide +revert
      have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
        have h := hnorm4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
        simpa using h.eq
      rw [RingOfIntegers.norm_zsqrtd] at hnodd
      omega

private theorem zsqrtd_norm_emod_eight_eq_one_or_seven_of_param_mod_eight_two
    {D : ℤ} (z : Zsqrtd D) (hd8 : D % 8 = 2)
    (hnodd : (Zsqrtd.norm z) % 2 = 1) :
    Zsqrtd.norm z % 8 = 1 ∨ Zsqrtd.norm z % 8 = 7 := by
  rw [RingOfIntegers.norm_zsqrtd]
  have hd8mod : D ≡ 2 [ZMOD 8] := by exact hd8
  by_cases ha2 : 2 ∣ z.re
  · have ha4 : z.re ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.re ha2
    have hda2 : D ≡ 0 [ZMOD 2] := by
      have hd2 : D % 2 = 0 := by omega
      exact hd2
    have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
      have ha2mod : z.re ^ 2 ≡ 0 [ZMOD 2] :=
        ha4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
      have hprod2 : D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using hda2.mul (Int.ModEq.refl (z.im ^ 2))
      have hmod : z.re ^ 2 - D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using ha2mod.sub hprod2
      exact hmod.eq
    rw [RingOfIntegers.norm_zsqrtd] at hnodd
    omega
  · have ha8 : z.re ^ 2 ≡ 1 [ZMOD 8] := sq_emod_eight_of_odd z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have htwo_mul_b : (2 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
        simpa using hb4.mul_left' (c := (2 : ℤ))
      have hdb : D * z.im ^ 2 ≡ 0 [ZMOD 8] :=
        (hd8mod.mul (Int.ModEq.refl (z.im ^ 2))).trans htwo_mul_b
      have hnorm8 : z.re ^ 2 - D * z.im ^ 2 ≡ 1 [ZMOD 8] := by
        simpa using ha8.sub hdb
      left
      exact hnorm8
    · have hb8 : z.im ^ 2 ≡ 1 [ZMOD 8] := sq_emod_eight_of_odd z.im hb2
      have hdb : D * z.im ^ 2 ≡ 2 [ZMOD 8] := by
        simpa using hd8mod.mul hb8
      have hnorm8 : z.re ^ 2 - D * z.im ^ 2 ≡ 7 [ZMOD 8] := by
        calc
          z.re ^ 2 - D * z.im ^ 2 ≡ 1 - 2 [ZMOD 8] := ha8.sub hdb
          _ ≡ 7 [ZMOD 8] := by decide +revert
      right
      exact hnorm8

private theorem zsqrtd_norm_emod_eight_eq_one_or_three_of_param_mod_eight_six
    {D : ℤ} (z : Zsqrtd D) (hd8 : D % 8 = 6)
    (hnodd : (Zsqrtd.norm z) % 2 = 1) :
    Zsqrtd.norm z % 8 = 1 ∨ Zsqrtd.norm z % 8 = 3 := by
  rw [RingOfIntegers.norm_zsqrtd]
  have hd8mod : D ≡ 6 [ZMOD 8] := by exact hd8
  by_cases ha2 : 2 ∣ z.re
  · have ha4 : z.re ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.re ha2
    have hda2 : D ≡ 0 [ZMOD 2] := by
      have hd2 : D % 2 = 0 := by omega
      exact hd2
    have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
      have ha2mod : z.re ^ 2 ≡ 0 [ZMOD 2] :=
        ha4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
      have hprod2 : D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using hda2.mul (Int.ModEq.refl (z.im ^ 2))
      have hmod : z.re ^ 2 - D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using ha2mod.sub hprod2
      exact hmod.eq
    rw [RingOfIntegers.norm_zsqrtd] at hnodd
    omega
  · have ha8 : z.re ^ 2 ≡ 1 [ZMOD 8] := sq_emod_eight_of_odd z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have hsix_mul_b : (6 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
        have htwo_mul_b : (2 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
          simpa using hb4.mul_left' (c := (2 : ℤ))
        have hfour_mul_b : (4 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
          have h := hb4.mul_left' (c := (4 : ℤ))
          exact h.of_dvd (by norm_num : (8 : ℤ) ∣ 4 * 4)
        calc
          (6 : ℤ) * z.im ^ 2 = (2 : ℤ) * z.im ^ 2 + (4 : ℤ) * z.im ^ 2 := by ring
          _ ≡ 0 + 0 [ZMOD 8] := htwo_mul_b.add hfour_mul_b
          _ ≡ 0 [ZMOD 8] := by decide +revert
      have hdb : D * z.im ^ 2 ≡ 0 [ZMOD 8] :=
        (hd8mod.mul (Int.ModEq.refl (z.im ^ 2))).trans hsix_mul_b
      have hnorm8 : z.re ^ 2 - D * z.im ^ 2 ≡ 1 [ZMOD 8] := by
        simpa using ha8.sub hdb
      left
      exact hnorm8
    · have hb8 : z.im ^ 2 ≡ 1 [ZMOD 8] := sq_emod_eight_of_odd z.im hb2
      have hdb : D * z.im ^ 2 ≡ 6 [ZMOD 8] := by
        simpa using hd8mod.mul hb8
      have hnorm8 : z.re ^ 2 - D * z.im ^ 2 ≡ 3 [ZMOD 8] := by
        calc
          z.re ^ 2 - D * z.im ^ 2 ≡ 1 - 6 [ZMOD 8] := ha8.sub hdb
          _ ≡ 3 [ZMOD 8] := by decide +revert
      right
      exact hnorm8

/-- In the `ℤ[√d]` branch, nonnegative explicit norms prime to the `2`-primary
signed factor have trivial `2`-primary Kronecker value. -/
theorem kroneckerSymNat_twoPrimeDiscriminantFactor_zsqrtd_norm_eq_one
    {D : ℤ} [Fact (Squarefree D)]
    (z : Zsqrtd D) (hd4 : D % 4 ≠ 1) (hN_nonneg : 0 ≤ Zsqrtd.norm z)
    (hcop : Nat.Coprime (Zsqrtd.norm z).natAbs (twoPrimeDiscriminantFactor D).natAbs) :
    kroneckerSymNat (twoPrimeDiscriminantFactor D) (Zsqrtd.norm z).natAbs = 1 := by
  refine kroneckerSymNat_twoPrimeDiscriminantFactor_eq_one_of_mod_conditions ?_ ?_ ?_
  · intro hd2
    have hcop4 : Nat.Coprime (Zsqrtd.norm z).natAbs 4 := by
      simpa [twoPrimeDiscriminantFactor, hd2] using hcop
    have hnodd : (Zsqrtd.norm z) % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN_nonneg hcop4
        (by norm_num : 2 ∣ 4)
    have hd43 : D % 4 = 3 := by omega
    have hmod := zsqrtd_norm_emod_four_eq_one_of_param_mod_four_three z hd43 hnodd
    have hcast : (((Zsqrtd.norm z).natAbs % 4 : ℕ) : ℤ) = 1 := by
      have habs := Int.natAbs_of_nonneg hN_nonneg
      omega
    omega
  · intro hd2 hd8
    have hcop8 : Nat.Coprime (Zsqrtd.norm z).natAbs 8 := by
      simpa [twoPrimeDiscriminantFactor, hd2, hd8] using hcop
    have hnodd : (Zsqrtd.norm z) % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN_nonneg hcop8
        (by norm_num : 2 ∣ 8)
    rcases zsqrtd_norm_emod_eight_eq_one_or_seven_of_param_mod_eight_two z hd8 hnodd
      with hmod | hmod
    · left
      have hcast : (((Zsqrtd.norm z).natAbs % 8 : ℕ) : ℤ) = 1 := by
        have habs := Int.natAbs_of_nonneg hN_nonneg
        omega
      omega
    · right
      have hcast : (((Zsqrtd.norm z).natAbs % 8 : ℕ) : ℤ) = 7 := by
        have habs := Int.natAbs_of_nonneg hN_nonneg
        omega
      omega
  · intro hd2 hd8_ne
    have hcop8 : Nat.Coprime (Zsqrtd.norm z).natAbs 8 := by
      simpa [twoPrimeDiscriminantFactor, hd2, hd8_ne] using hcop
    have hnodd : (Zsqrtd.norm z) % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN_nonneg hcop8
        (by norm_num : 2 ∣ 8)
    have hd4_ne_zero : D % 4 ≠ 0 := by
      intro hd40
      exact squarefree_int_not_dvd_four D (Fact.out : Squarefree D)
        (Int.dvd_of_emod_eq_zero hd40)
    have hd86 : D % 8 = 6 := by omega
    rcases zsqrtd_norm_emod_eight_eq_one_or_three_of_param_mod_eight_six z hd86 hnodd
      with hmod | hmod
    · left
      have hcast : (((Zsqrtd.norm z).natAbs % 8 : ℕ) : ℤ) = 1 := by
        have habs := Int.natAbs_of_nonneg hN_nonneg
        omega
      omega
    · right
      have hcast : (((Zsqrtd.norm z).natAbs % 8 : ℕ) : ℤ) = 3 := by
        have habs := Int.natAbs_of_nonneg hN_nonneg
        omega
      omega

private theorem legendreSym_zsqrtd_norm_eq_one_of_dvd_param
    {D : ℤ} {p : ℕ} [Fact p.Prime] (hpd : (p : ℤ) ∣ D) (z : Zsqrtd D)
    (hz : ¬ (p : ℤ) ∣ Zsqrtd.norm z) :
    legendreSym p (Zsqrtd.norm z) = 1 := by
  have hnorm_ne : ((Zsqrtd.norm z : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd (Zsqrtd.norm z) p).mp hzero)
  refine (legendreSym.eq_one_iff p hnorm_ne).mpr ?_
  refine ⟨(z.re : ZMod p), ?_⟩
  have hD_zero : ((D : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hpd
  rw [RingOfIntegers.norm_zsqrtd]
  push_cast
  rw [hD_zero]
  ring

private theorem legendreSym_zOnePlusSqrtOverTwo_norm_eq_one_of_dvd_discr
    {k : ℤ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : (p : ℤ) ∣ 1 + 4 * k) (z : ZOnePlusSqrtdOverTwo k)
    (hz : ¬ (p : ℤ) ∣ QuadraticAlgebra.norm z) :
    legendreSym p (QuadraticAlgebra.norm z) = 1 := by
  have hnorm_ne : ((QuadraticAlgebra.norm z : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd (QuadraticAlgebra.norm z) p).mp hzero)
  refine (legendreSym.eq_one_iff p hnorm_ne).mpr ?_
  let w : ZMod p := (2 : ZMod p) * (z.re : ZMod p) + (z.im : ZMod p)
  refine ⟨(2 : ZMod p)⁻¹ * w, ?_⟩
  have h2 : (2 : ZMod p) ≠ 0 :=
    Splitting.zmod_two_ne_zero_of_prime_ne_two p hp2
  have hD : (1 : ZMod p) + 4 * (k : ZMod p) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (1 + 4 * k) p).mpr hpd
    simpa using h
  have hk : (k : ZMod p) * 4 = -1 := by
    linear_combination hD
  rw [RingOfIntegers.norm_zOnePlusSqrtOverTwo]
  push_cast
  field_simp [w, h2]
  ring_nf
  rw [show (z.im : ZMod p) ^ 2 * (k : ZMod p) * 4 =
      ((k : ZMod p) * 4) * (z.im : ZMod p) ^ 2 by ring]
  rw [hk]
  ring

private theorem odd_ramified_dvd_param_of_mod_four_ne_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp_ram : p ∈ ramifiedPrimes D) (hp2 : p ≠ 2) (hd4 : D % 4 ≠ 1) :
    (p : ℤ) ∣ D := by
  have hp_prime : p.Prime := prime_of_mem_ramifiedPrimes hp_ram
  have hp_dvd_disc : (p : ℤ) ∣ NumberField.discr (Qsqrtd (D : ℚ)) :=
    dvd_discr_of_mem_ramifiedPrimes hp_ram
  rw [RingOfIntegers.discr_formula,
    RingOfIntegers.discrFormula_of_mod_four_ne_one hd4] at hp_dvd_disc
  have hp_int_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  rcases hp_int_prime.dvd_or_dvd hp_dvd_disc with hp4 | hpD
  · have hp_dvd_four_nat : p ∣ 4 := by
      exact_mod_cast hp4
    have hp_le4 : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp_dvd_four_nat
    interval_cases p
    · norm_num at hp_prime
    · norm_num at hp_prime
    · exact (hp2 rfl).elim
    · norm_num at hp_dvd_four_nat
    · norm_num at hp_prime
  · exact hpD

private theorem odd_ramified_dvd_param_of_mod_four_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp_ram : p ∈ ramifiedPrimes D) (hd4 : D % 4 = 1) :
    (p : ℤ) ∣ D := by
  have hp_dvd_disc : (p : ℤ) ∣ NumberField.discr (Qsqrtd (D : ℚ)) :=
    dvd_discr_of_mem_ramifiedPrimes hp_ram
  simpa [RingOfIntegers.discr_formula, RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    using hp_dvd_disc

private theorem two_not_mem_ramifiedPrimes_of_mod_four_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] (hd4 : D % 4 = 1) :
    2 ∉ ramifiedPrimes D := by
  intro h2ram
  have h2_dvd_disc : (2 : ℤ) ∣ NumberField.discr (Qsqrtd (D : ℚ)) :=
    dvd_discr_of_mem_ramifiedPrimes h2ram
  have h2D : (2 : ℤ) ∣ D := by
    simpa [RingOfIntegers.discr_formula, RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
      using h2_dvd_disc
  have hd2 : D % 2 = 0 := Int.emod_eq_zero_of_dvd h2D
  omega

/-- In the `ℤ[√d]` branch, nonnegative explicit norms prime to any signed
prime-discriminant factor have trivial Kronecker value. -/
theorem kroneckerSymNat_signedFactor_zsqrtd_norm_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (z : Zsqrtd D) (hd4 : D % 4 ≠ 1) (hN_nonneg : 0 ≤ Zsqrtd.norm z)
    (hcop : Nat.Coprime (Zsqrtd.norm z).natAbs q.1.natAbs) :
    kroneckerSymNat q.1 (Zsqrtd.norm z).natAbs = 1 := by
  rcases eq_twoPrimeDiscriminantFactor_or_exists_oddPrimeDiscriminantFactor_of_mem
      (d := D) q.property with htwo | hodd
  · rcases htwo with ⟨hq, _h2ram⟩
    rw [hq] at hcop ⊢
    exact kroneckerSymNat_twoPrimeDiscriminantFactor_zsqrtd_norm_eq_one
      z hd4 hN_nonneg hcop
  · rcases hodd with ⟨p, hp_ram, hp_prime, hp2, hq⟩
    rw [hq] at hcop ⊢
    letI : Fact p.Prime := ⟨hp_prime⟩
    rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
    have hcop_p : Nat.Coprime (Zsqrtd.norm z).natAbs p := by
      simpa [natAbs_oddPrimeDiscriminantFactor] using hcop
    have hnot_p_nat : ¬ p ∣ (Zsqrtd.norm z).natAbs :=
      (hp_prime.coprime_iff_not_dvd).mp hcop_p.symm
    have hnot_p_int : ¬ (p : ℤ) ∣ Zsqrtd.norm z := by
      intro hdiv
      exact hnot_p_nat (Int.natCast_dvd.mp hdiv)
    have hpd : (p : ℤ) ∣ D :=
      odd_ramified_dvd_param_of_mod_four_ne_one hp_ram hp2 hd4
    have h_absnorm_int : (((Zsqrtd.norm z).natAbs : ℕ) : ℤ) = Zsqrtd.norm z :=
      Int.natAbs_of_nonneg hN_nonneg
    rw [h_absnorm_int]
    exact legendreSym_zsqrtd_norm_eq_one_of_dvd_param hpd z hnot_p_int

/-- In the half-integral branch, nonnegative explicit norms prime to any signed
prime-discriminant factor have trivial Kronecker value. -/
theorem kroneckerSymNat_signedFactor_zOnePlusSqrtOverTwo_norm_eq_one
    {D k : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (z : ZOnePlusSqrtdOverTwo k) (hk : D = 1 + 4 * k)
    (hN_nonneg : 0 ≤ QuadraticAlgebra.norm z)
    (hcop : Nat.Coprime (QuadraticAlgebra.norm z).natAbs q.1.natAbs) :
    kroneckerSymNat q.1 (QuadraticAlgebra.norm z).natAbs = 1 := by
  have hd4 : D % 4 = 1 := by
    rw [hk]
    omega
  rcases eq_twoPrimeDiscriminantFactor_or_exists_oddPrimeDiscriminantFactor_of_mem
      (d := D) q.property with htwo | hodd
  · rcases htwo with ⟨_hq, h2ram⟩
    exact (two_not_mem_ramifiedPrimes_of_mod_four_eq_one hd4 h2ram).elim
  · rcases hodd with ⟨p, hp_ram, hp_prime, hp2, hq⟩
    rw [hq] at hcop ⊢
    letI : Fact p.Prime := ⟨hp_prime⟩
    rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
    have hcop_p : Nat.Coprime (QuadraticAlgebra.norm z).natAbs p := by
      simpa [natAbs_oddPrimeDiscriminantFactor] using hcop
    have hnot_p_nat : ¬ p ∣ (QuadraticAlgebra.norm z).natAbs :=
      (hp_prime.coprime_iff_not_dvd).mp hcop_p.symm
    have hnot_p_int : ¬ (p : ℤ) ∣ QuadraticAlgebra.norm z := by
      intro hdiv
      exact hnot_p_nat (Int.natCast_dvd.mp hdiv)
    have hpd : (p : ℤ) ∣ D :=
      odd_ramified_dvd_param_of_mod_four_eq_one hp_ram hd4
    have h_absnorm_int :
        (((QuadraticAlgebra.norm z).natAbs : ℕ) : ℤ) = QuadraticAlgebra.norm z :=
      Int.natAbs_of_nonneg hN_nonneg
    rw [h_absnorm_int]
    exact legendreSym_zOnePlusSqrtOverTwo_norm_eq_one_of_dvd_discr hp2
      (by simpa [hk] using hpd) z hnot_p_int

/-- In the `d % 4 ≠ 1` ring-of-integers branch, a principal ideal generated by
an element with nonnegative algebra norm has trivial Kronecker value at every
signed prime-discriminant factor coprime to its absolute norm. -/
theorem kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_mod_four_ne_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))} (hd4 : D % 4 ≠ 1)
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    kroneckerSymNat q.1
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) = 1 := by
  let z : Zsqrtd D :=
    (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one D hd4) α
  have hnorm : Algebra.norm ℤ α = Zsqrtd.norm z := by
    simpa [z] using RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one
      (d := D) hd4 α
  have hz_nonneg : 0 ≤ Zsqrtd.norm z := by
    rwa [hnorm] at hN_nonneg
  have hcop_z : Nat.Coprime (Zsqrtd.norm z).natAbs q.1.natAbs := by
    simpa [Ideal.absNorm_span_singleton, hnorm] using hcop
  rw [Ideal.absNorm_span_singleton, hnorm]
  exact kroneckerSymNat_signedFactor_zsqrtd_norm_eq_one q z hd4 hz_nonneg hcop_z

/-- In the `d % 4 = 1` ring-of-integers branch, a principal ideal generated by
an element with nonnegative algebra norm has trivial Kronecker value at every
signed prime-discriminant factor coprime to its absolute norm. -/
theorem kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_mod_four_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))} (hd4 : D % 4 = 1)
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    kroneckerSymNat q.1
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) = 1 := by
  obtain ⟨k, hk⟩ := RingOfIntegers.exists_k_of_mod_four_eq_one hd4
  let z : ZOnePlusSqrtdOverTwo k :=
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq D k hk) α
  have hnorm : Algebra.norm ℤ α = QuadraticAlgebra.norm z := by
    simpa [z] using RingOfIntegers.algebraNorm_eq_zOnePlusSqrtOverTwo_norm_of_eq
      (d := D) k hk α
  have hz_nonneg : 0 ≤ QuadraticAlgebra.norm z := by
    rwa [hnorm] at hN_nonneg
  have hcop_z : Nat.Coprime (QuadraticAlgebra.norm z).natAbs q.1.natAbs := by
    simpa [Ideal.absNorm_span_singleton, hnorm] using hcop
  rw [Ideal.absNorm_span_singleton, hnorm]
  exact kroneckerSymNat_signedFactor_zOnePlusSqrtOverTwo_norm_eq_one q z hk hz_nonneg
    hcop_z

/-- A principal ideal generated by an element with nonnegative algebra norm has
trivial Kronecker value at every signed prime-discriminant factor coprime to its
absolute norm. -/
theorem kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_algebraNorm_nonneg
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    kroneckerSymNat q.1
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) = 1 := by
  by_cases hd4 : D % 4 = 1
  · exact kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_mod_four_eq_one
      q hd4 hN_nonneg hcop
  · exact kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_mod_four_ne_one
      q hd4 hN_nonneg hcop

/-- The raw signed-factor character is trivial on a principal ideal generated by an
element of nonnegative algebra norm whose principal absolute norm is coprime to the
signed factor. -/
theorem genusCharacterOfSignedFactorRaw_span_eq_one_of_algebraNorm_nonneg
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    genusCharacterOfSignedFactorRaw D q
        ⟨Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hcop⟩ =
      1 := by
  ext
  simpa [genusCharacterOfSignedFactorRaw_val] using
    kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_algebraNorm_nonneg
      q hN_nonneg hcop

/-- A totally positive algebraic integer in `𝓞(Q(√D))` has nonnegative
integer algebra norm. In the imaginary case this is the existing quadratic norm
positivity; in the real case it follows by evaluating at the two explicit real
embeddings. -/
theorem algebraNorm_nonneg_of_isTotallyPositive
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hpos : NarrowClassGroup.IsTotallyPositive
      (algebraMap (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) α)) :
    0 ≤ Algebra.norm ℤ α := by
  by_cases hDneg : D < 0
  · exact RingOfIntegers.algebraNorm_nonneg_of_neg D hDneg α
  have hD_ne_zero : D ≠ 0 :=
    Squarefree.ne_zero (Fact.out : Squarefree D)
  have hDpos : 0 < D := by omega
  have hD_nonneg_real : 0 ≤ (D : ℝ) := by exact_mod_cast le_of_lt hDpos
  let e : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))) ≃ₐ[
      NumberField.RingOfIntegers (Qsqrtd (D : ℚ))] Qsqrtd (D : ℚ) :=
    FractionRing.algEquiv
      (A := NumberField.RingOfIntegers (Qsqrtd (D : ℚ))) (Qsqrtd (D : ℚ))
  let σpos : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))) →+* ℝ :=
    (Qsqrtd.realEmbeddingPos D hD_nonneg_real).toRingHom.comp e.toRingHom
  let σneg : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))) →+* ℝ :=
    (Qsqrtd.realEmbeddingNeg D hD_nonneg_real).toRingHom.comp e.toRingHom
  have hpos_pos : 0 < Qsqrtd.realEmbeddingPos D hD_nonneg_real
      (α : Qsqrtd (D : ℚ)) := by
    simpa [σpos, e] using hpos σpos
  have hpos_neg : 0 < Qsqrtd.realEmbeddingNeg D hD_nonneg_real
      (α : Qsqrtd (D : ℚ)) := by
    simpa [σneg, e] using hpos σneg
  have hnorm_pos_real : 0 < (Qsqrtd.norm (α : Qsqrtd (D : ℚ)) : ℝ) :=
    Qsqrtd.norm_pos_of_realEmbedding_pos D hD_nonneg_real hpos_pos hpos_neg
  have hnorm_pos_rat : 0 < Qsqrtd.norm (α : Qsqrtd (D : ℚ)) := by
    exact_mod_cast hnorm_pos_real
  have hcast : (0 : ℚ) ≤ (Algebra.norm ℤ α : ℚ) := by
    rw [Algebra.coe_norm_int (K := Qsqrtd (D : ℚ)),
      Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
    exact le_of_lt hnorm_pos_rat
  exact_mod_cast hcast

/-- If a totally positive fraction-field unit is represented as `a / b`, then
the integral element `a * b` has nonnegative algebra norm. Multiplying by the
positive square `b²` clears the denominator without changing signs at real
embeddings. -/
theorem algebraNorm_nonneg_mul_of_isTotallyPositive_mk'
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))ˣ}
    {a b : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hb : b ≠ 0)
    (hmk : IsLocalization.mk'
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) a
        ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) :
    0 ≤ Algebra.norm ℤ (a * b) := by
  refine algebraNorm_nonneg_of_isTotallyPositive ?_
  intro σ
  have hb_map_ne :
      algebraMap (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  have hmul :
      algebraMap (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) (a * b) =
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          algebraMap (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) b ^ 2 := by
    rw [map_mul]
    rw [← hmk, IsFractionRing.mk'_eq_div]
    field_simp [hb_map_ne]
  rw [hmul, map_mul, map_pow]
  exact mul_pos (hxpos σ)
    (sq_pos_of_ne_zero ((_root_.map_ne_zero σ).mpr hb_map_ne))

/-- Multiplying by a principal ideal generated by an element of nonnegative
algebra norm does not change the raw signed-factor character, provided the
principal ideal is coprime to the signed factor. -/
theorem genusCharacterOfSignedFactorRaw_mul_span_eq_self_of_algebraNorm_nonneg
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I : signedFactorCoprimeIdealSubmonoid D q)
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    genusCharacterOfSignedFactorRaw D q
        (I * ⟨Ideal.span
          ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hcop⟩) =
      genusCharacterOfSignedFactorRaw D q I := by
  change (genusCharacterOfSignedFactorRawOnCoprimeIdeals D q)
      (I * ⟨Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hcop⟩) =
    (genusCharacterOfSignedFactorRawOnCoprimeIdeals D q) I
  rw [map_mul]
  change genusCharacterOfSignedFactorRaw D q I *
      genusCharacterOfSignedFactorRaw D q
        ⟨Ideal.span
          ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hcop⟩ =
    genusCharacterOfSignedFactorRaw D q I
  rw [genusCharacterOfSignedFactorRaw_span_eq_one_of_algebraNorm_nonneg q hN_nonneg hcop,
    mul_one]

/-- A denominator-cleared principal relation is enough to compare raw
signed-factor characters: a nonnegative-norm principal multiplier is invisible,
and a square principal multiplier is invisible. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_span_mul_eq_span_sq_mul
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I J : signedFactorCoprimeIdealSubmonoid D q)
    {α β : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hα_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hαcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs)
    (hβcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs)
    (hprod : Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span
          ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span
            ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) :
    genusCharacterOfSignedFactorRaw D q I =
      genusCharacterOfSignedFactorRaw D q J := by
  let A : signedFactorCoprimeIdealSubmonoid D q :=
    ⟨Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hαcop⟩
  let B : signedFactorCoprimeIdealSubmonoid D q :=
    ⟨Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hβcop⟩
  have hprod' : I * A = J * B ^ 2 := by
    apply Subtype.ext
    change (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (A : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        ((B : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) ^ 2)
    dsimp [A, B]
    rw [pow_two]
    change (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    calc
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) := by
          rw [mul_comm]
      _ =
        Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) := hprod
      _ = (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) := by
          ac_rfl
  have hA :
      genusCharacterOfSignedFactorRaw D q A = 1 :=
    genusCharacterOfSignedFactorRaw_span_eq_one_of_algebraNorm_nonneg q hα_nonneg hαcop
  have hB :
      genusCharacterOfSignedFactorRaw D q (B ^ 2) = 1 :=
    genusCharacterOfSignedFactorRaw_sq D q B
  exact genusCharacterOfSignedFactorRaw_eq_of_mul_eq_of_raw_eq D q I J A (B ^ 2)
    hprod' (by rw [hA, hB])

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
