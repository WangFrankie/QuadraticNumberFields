/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.GenusTheory.PrimeDiscriminant
import QuadraticNumberFields.ClassGroup.Narrow
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.RingOfIntegers.Norm
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QNFMathlib.RingTheory.ClassGroup
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker
/-!
# Basic Genus-Character Infrastructure

This file contains the character target, signed-factor-coprime ideal
submonoids, raw signed-factor characters, and the restricted narrow-class-group
map used by the new genus-theory layer. The final well-defined characters and
genus-character map are packaged in `Genus.Characters`.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

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
    rw [← pow_succ, Nat.sub_add_cancel hcard_pos]
  rw [hpow] at hmul
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) hmul

/-- The product-one genus-character target has cardinality `2 ^ (t - 1)`, where
`t = ramifiedPrimeCount d`. -/
theorem card_genusCharacterTargetRelation :
    Nat.card (genusCharacterTargetRelation d) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  refine card_genusCharacterTargetRelation_of_nonempty d ?_
  rw [signedPrimeDiscriminantFactors_nonempty_iff, ← Finset.card_pos,
    ← ramifiedPrimeCount_eq_card]
  exact one_le_ramifiedPrimeCount d

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

private theorem exists_nat_forall_pos_add_nat_mul {ι : Type*} [Finite ι]
    (x : ι → ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, ∀ i : ι, 0 < x i + (k : ℝ) * c := by
  classical
  letI := Fintype.ofFinite ι
  let B : ℝ := ∑ i : ι, max 0 ((-x i) / c)
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨k + 1, ?_⟩
  intro i
  have hnonneg : ∀ j : ι, 0 ≤ max 0 ((-x j) / c) := by
    intro j
    exact le_max_left _ _
  have hi_le_B : (-x i) / c ≤ B := by
    have hle_max : (-x i) / c ≤ max 0 ((-x i) / c) := le_max_right _ _
    have hmax_le_sum : max 0 ((-x i) / c) ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    exact hle_max.trans hmax_le_sum
  have hlt : (-x i) / c < (k + 1 : ℕ) :=
    lt_of_le_of_lt hi_le_B (lt_trans hk (by norm_num))
  have hlt_real : (-x i) / c < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlt
  have hmul : -x i < ((k + 1 : ℕ) : ℝ) * c :=
    (div_lt_iff₀ hc).mp hlt_real
  linarith

private theorem narrow_mk0_span_singleton_eq_one_of_isTotallyPositive
    {a : NumberField.RingOfIntegers (Qsqrtd (d : ℚ))}
    (ha : a ≠ 0)
    (hpos : NarrowClassGroup.IsTotallyPositive
      (algebraMap (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) a)) :
    NarrowClassGroup.mk0
      (R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
      ⟨Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))), by
        rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
          Ideal.span_singleton_eq_bot]
        exact ha⟩ = 1 := by
  let OK := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let K := FractionRing OK
  have haK : algebraMap OK K a ≠ 0 := by
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    exact ha
  let u : Kˣ := Units.mk0 (algebraMap OK K a) haK
  have hu_pos : u ∈ NarrowClassGroup.totallyPositiveUnits K := hpos
  rw [← NarrowClassGroup.mk_mk0, NarrowClassGroup.mk_eq_mk']
  exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨u, hu_pos⟩, by
    apply Units.ext
    change (toPrincipalIdeal OK K u : FractionalIdeal OK⁰ K) =
      FractionalIdeal.mk0 K
        ⟨Ideal.span ({a} : Set OK), by
          rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
            Ideal.span_singleton_eq_bot]
          exact ha⟩
    rw [coe_toPrincipalIdeal]
    change FractionalIdeal.spanSingleton OK⁰ (algebraMap OK K a) =
      (Ideal.span ({a} : Set OK) : FractionalIdeal OK⁰ K)
    rw [FractionalIdeal.coeIdeal_span_singleton]
  ⟩

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
  classical
  let OK := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let M : ℕ := Finset.univ.prod
    (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => q.1.natAbs)
  let Mideal : Ideal OK := Ideal.span ({(M : OK)} : Set OK)
  have hM_ne : M ≠ 0 := by
    dsimp [M]
    exact Finset.prod_ne_zero_iff.mpr fun q _ =>
      natAbs_ne_zero_of_mem_signedPrimeDiscriminantFactors d q.property
  have hM_cast_ne : (M : OK) ≠ 0 := Nat.cast_ne_zero.mpr hM_ne
  by_cases hMtop : Mideal = ⊤
  · obtain ⟨I, hI⟩ := NarrowClassGroup.mk0_surjective C
    refine ⟨I, hI, ?_⟩
    intro q
    have hq_dvd_M : (q.1.natAbs : OK) ∣ (M : OK) := by
      have hq_dvd_M_nat : q.1.natAbs ∣ M := by
        dsimp [M]
        exact Finset.dvd_prod_of_mem
          (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => q.1.natAbs)
          (Finset.mem_univ q)
      exact_mod_cast Nat.cast_dvd_cast hq_dvd_M_nat
    have hspan_le :
        Mideal ≤ Ideal.span ({(q.1.natAbs : OK)} : Set OK) := by
      dsimp [Mideal]
      exact Ideal.span_singleton_le_span_singleton.mpr hq_dvd_M
    have hspan_q_top : Ideal.span ({(q.1.natAbs : OK)} : Set OK) = ⊤ := by
      have htop_le : (⊤ : Ideal OK) ≤ Ideal.span ({(q.1.natAbs : OK)} : Set OK) := by
        rw [← hMtop]
        exact hspan_le
      exact top_le_iff.mp htop_le
    change (I : Ideal OK) ⊔ Ideal.span ({(q.1.natAbs : OK)} : Set OK) = ⊤
    rw [hspan_q_top, sup_top_eq]
  · obtain ⟨A, hA⟩ := NarrowClassGroup.mk0_surjective (C⁻¹)
    have hA0 : (A : Ideal OK) ≠ 0 := by
      have h := A.2
      rwa [mem_nonZeroDivisors_iff_ne_zero] at h
    have hM0 : Mideal ≠ 0 := by
      rw [Ideal.zero_eq_bot, ne_eq]
      dsimp [Mideal]
      rw [Ideal.span_singleton_eq_bot]
      exact hM_cast_ne
    have hle : (A : Ideal OK) * Mideal ≤ (A : Ideal OK) :=
      Ideal.mul_le_inf.trans inf_le_left
    have hAM0 : (A : Ideal OK) * Mideal ≠ 0 := mul_ne_zero hA0 hM0
    obtain ⟨a₀, hsup₀⟩ := IsDedekindDomain.exists_sup_span_eq hle hAM0
    have hspan₀_le : Ideal.span ({a₀} : Set OK) ≤ (A : Ideal OK) :=
      le_sup_right.trans hsup₀.le
    let n : ℕ := Ideal.absNorm ((A : Ideal OK) * Mideal)
    have hn_mem : (n : OK) ∈ (A : Ideal OK) * Mideal := by
      change (Ideal.absNorm ((A : Ideal OK) * Mideal) : OK) ∈ (A : Ideal OK) * Mideal
      exact Ideal.absNorm_mem ((A : Ideal OK) * Mideal)
    have hn_ne : n ≠ 0 := by
      intro hn
      have hnorm_zero : Ideal.absNorm ((A : Ideal OK) * Mideal) = 0 := by
        simpa [n] using hn
      rw [Ideal.absNorm_eq_zero_iff] at hnorm_zero
      exact hAM0 (by simpa [Ideal.zero_eq_bot] using hnorm_zero)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn_ne
    let x : (FractionRing OK →+* ℝ) → ℝ := fun σ =>
      σ (algebraMap OK (FractionRing OK) a₀)
    rcases exists_nat_forall_pos_add_nat_mul x hn_pos with ⟨k, hk⟩
    let a : OK := a₀ + (k : OK) * (n : OK)
    have ha_sub_mem : a - a₀ ∈ (A : Ideal OK) * Mideal := by
      dsimp [a]
      rw [add_sub_cancel_left]
      exact Ideal.mul_mem_left _ (k : OK) hn_mem
    have ha_pos : NarrowClassGroup.IsTotallyPositive
        (algebraMap OK (FractionRing OK) a) := by
      intro σ
      have hσ := hk σ
      have hk_map : σ (algebraMap OK (FractionRing OK) (k : OK)) = (k : ℝ) := by
        exact map_natCast (σ.comp (algebraMap OK (FractionRing OK))) k
      have hn_map : σ (algebraMap OK (FractionRing OK) (n : OK)) = (n : ℝ) := by
        exact map_natCast (σ.comp (algebraMap OK (FractionRing OK))) n
      rw [show σ (algebraMap OK (FractionRing OK) a) =
          σ (algebraMap OK (FractionRing OK) a₀) +
            σ (algebraMap OK (FractionRing OK) (k : OK)) *
              σ (algebraMap OK (FractionRing OK) (n : OK)) by
          simp [a, map_add, map_mul]]
      rw [hk_map, hn_map]
      exact hσ
    have ha_mem_A : a ∈ (A : Ideal OK) := by
      dsimp [a]
      have hkn_mem : (k : OK) * (n : OK) ∈ (A : Ideal OK) * Mideal :=
        Ideal.mul_mem_left _ (k : OK) hn_mem
      exact add_mem (hspan₀_le (Ideal.mem_span_singleton_self a₀))
        (hle hkn_mem)
    have hspan_a_le : Ideal.span ({a} : Set OK) ≤ (A : Ideal OK) :=
      (Ideal.span_singleton_le_iff_mem (I := (A : Ideal OK))).mpr ha_mem_A
    have hsup_a : (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) =
        (A : Ideal OK) := by
      apply le_antisymm
      · exact sup_le hle hspan_a_le
      · calc
          (A : Ideal OK) = (A : Ideal OK) * Mideal ⊔ Ideal.span ({a₀} : Set OK) :=
            hsup₀.symm
          _ ≤ (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) := by
            apply sup_le le_sup_left
            have ha_mem_sup :
                a ∈ (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) :=
              (show Ideal.span ({a} : Set OK) ≤
                (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) from le_sup_right)
                  (Ideal.mem_span_singleton_self a)
            have hdiff_mem_sup :
                a - a₀ ∈ (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) :=
              (show (A : Ideal OK) * Mideal ≤
                (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) from le_sup_left)
                  ha_sub_mem
            have hsub := sub_mem ha_mem_sup hdiff_mem_sup
            have ha₀_mem_sup : a₀ ∈
                (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) := by
              convert hsub using 1
              ring
            exact (Ideal.span_singleton_le_iff_mem
              (I := (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK))).mpr ha₀_mem_sup
    have ha_ne : a ≠ 0 := by
      intro ha
      apply hMtop
      have hspan_zero : Ideal.span ({a} : Set OK) = ⊥ := by
        rw [ha, Ideal.span_singleton_eq_bot]
      rw [hspan_zero, sup_bot_eq] at hsup_a
      have hAM1 : (A : Ideal OK) * Mideal = (A : Ideal OK) * 1 := by
        rw [hsup_a, mul_one]
      have hM1 : Mideal = 1 := mul_left_cancel₀ hA0 hAM1
      rwa [Ideal.one_eq_top] at hM1
    obtain ⟨I, hImul⟩ := Ideal.dvd_iff_le.mpr hspan_a_le
    have hI0 : I ≠ 0 := by
      intro h
      rw [h, mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hImul
      exact ha_ne hImul
    refine ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩, ?_, ?_⟩
    · have hprin :
          NarrowClassGroup.mk0
            (A * ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩) = 1 := by
        have hAI_eq :
            A * ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩ =
              ⟨Ideal.span ({a} : Set OK), by
                rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
                  Ideal.span_singleton_eq_bot]
                exact ha_ne⟩ := by
          ext x
          change x ∈ (A : Ideal OK) * I ↔ x ∈ Ideal.span ({a} : Set OK)
          rw [hImul]
        rw [hAI_eq]
        exact narrow_mk0_span_singleton_eq_one_of_isTotallyPositive d ha_ne ha_pos
      rw [map_mul, hA, inv_mul_eq_one] at hprin
      exact hprin.symm
    · have hIcop_M : I ⊔ Mideal = ⊤ := by
        have hkey : (A : Ideal OK) * (Mideal ⊔ I) = (A : Ideal OK) := by
          rw [Ideal.mul_sup, ← hImul, hsup_a]
        have hkey1 : (A : Ideal OK) * (Mideal ⊔ I) = (A : Ideal OK) * 1 := by
          rw [hkey, mul_one]
        have hMI : Mideal ⊔ I = 1 := mul_left_cancel₀ hA0 hkey1
        rw [sup_comm, hMI, Ideal.one_eq_top]
      intro q
      have hq_dvd_M : (q.1.natAbs : OK) ∣ (M : OK) := by
        have hq_dvd_M_nat : q.1.natAbs ∣ M := by
          dsimp [M]
          exact Finset.dvd_prod_of_mem
            (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => q.1.natAbs)
            (Finset.mem_univ q)
        exact_mod_cast Nat.cast_dvd_cast hq_dvd_M_nat
      have hspan_le :
          Mideal ≤ Ideal.span ({(q.1.natAbs : OK)} : Set OK) := by
        dsimp [Mideal]
        exact Ideal.span_singleton_le_span_singleton.mpr hq_dvd_M
      have htop_le := sup_le_sup_left hspan_le I
      rw [hIcop_M] at htop_le
      exact top_le_iff.mp htop_le

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

end GenusTheory
end ClassGroup
end QuadraticNumberFields
