/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.ClassGroup.Narrow
import QuadraticNumberFields.ClassGroup.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex

attribute [-instance] DivisionRing.toRatAlgebra

/-!
# Narrow Class Groups of Quadratic Fields

This file specializes the generic `NarrowClassGroup` API to the standard
quadratic fields `Qsqrtd d`.
-/

open scoped NumberField nonZeroDivisors

namespace QuadraticNumberFields

/-- Scoped notation for the narrow ideal class group `Cl⁺(𝓞(ℚ(√d)))`. -/
scoped[QuadraticNumberFields.ClassGroup]
  notation "Cl⁺(" d ")" => NarrowClassGroup
    (NumberField.RingOfIntegers
      (Qsqrtd ((d : ℤ) : ℚ)))

namespace Qsqrtd

open _root_.Qsqrtd

open scoped QuadraticNumberFields.ClassGroup

section NarrowClassGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞 (Qsqrtd (d : ℚ))

/-- The narrow class number of `ℚ(√d)`. -/
noncomputable def narrowClassNumber : ℕ :=
  NarrowClassGroup.classNumber OK

/-- The natural map from the narrow class group of `𝓞(ℚ(√d))` to the ordinary
wide ideal class group. -/
noncomputable abbrev narrowToClassGroup :
    Cl⁺(d) →* Cl(d) :=
  NarrowClassGroup.toClassGroup OK

/-- The natural map from the narrow class group to the ordinary wide ideal class
group is surjective. -/
theorem narrowToClassGroup_surjective :
    Function.Surjective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_surjective OK

/-- The kernel of `Cl⁺(d) → Cl(d)` is controlled by the sign vectors realized by
units of the fraction field. -/
theorem card_narrowToClassGroup_ker_dvd_card_signVectorRange :
    Nat.card (narrowToClassGroup d).ker ∣
      Nat.card (NarrowClassGroup.signVectorHom (FractionRing OK)).range :=
  NarrowClassGroup.card_toClassGroup_ker_dvd_card_signVectorRange OK

/-- The kernel of `Cl⁺(d) → Cl(d)` is bounded by the field-unit sign quotient
after quotienting by the diagonal sign represented by `-1`. -/
theorem card_narrowToClassGroup_ker_dvd_card_signQuotientModuloNegOne :
    Nat.card (narrowToClassGroup d).ker ∣
      Nat.card (NarrowClassGroup.signQuotientModuloNegOne OK) :=
  NarrowClassGroup.card_toClassGroup_ker_dvd_card_signQuotientModuloNegOne OK

/-- The class of `-1` in the fraction-field sign quotient is killed by
`Kˣ/K⁺ → P/P⁺`. -/
theorem negOne_mem_unitsQuotientTotallyPositiveToPrincipalIdealQuotient_ker :
    QuotientGroup.mk' (NarrowClassGroup.totallyPositiveUnits (FractionRing OK))
        (-1 : (FractionRing OK)ˣ) ∈
      (NarrowClassGroup.unitsQuotientTotallyPositiveToPrincipalIdealQuotient OK).ker :=
  NarrowClassGroup.negOne_mem_unitsQuotientTotallyPositiveToPrincipalIdealQuotient_ker OK

/-- If every unit of the fraction field of `𝓞(ℚ(√d))` is totally positive, then
the narrow class group and ordinary wide class group are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup_of_forall_isTotallyPositive
    (hpos : ∀ x : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing OK)) :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  NarrowClassGroup.nonempty_mulEquivClassGroup_of_forall_isTotallyPositive OK hpos

/-- If every unit of the fraction field of `𝓞(ℚ(√d))` is totally positive, then
the natural map from the narrow class group to the ordinary wide class group is
bijective. -/
theorem narrowToClassGroup_bijective_of_forall_isTotallyPositive
    (hpos : ∀ x : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing OK)) :
    Function.Bijective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_bijective_of_forall_isTotallyPositive OK hpos

namespace Real

/-- If `d > 0`, the fraction field of `𝓞(ℚ(√d))` has a real embedding. -/
theorem nonempty_fractionRing_realEmbeddings (hd : 0 < d) :
    Nonempty (FractionRing OK →+* ℝ) := by
  haveI : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) :=
    { finrank_eq_two' := QuadraticAlgebra.finrank_eq_two ((d : ℤ) : ℚ) 0 }
  haveI : QuadraticField (Qsqrtd (d : ℚ)) :=
    { isQuadratic := inferInstance }
  haveI : NumberField (Qsqrtd (d : ℚ)) :=
    QuadraticField.instNumberField (Qsqrtd (d : ℚ))
  haveI : IsFractionRing OK (Qsqrtd (d : ℚ)) := inferInstance
  let e := IsLocalization.algEquiv OK⁰ (FractionRing OK) (Qsqrtd (d : ℚ))
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  exact ⟨(Qsqrtd.realEmbeddingPos d hd_nonneg_real).toRingHom.comp e.toRingHom⟩

/-- The fraction field of `𝓞(ℚ(√d))` has at most two real embeddings. -/
theorem card_fractionRing_realEmbeddings_le_two :
    Nat.card (FractionRing OK →+* ℝ) ≤ 2 := by
  classical
  letI : Algebra ℚ (Qsqrtd (d : ℚ)) := DivisionRing.toRatAlgebra
  haveI : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) :=
    { finrank_eq_two' := finrank_ratAlgebra_eq_two ((d : ℤ) : ℚ) }
  haveI : QuadraticField (Qsqrtd (d : ℚ)) :=
    { isQuadratic := inferInstance }
  haveI : NumberField (Qsqrtd (d : ℚ)) :=
    QuadraticField.instNumberField (Qsqrtd (d : ℚ))
  haveI : IsFractionRing OK (Qsqrtd (d : ℚ)) := inferInstance
  let e := IsLocalization.algEquiv OK⁰ (FractionRing OK) (Qsqrtd (d : ℚ))
  let toComplex : (FractionRing OK →+* ℝ) → (Qsqrtd (d : ℚ) →+* ℂ) :=
    fun σ => Complex.ofRealHom.comp (σ.comp e.symm.toRingHom)
  have hinj : Function.Injective toComplex := by
    intro σ τ hστ
    ext x
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    have hy := RingHom.congr_fun hστ y
    exact Complex.ofReal_injective hy
  have hle : Nat.card (FractionRing OK →+* ℝ) ≤ Nat.card (Qsqrtd (d : ℚ) →+* ℂ) :=
    Nat.card_le_card_of_injective toComplex hinj
  have hcomplex : Nat.card (Qsqrtd (d : ℚ) →+* ℂ) = 2 := by
    rw [Nat.card_eq_fintype_card, NumberField.Embeddings.card]
    exact finrank_ratAlgebra_eq_two ((d : ℤ) : ℚ)
  exact hle.trans_eq hcomplex

/-- For `d > 0`, the class of `-1` in `Kˣ/K⁺` is nontrivial. -/
theorem quotient_mk'_negOne_ne_one (hd : 0 < d) :
    QuotientGroup.mk' (NarrowClassGroup.totallyPositiveUnits (FractionRing OK))
        (-1 : (FractionRing OK)ˣ) ≠ 1 := by
  haveI : Nonempty (FractionRing OK →+* ℝ) :=
    nonempty_fractionRing_realEmbeddings d hd
  exact NarrowClassGroup.quotient_mk'_negOne_ne_one_of_nonempty_realEmbeddings

/-- For `d > 0`, the sign-unit map `Kˣ/K⁺ → P/P⁺` has nontrivial kernel. -/
theorem unitsQuotientTotallyPositiveToPrincipalIdealQuotient_ker_ne_bot (hd : 0 < d) :
    (NarrowClassGroup.unitsQuotientTotallyPositiveToPrincipalIdealQuotient OK).ker ≠ ⊥ := by
  intro hker
  have hmem := negOne_mem_unitsQuotientTotallyPositiveToPrincipalIdealQuotient_ker d
  have hbot : QuotientGroup.mk' (NarrowClassGroup.totallyPositiveUnits (FractionRing OK))
      (-1 : (FractionRing OK)ˣ) ∈
        (⊥ : Subgroup ((FractionRing OK)ˣ ⧸
          NarrowClassGroup.totallyPositiveUnits (FractionRing OK))) := by
    simpa [hker] using hmem
  rw [Subgroup.mem_bot] at hbot
  exact quotient_mk'_negOne_ne_one d hd hbot

/-- For `d > 0`, if the fraction field has at most two real embeddings, then
the sign quotient modulo the diagonal sign represented by `-1` has cardinality
dividing `2`. The remaining input is the real-quadratic embedding count. -/
theorem card_signQuotientModuloNegOne_dvd_two_of_card_realEmbeddings_le_two
    (hd : 0 < d)
    (hemb : Nat.card (FractionRing OK →+* ℝ) ≤ 2) :
    Nat.card (NarrowClassGroup.signQuotientModuloNegOne OK) ∣ 2 := by
  haveI : Nonempty (FractionRing OK →+* ℝ) :=
    nonempty_fractionRing_realEmbeddings d hd
  exact NarrowClassGroup.card_signQuotientModuloNegOne_dvd_two_of_card_realEmbeddings_le_two
    OK hemb

/-- For `d > 0`, quotienting the sign quotient by the diagonal sign represented
by `-1` leaves a group whose cardinality divides `2`. -/
theorem card_signQuotientModuloNegOne_dvd_two (hd : 0 < d) :
    Nat.card (NarrowClassGroup.signQuotientModuloNegOne OK) ∣ 2 :=
  card_signQuotientModuloNegOne_dvd_two_of_card_realEmbeddings_le_two d hd
    (card_fractionRing_realEmbeddings_le_two d)

/-- For `d > 0`, the field-unit sign quotient modulo the diagonal sign
represented by `-1` has exactly two elements. -/
theorem card_signQuotientModuloNegOne_eq_two (hd : 0 < d) :
    Nat.card (NarrowClassGroup.signQuotientModuloNegOne OK) = 2 := by
  haveI : Nonempty (FractionRing OK →+* ℝ) :=
    nonempty_fractionRing_realEmbeddings d hd
  haveI : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) :=
    { finrank_eq_two' := QuadraticAlgebra.finrank_eq_two ((d : ℤ) : ℚ) 0 }
  haveI : QuadraticField (Qsqrtd (d : ℚ)) :=
    { isQuadratic := inferInstance }
  haveI : NumberField (Qsqrtd (d : ℚ)) :=
    QuadraticField.instNumberField (Qsqrtd (d : ℚ))
  haveI : IsFractionRing OK (Qsqrtd (d : ℚ)) := inferInstance
  let e := IsLocalization.algEquiv OK⁰ (FractionRing OK) (Qsqrtd (d : ℚ))
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  let σ : FractionRing OK →+* ℝ :=
    (realEmbeddingPos d hd_nonneg_real).toRingHom.comp e.toRingHom
  let τ : FractionRing OK →+* ℝ :=
    (realEmbeddingNeg d hd_nonneg_real).toRingHom.comp e.toRingHom
  have homega_ne_zero : (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)) ≠ 0 := by
    intro h
    have him := congrArg QuadraticAlgebra.im h
    norm_num at him
  have hx0 : e.symm QuadraticAlgebra.omega ≠ 0 := by
    intro h
    apply homega_ne_zero
    have hmap := congrArg e h
    simpa using hmap
  let x : (FractionRing OK)ˣ := Units.mk0 (e.symm QuadraticAlgebra.omega) hx0
  have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_real_pos
  have hσpos : 0 < σ (x : FractionRing OK) := by
    dsimp [σ, x]
    rw [AlgEquiv.apply_symm_apply]
    rw [realEmbeddingPos_apply]
    simpa using hsqrt_pos
  have hτneg : τ (x : FractionRing OK) < 0 := by
    dsimp [τ, x]
    rw [AlgEquiv.apply_symm_apply]
    rw [realEmbeddingNeg_apply]
    simpa using neg_lt_zero.mpr hsqrt_pos
  exact NarrowClassGroup.card_signQuotientModuloNegOne_eq_two_of_signRatio_ne_one
    OK (card_fractionRing_realEmbeddings_le_two d)
    (NarrowClassGroup.signRatioHom_ne_one_of_pos_neg σ τ x hσpos hτneg)

/-- For `d > 0`, the sign-correction exact sequence has cardinality
`|ker((Kˣ/K⁺)/⟨-1⟩ → P/P⁺)| * |ker(Cl⁺ → Cl)| = 2`. -/
theorem card_signCorrection_ker_mul_card_narrowToClassGroup_ker_eq_two
    (hd : 0 < d) :
    Nat.card (NarrowClassGroup.signQuotientModuloNegOneToPrincipalIdealQuotient OK).ker *
        Nat.card (narrowToClassGroup d).ker = 2 := by
  rw [NarrowClassGroup.card_signCorrection_ker_mul_card_toClassGroup_ker,
    card_signQuotientModuloNegOne_eq_two d hd]

/-- For `d > 0`, the kernel of `Cl⁺(d) → Cl(d)` is either trivial or has order
`2`. -/
theorem card_narrowToClassGroup_ker_eq_one_or_eq_two_of_pos (hd : 0 < d) :
    Nat.card (narrowToClassGroup d).ker = 1 ∨
      Nat.card (narrowToClassGroup d).ker = 2 :=
  (Nat.dvd_prime Nat.prime_two).mp
    ((card_narrowToClassGroup_ker_dvd_card_signQuotientModuloNegOne d).trans
      (by rw [card_signQuotientModuloNegOne_eq_two d hd]))

end Real

namespace Imaginary

/-- If `d < 0`, then the fraction field of `𝓞(ℚ(√d))` has no real embeddings. -/
theorem isEmpty_fractionRing_realEmbeddings (hd : d < 0) :
    IsEmpty (FractionRing OK →+* ℝ) := by
  refine ⟨fun σ => ?_⟩
  letI : Algebra ℚ (Qsqrtd (d : ℚ)) := DivisionRing.toRatAlgebra
  haveI : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) :=
    { finrank_eq_two' := finrank_ratAlgebra_eq_two ((d : ℤ) : ℚ) }
  haveI : QuadraticField (Qsqrtd (d : ℚ)) :=
    { isQuadratic := inferInstance }
  haveI : NumberField (Qsqrtd (d : ℚ)) :=
    QuadraticField.instNumberField (Qsqrtd (d : ℚ))
  haveI : IsFractionRing OK (Qsqrtd (d : ℚ)) := inferInstance
  let e := IsLocalization.algEquiv OK⁰ (FractionRing OK) (Qsqrtd (d : ℚ))
  let φ : Qsqrtd (d : ℚ) →+* ℂ := Complex.ofRealHom.comp (σ.comp e.symm.toRingHom)
  haveI := isTotallyComplex d hd
  exact (NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ) (by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp [φ, NumberField.ComplexEmbedding.conjugate_coe_eq])

/-- In the imaginary quadratic case, the narrow and ordinary principal fractional
ideal subgroups coincide. -/
theorem narrowPrincipalIdeals_eq_principalIdeals (hd : d < 0) :
    NarrowClassGroup.narrowPrincipalIdeals OK (FractionRing OK) =
      (toPrincipalIdeal OK (FractionRing OK)).range := by
  letI := isEmpty_fractionRing_realEmbeddings d hd
  exact NarrowClassGroup.narrowPrincipalIdeals_eq_principalIdeals_of_isEmpty

/-- In the imaginary quadratic case, the narrow class group is naturally isomorphic
to the ordinary wide ideal class group. -/
noncomputable def narrowMulEquivClassGroup (hd : d < 0) :
    Cl⁺(d) ≃* Cl(d) := by
  letI := isEmpty_fractionRing_realEmbeddings d hd
  exact NarrowClassGroup.mulEquivClassGroupOfIsEmpty OK

/-- In the imaginary quadratic case, the narrow class group and ordinary wide ideal
class group are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup (hd : d < 0) :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  ⟨narrowMulEquivClassGroup d hd⟩

/-- In the imaginary quadratic case, the natural map from the narrow class group to
the ordinary wide class group is bijective. -/
theorem narrowToClassGroup_bijective (hd : d < 0) :
    Function.Bijective (narrowToClassGroup d) := by
  letI := isEmpty_fractionRing_realEmbeddings d hd
  exact NarrowClassGroup.toClassGroup_bijective_of_isEmpty OK

end Imaginary

/-- If the fraction field of `𝓞(ℚ(√d))` has no real embeddings, then the narrow
class group and ordinary wide class group are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup_of_isEmpty
    [IsEmpty (FractionRing OK →+* ℝ)] :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  NarrowClassGroup.nonempty_mulEquivClassGroup_of_isEmpty OK

/-- If the fraction field of `𝓞(ℚ(√d))` has no real embeddings, then the natural
map from the narrow class group to the ordinary wide class group is bijective. -/
theorem narrowToClassGroup_bijective_of_isEmpty
    [IsEmpty (FractionRing OK →+* ℝ)] :
    Function.Bijective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_bijective_of_isEmpty OK

end NarrowClassGroup

end Qsqrtd

end QuadraticNumberFields
