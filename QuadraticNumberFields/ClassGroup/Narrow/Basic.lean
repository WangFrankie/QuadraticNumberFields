/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.GroupTheory.Index
import QNFMathlib.NumberTheory.NumberField.NarrowClassGroup
import QuadraticNumberFields.ClassGroup.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.Units.Fundamental

/-!
# Narrow Class Groups of Quadratic Fields

This file specializes the basic `NarrowClassGroup` API to the standard
quadratic fields `Qsqrtd d`.

## Main statements

The real quadratic narrow-class-number dichotomy from Keune, Chapter 6,
Exercise 11, is given by `narrowClassNumber_eq_cases_fundamentalUnit`.
-/

open scoped NumberField nonZeroDivisors

namespace QuadraticNumberFields

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd`
-- calculations.
attribute [-instance] DivisionRing.toRatAlgebra

/-- Scoped notation for the narrow ideal class group of `𝓞(ℚ(√d))`. -/
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
  NumberField.narrowClassNumber (Qsqrtd (d : ℚ))

/-- View a unit of the ring of integers inside the fraction field. -/
noncomputable abbrev unitToFractionRing :
    OKˣ →* (FractionRing OK)ˣ :=
  _root_.Units.map (algebraMap OK (FractionRing OK)).toMonoidHom

/-- Forget the positivity condition and map the narrow class group to the ordinary
ideal class group. -/
noncomputable abbrev narrowToClassGroup :
    Cl⁺(d) →* Cl(d) :=
  NarrowClassGroup.toClassGroup OK

/-- The narrow class number is the ordinary class number multiplied by the
kernel size of the narrow-to-wide comparison map. -/
private theorem narrowClassNumber_eq_ker_card_mul_classNumber :
    narrowClassNumber d = Nat.card (narrowToClassGroup d).ker *
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  unfold narrowClassNumber NumberField.narrowClassNumber NarrowClassGroup.narrowClassNumber
    NumberField.classNumber
  simpa [Nat.card_eq_fintype_card] using
    MonoidHom.nat_card_eq_card_ker_mul_card_of_surjective (narrowToClassGroup d)
      (NarrowClassGroup.toClassGroup_surjective OK)

/-- If the narrow-to-wide comparison is injective, the two class numbers agree. -/
private theorem narrowClassNumber_eq_classNumber_of_narrowToClassGroup_injective
    (hinj : Function.Injective (narrowToClassGroup d)) :
    narrowClassNumber d = NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  rw [narrowClassNumber_eq_ker_card_mul_classNumber d]
  have hker : (narrowToClassGroup d).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff (narrowToClassGroup d)).mpr hinj
  rw [hker]
  simp

/-- If one real embedding sends `a` to a positive value and another sends it to
a negative value, then every real embedding is one of those two. -/
private theorem fractionRing_realEmbedding_eq_left_or_right_of_pos_neg
    (hd : 0 < d) {a : FractionRing OK} {σ τ : FractionRing OK →+* ℝ}
    (hσ_pos : 0 < σ a) (hτ_neg : τ a < 0) (ρ : FractionRing OK →+* ℝ) :
    ρ = σ ∨ ρ = τ := by
  let hdR : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  rcases Qsqrtd.fractionRing_ringHom_eq_realEmbeddingPos_or_neg d hdR σ with hσ | hσ
  · rcases Qsqrtd.fractionRing_ringHom_eq_realEmbeddingPos_or_neg d hdR τ with hτ | hτ
    · have hsame : τ a = σ a := by rw [hτ, hσ]
      linarith
    · rcases Qsqrtd.fractionRing_ringHom_eq_realEmbeddingPos_or_neg d hdR ρ with hρ | hρ
      · left
        rw [hρ, hσ]
      · right
        rw [hρ, hτ]
  · rcases Qsqrtd.fractionRing_ringHom_eq_realEmbeddingPos_or_neg d hdR τ with hτ | hτ
    · rcases Qsqrtd.fractionRing_ringHom_eq_realEmbeddingPos_or_neg d hdR ρ with hρ | hρ
      · right
        rw [hρ, hτ]
      · left
        rw [hρ, hσ]
    · have hsame : τ a = σ a := by rw [hτ, hσ]
      linarith

/-- The fraction field contains a unit whose signs at the two real embeddings
are mixed. -/
private theorem exists_mixed_sign_fractionRing_unit (hd : 0 < d) :
    ∃ α : (FractionRing OK)ˣ,
      ∃ σ τ : FractionRing OK →+* ℝ,
        0 < σ (α : FractionRing OK) ∧ τ (α : FractionRing OK) < 0 := by
  let hdR : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  let e : FractionRing OK ≃ₐ[OK] Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv OK (Qsqrtd (d : ℚ))
  let a0 : FractionRing OK := e.symm QuadraticAlgebra.omega
  have homega_ne : (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)) ≠ 0 := by
    intro hω
    have hsq := QuadraticAlgebra.omega_mul_omega_eq_add (R := ℚ) (a := (d : ℚ)) (b := 0)
    rw [hω] at hsq
    have hdQ : (d : ℚ) = 0 := by
      simpa [Algebra.smul_def] using hsq.symm
    have hd0 : d = 0 := by exact_mod_cast hdQ
    omega
  have ha0 : a0 ≠ 0 := by
    intro ha
    exact homega_ne (by simpa [a0] using congrArg e ha)
  let α : (FractionRing OK)ˣ := Units.mk0 a0 ha0
  let σ : FractionRing OK →+* ℝ := (Qsqrtd.realEmbeddingPos d hdR).toRingHom.comp e.toRingHom
  let τ : FractionRing OK →+* ℝ := (Qsqrtd.realEmbeddingNeg d hdR).toRingHom.comp e.toRingHom
  refine ⟨α, σ, τ, ?_, ?_⟩
  · have hsqrt : 0 < Real.sqrt (d : ℝ) := by positivity
    simpa [α, σ, a0, e, Qsqrtd.realEmbeddingPos_apply] using hsqrt
  · have hsqrt : 0 < Real.sqrt (d : ℝ) := by positivity
    have hneg : -Real.sqrt (d : ℝ) < 0 := neg_neg_of_pos hsqrt
    simpa [α, τ, a0, e, Qsqrtd.realEmbeddingNeg_apply] using hneg

/-- A mixed-sign integral unit lets every fraction-field unit be adjusted to a
totally positive generator. -/
private theorem forall_exists_unit_mul_isTotallyPositive_of_mixed_sign_unit
    (hd : 0 < d) (ε : OKˣ)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK))
    (hε_tp : ¬ NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    ∀ x : (FractionRing OK)ˣ, ∃ u : OKˣ,
      NarrowClassGroup.IsTotallyPositive
        (((x * NarrowClassGroup.ringUnitToFractionRing OK (FractionRing OK) u :
          (FractionRing OK)ˣ)) : FractionRing OK) := by
  classical
  let εF : (FractionRing OK)ˣ := unitToFractionRing d ε
  obtain ⟨σ, hσ_pos⟩ := hε_pos
  have hnot : ∃ τ : FractionRing OK →+* ℝ, ¬ 0 < τ (εF : FractionRing OK) := by
    simpa [εF, NarrowClassGroup.IsTotallyPositive] using not_forall.mp hε_tp
  obtain ⟨τ, hτ_not_pos⟩ := hnot
  have hτ_ne : τ (εF : FractionRing OK) ≠ 0 :=
    (_root_.map_ne_zero τ).mpr (Units.ne_zero εF)
  have hτ_neg : τ (εF : FractionRing OK) < 0 :=
    lt_of_le_of_ne (not_lt.mp hτ_not_pos) hτ_ne
  intro x
  have hσx_ne : σ (x : FractionRing OK) ≠ 0 :=
    (_root_.map_ne_zero σ).mpr (Units.ne_zero x)
  have hτx_ne : τ (x : FractionRing OK) ≠ 0 :=
    (_root_.map_ne_zero τ).mpr (Units.ne_zero x)
  rcases lt_or_gt_of_ne hσx_ne with hσx_neg | hσx_pos
  · rcases lt_or_gt_of_ne hτx_ne with hτx_neg | hτx_pos
    · refine ⟨-1, ?_⟩
      intro ρ
      rcases fractionRing_realEmbedding_eq_left_or_right_of_pos_neg d hd hσ_pos hτ_neg ρ
        with hρ | hρ
      · rw [hρ]
        simpa [NarrowClassGroup.ringUnitToFractionRing] using neg_pos.mpr hσx_neg
      · rw [hρ]
        simpa [NarrowClassGroup.ringUnitToFractionRing] using neg_pos.mpr hτx_neg
    · refine ⟨-ε, ?_⟩
      intro ρ
      rcases fractionRing_realEmbedding_eq_left_or_right_of_pos_neg d hd hσ_pos hτ_neg ρ
        with hρ | hρ
      · rw [hρ]
        have hεσneg :
            σ ((unitToFractionRing d (-ε) : (FractionRing OK)ˣ) : FractionRing OK) < 0 := by
          simpa [unitToFractionRing, NarrowClassGroup.ringUnitToFractionRing] using
            neg_neg_of_pos hσ_pos
        have := mul_pos_of_neg_of_neg hσx_neg hεσneg
        simpa [unitToFractionRing, NarrowClassGroup.ringUnitToFractionRing, mul_comm,
          mul_left_comm, mul_assoc] using this
      · rw [hρ]
        have hετpos :
            0 < τ ((unitToFractionRing d (-ε) : (FractionRing OK)ˣ) : FractionRing OK) := by
          simpa [unitToFractionRing, NarrowClassGroup.ringUnitToFractionRing] using
            neg_pos.mpr hτ_neg
        have := mul_pos hτx_pos hετpos
        simpa [unitToFractionRing, NarrowClassGroup.ringUnitToFractionRing, mul_comm,
          mul_left_comm, mul_assoc] using this
  · rcases lt_or_gt_of_ne hτx_ne with hτx_neg | hτx_pos
    · refine ⟨ε, ?_⟩
      intro ρ
      rcases fractionRing_realEmbedding_eq_left_or_right_of_pos_neg d hd hσ_pos hτ_neg ρ
        with hρ | hρ
      · rw [hρ]
        have := mul_pos hσx_pos hσ_pos
        simpa [εF, unitToFractionRing, NarrowClassGroup.ringUnitToFractionRing, mul_comm,
          mul_left_comm, mul_assoc] using this
      · rw [hρ]
        have := mul_pos_of_neg_of_neg hτx_neg hτ_neg
        simpa [εF, unitToFractionRing, NarrowClassGroup.ringUnitToFractionRing, mul_comm,
          mul_left_comm, mul_assoc] using this
    · refine ⟨1, ?_⟩
      intro ρ
      rcases fractionRing_realEmbedding_eq_left_or_right_of_pos_neg d hd hσ_pos hτ_neg ρ
        with hρ | hρ
      · rw [hρ]
        simpa [NarrowClassGroup.ringUnitToFractionRing] using hσx_pos
      · rw [hρ]
        simpa [NarrowClassGroup.ringUnitToFractionRing] using hτx_pos

/-- If a fundamental integral unit is totally positive, every integral unit is
totally positive up to multiplication by the global sign `-1`. -/
private theorem ringUnit_isTotallyPositive_or_neg_of_fundamentalUnit_isTotallyPositive
    (ε v : OKˣ) (hε : Units.IsFundamentalUnit ε)
    (hε_tp : NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    NarrowClassGroup.IsTotallyPositive
        ((unitToFractionRing d v : (FractionRing OK)ˣ) : FractionRing OK) ∨
      NarrowClassGroup.IsTotallyPositive
        ((unitToFractionRing d (-v) : (FractionRing OK)ˣ) : FractionRing OK) := by
  obtain ⟨n, hv | hv⟩ := hε v
  · left
    rw [hv]
    simpa [map_zpow] using
      NarrowClassGroup.isTotallyPositive_zpow (unitToFractionRing d ε) hε_tp n
  · right
    rw [hv]
    simpa [map_zpow] using
      NarrowClassGroup.isTotallyPositive_zpow (unitToFractionRing d ε) hε_tp n

/-! ### Keune, Chapter 6, Exercise 11 -/

/-- If a fundamental unit is totally positive, the kernel of the comparison
`Cl⁺(d) → Cl(d)` has order two. -/
theorem card_narrowToClassGroup_ker_eq_two_of_isTotallyPositive_fundamentalUnit
    (hd : 0 < d) (ε : OKˣ)
    (hε : Units.IsFundamentalUnit ε)
    (hε_tp : NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    Nat.card (narrowToClassGroup d).ker = 2 := by
  have hker_range :
      (narrowToClassGroup d).ker = (NarrowClassGroup.principalToNarrow OK).range :=
    NarrowClassGroup.toClassGroup_ker_eq_principalToNarrow_range OK
  have hker_card : Nat.card (narrowToClassGroup d).ker = 2 := by
    rw [hker_range]
    have hunit_sign :
        ∀ v : OKˣ,
          NarrowClassGroup.IsTotallyPositive
              ((unitToFractionRing d v : (FractionRing OK)ˣ) : FractionRing OK) ∨
            NarrowClassGroup.IsTotallyPositive
              ((unitToFractionRing d (-v) : (FractionRing OK)ˣ) : FractionRing OK) :=
      fun v =>
        ringUnit_isTotallyPositive_or_neg_of_fundamentalUnit_isTotallyPositive
          d ε v hε hε_tp
    obtain ⟨α, σ, τ, hασ_pos, hατ_neg⟩ := exists_mixed_sign_fractionRing_unit d hd
    have hα_ne_one : NarrowClassGroup.principalToNarrow OK α ≠ 1 := by
      intro hα
      obtain ⟨u, hαu_pos⟩ :=
        (NarrowClassGroup.principalToNarrow_eq_one_iff_exists_unit_mul_isTotallyPositive α).mp hα
      rcases hunit_sign u with hu_pos | hneg_u_pos
      · have hprod_neg :
            τ (((α * NarrowClassGroup.ringUnitToFractionRing OK (FractionRing OK) u :
              (FractionRing OK)ˣ)) : FractionRing OK) < 0 := by
          have huτ_pos :
              0 < τ (((NarrowClassGroup.ringUnitToFractionRing OK (FractionRing OK) u :
                (FractionRing OK)ˣ)) : FractionRing OK) := by
            simpa [unitToFractionRing, NarrowClassGroup.ringUnitToFractionRing] using hu_pos τ
          simpa [map_mul] using mul_neg_of_neg_of_pos hατ_neg huτ_pos
        exact (not_lt_of_gt hprod_neg) (hαu_pos τ)
      · have hprod_neg :
            σ (((α * NarrowClassGroup.ringUnitToFractionRing OK (FractionRing OK) u :
              (FractionRing OK)ˣ)) : FractionRing OK) < 0 := by
          have hnegσ_pos :
              0 < σ ((unitToFractionRing d (-u) : (FractionRing OK)ˣ) : FractionRing OK) :=
            hneg_u_pos σ
          have huσ_neg :
              σ (((NarrowClassGroup.ringUnitToFractionRing OK (FractionRing OK) u :
                (FractionRing OK)ˣ)) : FractionRing OK) < 0 := by
            have hneg :
                0 < -σ (((NarrowClassGroup.ringUnitToFractionRing OK (FractionRing OK) u :
                  (FractionRing OK)ˣ)) : FractionRing OK) := by
              simpa [unitToFractionRing, NarrowClassGroup.ringUnitToFractionRing] using hnegσ_pos
            exact neg_pos.mp hneg
          simpa [map_mul] using mul_neg_of_pos_of_neg hασ_pos huσ_neg
        exact (not_lt_of_gt hprod_neg) (hαu_pos σ)
    let A : (NarrowClassGroup.principalToNarrow OK).range :=
      ⟨NarrowClassGroup.principalToNarrow OK α, ⟨α, rfl⟩⟩
    have hA_ne_one : (1 : (NarrowClassGroup.principalToNarrow OK).range) ≠ A := by
      intro hA
      exact hα_ne_one (congrArg Subtype.val hA).symm
    have hrange : ∀ C : (NarrowClassGroup.principalToNarrow OK).range, C = 1 ∨ C = A := by
      rintro ⟨_, x, rfl⟩
      have hσx_ne : σ (x : FractionRing OK) ≠ 0 :=
        (_root_.map_ne_zero σ).mpr (Units.ne_zero x)
      have hτx_ne : τ (x : FractionRing OK) ≠ 0 :=
        (_root_.map_ne_zero τ).mpr (Units.ne_zero x)
      rcases lt_or_gt_of_ne hσx_ne with hσx_neg | hσx_pos
      · rcases lt_or_gt_of_ne hτx_ne with hτx_neg | hτx_pos
        · have hx_one : NarrowClassGroup.principalToNarrow OK x = 1 :=
            (NarrowClassGroup.principalToNarrow_eq_one_iff_exists_unit_mul_isTotallyPositive x).mpr
              ⟨-1, by
                intro ρ
                rcases fractionRing_realEmbedding_eq_left_or_right_of_pos_neg
                    d hd hασ_pos hατ_neg ρ with hρ | hρ
                · rw [hρ]
                  simpa [NarrowClassGroup.ringUnitToFractionRing] using
                    neg_pos.mpr hσx_neg
                · rw [hρ]
                  simpa [NarrowClassGroup.ringUnitToFractionRing] using
                    neg_pos.mpr hτx_neg⟩
          left
          exact Subtype.ext hx_one
        · have hx_div_one : NarrowClassGroup.principalToNarrow OK (x / α) = 1 :=
            (NarrowClassGroup.principalToNarrow_eq_one_iff_exists_unit_mul_isTotallyPositive
              (x / α)).mpr
              ⟨-1, by
                intro ρ
                rcases fractionRing_realEmbedding_eq_left_or_right_of_pos_neg
                    d hd hασ_pos hατ_neg ρ with hρ | hρ
                · rw [hρ]
                  have hxα_neg : σ ((x / α : (FractionRing OK)ˣ) : FractionRing OK) < 0 := by
                    simpa using div_neg_of_neg_of_pos hσx_neg hασ_pos
                  simpa [NarrowClassGroup.ringUnitToFractionRing] using
                    neg_pos.mpr hxα_neg
                · rw [hρ]
                  have hxα_neg : τ ((x / α : (FractionRing OK)ˣ) : FractionRing OK) < 0 := by
                    simpa using div_neg_of_pos_of_neg hτx_pos hατ_neg
                  simpa [NarrowClassGroup.ringUnitToFractionRing] using
                    neg_pos.mpr hxα_neg⟩
          rw [map_div] at hx_div_one
          right
          exact Subtype.ext (div_eq_one.mp hx_div_one)
      · rcases lt_or_gt_of_ne hτx_ne with hτx_neg | hτx_pos
        · have hx_div_one : NarrowClassGroup.principalToNarrow OK (x / α) = 1 :=
            (NarrowClassGroup.principalToNarrow_eq_one_iff_exists_unit_mul_isTotallyPositive
              (x / α)).mpr
              ⟨1, by
                intro ρ
                rcases fractionRing_realEmbedding_eq_left_or_right_of_pos_neg
                    d hd hασ_pos hατ_neg ρ with hρ | hρ
                · rw [hρ]
                  simpa [NarrowClassGroup.ringUnitToFractionRing] using
                    div_pos hσx_pos hασ_pos
                · rw [hρ]
                  simpa [NarrowClassGroup.ringUnitToFractionRing] using
                    div_pos_of_neg_of_neg hτx_neg hατ_neg⟩
          rw [map_div] at hx_div_one
          right
          exact Subtype.ext (div_eq_one.mp hx_div_one)
        · have hx_one : NarrowClassGroup.principalToNarrow OK x = 1 :=
            (NarrowClassGroup.principalToNarrow_eq_one_iff_exists_unit_mul_isTotallyPositive x).mpr
              ⟨1, by
                intro ρ
                rcases fractionRing_realEmbedding_eq_left_or_right_of_pos_neg
                    d hd hασ_pos hατ_neg ρ with hρ | hρ
                · rw [hρ]
                  simpa [NarrowClassGroup.ringUnitToFractionRing] using hσx_pos
                · rw [hρ]
                  simpa [NarrowClassGroup.ringUnitToFractionRing] using hτx_pos⟩
          left
          exact Subtype.ext hx_one
    rw [Nat.card_eq_two_iff]
    refine ⟨1, A, hA_ne_one, ?_⟩
    ext C
    constructor
    · intro _hC
      trivial
    · intro _hC
      rcases hrange C with hC | hC
      · left
        exact hC
      · right
        exact hC
  exact hker_card

/-- Keune Ch6 Ex. 11: the narrow class number is twice the ordinary class
number when a fundamental unit is totally positive. -/
theorem narrowClassNumber_eq_two_mul_classNumber_of_isTotallyPositive_fundamentalUnit
    (hd : 0 < d) (ε : OKˣ)
    (hε : Units.IsFundamentalUnit ε)
    (hε_tp : NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    narrowClassNumber d = 2 * NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  rw [narrowClassNumber_eq_ker_card_mul_classNumber d,
    card_narrowToClassGroup_ker_eq_two_of_isTotallyPositive_fundamentalUnit
      d hd ε hε hε_tp]

/-- A mixed-sign integral unit makes the comparison `Cl⁺(d) → Cl(d)`
injective. -/
theorem narrowToClassGroup_injective_of_mixed_sign_unit
    (hd : 0 < d) (ε : OKˣ)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK))
    (hε_tp : ¬ NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    Function.Injective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_injective_of_forall_exists_unit_mul_isTotallyPositive
    (forall_exists_unit_mul_isTotallyPositive_of_mixed_sign_unit
      d hd ε hε_pos hε_tp)

/-- A mixed-sign integral unit makes the comparison kernel trivial. -/
theorem card_narrowToClassGroup_ker_eq_one_of_mixed_sign_unit
    (hd : 0 < d) (ε : OKˣ)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK))
    (hε_tp : ¬ NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    Nat.card (narrowToClassGroup d).ker = 1 := by
  rw [Subgroup.card_eq_one, MonoidHom.ker_eq_bot_iff]
  exact narrowToClassGroup_injective_of_mixed_sign_unit d hd ε hε_pos hε_tp

/-- The narrow class number equals the ordinary class number when an integral
unit has mixed signs at the real embeddings. -/
theorem narrowClassNumber_eq_classNumber_of_mixed_sign_unit
    (hd : 0 < d) (ε : OKˣ)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK))
    (hε_tp : ¬ NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    narrowClassNumber d = NumberField.classNumber (Qsqrtd (d : ℚ)) :=
  narrowClassNumber_eq_classNumber_of_narrowToClassGroup_injective d
    (narrowToClassGroup_injective_of_mixed_sign_unit d hd ε hε_pos hε_tp)

/-- Keune Ch6 Ex. 11, with the two class-number cases bundled together. -/
theorem narrowClassNumber_eq_cases_fundamentalUnit
    (hd : 0 < d) (ε : OKˣ)
    (hε : Units.IsFundamentalUnit ε)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    (NarrowClassGroup.IsTotallyPositive
        ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK) →
      narrowClassNumber d = 2 * NumberField.classNumber (Qsqrtd (d : ℚ))) ∧
    (¬ NarrowClassGroup.IsTotallyPositive
        ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK) →
      narrowClassNumber d = NumberField.classNumber (Qsqrtd (d : ℚ))) := by
  constructor
  · exact narrowClassNumber_eq_two_mul_classNumber_of_isTotallyPositive_fundamentalUnit
      d hd ε hε
  · exact narrowClassNumber_eq_classNumber_of_mixed_sign_unit d hd ε hε_pos

/-- If every unit of the fraction field is totally positive, the narrow and
ordinary class groups are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup_of_forall_isTotallyPositive
    (hpos : ∀ x : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing OK)) :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  NarrowClassGroup.nonempty_mulEquivClassGroup_of_forall_isTotallyPositive OK hpos

/-- If every unit of the fraction field is totally positive, then
`narrowToClassGroup` is bijective. -/
theorem narrowToClassGroup_bijective_of_forall_isTotallyPositive
    (hpos : ∀ x : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing OK)) :
    Function.Bijective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_bijective_of_forall_isTotallyPositive OK hpos

namespace Imaginary

/-- If `d < 0`, the fraction field of `𝓞(ℚ(√d))` has no real embeddings. -/
theorem isEmpty_fractionRing_realEmbeddings (hd : d < 0) :
    IsEmpty (FractionRing OK →+* ℝ) := by
  haveI := isTotallyComplex d hd
  exact NumberField.isEmpty_fractionRing_realEmbeddings_of_isTotallyComplex (Qsqrtd (d : ℚ))

/-- For imaginary quadratic fields, the narrow and ordinary principal fractional
ideal subgroups coincide. -/
theorem narrowPrincipalIdeals_eq_principalIdeals (hd : d < 0) :
    NarrowClassGroup.narrowPrincipalIdeals OK (FractionRing OK) =
      (toPrincipalIdeal OK (FractionRing OK)).range := by
  haveI := isTotallyComplex d hd
  exact
    NumberField.narrowPrincipalIdeals_eq_principalIdeals_of_isTotallyComplex
      (Qsqrtd (d : ℚ))

/-- For imaginary quadratic fields, the narrow class group is isomorphic to the
ordinary ideal class group. -/
noncomputable def narrowMulEquivClassGroup (hd : d < 0) :
    Cl⁺(d) ≃* Cl(d) := by
  haveI := isTotallyComplex d hd
  exact NumberField.narrowMulEquivClassGroupOfIsTotallyComplex (Qsqrtd (d : ℚ))

/-- Nonempty form of `narrowMulEquivClassGroup`. -/
theorem nonempty_narrowMulEquivClassGroup (hd : d < 0) :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  ⟨narrowMulEquivClassGroup d hd⟩

/-- For imaginary quadratic fields, `narrowToClassGroup` is bijective. -/
theorem narrowToClassGroup_bijective (hd : d < 0) :
    Function.Bijective (narrowToClassGroup d) := by
  haveI := isTotallyComplex d hd
  exact NumberField.narrowToClassGroup_bijective_of_isTotallyComplex (Qsqrtd (d : ℚ))

end Imaginary

/-- If the fraction field has no real embeddings, the narrow and ordinary class
groups are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup_of_isEmpty
    [IsEmpty (FractionRing OK →+* ℝ)] :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  NarrowClassGroup.nonempty_mulEquivClassGroup_of_isEmpty OK

/-- If the fraction field has no real embeddings, then `narrowToClassGroup` is
bijective. -/
theorem narrowToClassGroup_bijective_of_isEmpty
    [IsEmpty (FractionRing OK →+* ℝ)] :
    Function.Bijective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_bijective_of_isEmpty OK

end NarrowClassGroup

end Qsqrtd

end QuadraticNumberFields
