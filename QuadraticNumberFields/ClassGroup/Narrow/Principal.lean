/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.QuadraticField.Conj
import QuadraticNumberFields.RingOfIntegers.Norm

/-!
# Principal Narrow Class Group Results for Quadratic Fields

This file specializes the positive-principal exact sequence to `𝓞(ℚ(√d))`.
-/

open scoped NumberField nonZeroDivisors

-- Use the canonical `QuadraticAlgebra` algebra structure on standard `Qsqrtd`
-- models in the real-positive Hilbert 90 wrapper.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields

namespace Qsqrtd

open _root_.Qsqrtd

open scoped QuadraticNumberFields.ClassGroup

section PositivePrincipal

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞 (Qsqrtd (d : ℚ))

/-- The totally positive unit subgroup `𝓞(ℚ(√d))ˣ⁺`. -/
noncomputable abbrev positiveUnits : Subgroup OKˣ :=
  NarrowClassGroup.totallyPositiveRingUnits OK (FractionRing OK)

/-- The inclusion `𝓞(ℚ(√d))ˣ⁺ → (Frac 𝓞(ℚ(√d)))ˣ⁺`. -/
noncomputable abbrev positiveUnitsToFractionRing :
    positiveUnits d →* NarrowClassGroup.totallyPositiveUnits (FractionRing OK) :=
  NarrowClassGroup.totallyPositiveRingUnitsToField OK (FractionRing OK)

/-- The positive principal fractional ideals `P_K⁺` for `K = ℚ(√d)`. -/
noncomputable abbrev positivePrincipalIdeals :
    Subgroup ((FractionalIdeal OK⁰ (FractionRing OK))ˣ) :=
  NarrowClassGroup.narrowPrincipalIdeals OK (FractionRing OK)

/-- The map `(Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺`. -/
noncomputable abbrev toPositivePrincipalIdeals :
    NarrowClassGroup.totallyPositiveUnits (FractionRing OK) →* positivePrincipalIdeals d :=
  NarrowClassGroup.toPositivePrincipalIdeals OK (FractionRing OK)

/-- The map `(Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺` is surjective. -/
theorem toPositivePrincipalIdeals_surjective :
    Function.Surjective (toPositivePrincipalIdeals d) :=
  NarrowClassGroup.toPositivePrincipalIdeals_surjective OK (FractionRing OK)

/-- Exactness at `(Frac 𝓞(ℚ(√d)))ˣ⁺` in
`1 → 𝓞(ℚ(√d))ˣ⁺ → (Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺ → 1`. -/
theorem positiveUnitsToFractionRing_mulExact_toPositivePrincipalIdeals :
    Function.MulExact (positiveUnitsToFractionRing d) (toPositivePrincipalIdeals d) :=
  NarrowClassGroup.totallyPositiveRingUnitsToField_mulExact_toPositivePrincipalIdeals
    OK (FractionRing OK)

/-- Principal-layer positive Hilbert 90 for `𝓞(ℚ(√d))`.

If a totally positive fraction-field unit is norm-one for an involution `τ`, then its
positive principal ideal is a positive principal coboundary. This is the concrete
`H¹(G, P_K⁺) = 1` interface used by the strict principal layer. -/
theorem toPositivePrincipalIdeals_coboundary_of_mul_apply_eq_one
    [Nonempty (FractionRing OK →+* ℝ)] (τ : FractionRing OK ≃+* FractionRing OK)
    (hτpos : ∀ x : FractionRing OK,
      NarrowClassGroup.IsTotallyPositive x → NarrowClassGroup.IsTotallyPositive (τ x))
    {a : NarrowClassGroup.totallyPositiveUnits (FractionRing OK)}
    (ha_norm : (a : (FractionRing OK)ˣ) *
      Units.map τ.toMonoidHom (a : (FractionRing OK)ˣ) = 1) :
    ∃ b : NarrowClassGroup.totallyPositiveUnits (FractionRing OK),
      toPositivePrincipalIdeals d a =
        toPositivePrincipalIdeals d b /
          toPositivePrincipalIdeals d
            ⟨Units.map τ.toMonoidHom (b : (FractionRing OK)ˣ),
              hτpos (((b : (FractionRing OK)ˣ) : FractionRing OK)) b.2⟩ :=
  NarrowClassGroup.toPositivePrincipalIdeals_coboundary_of_mul_apply_eq_one
    OK (FractionRing OK) τ hτpos ha_norm

end PositivePrincipal

namespace Real

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "OK" => 𝓞 K

/-- A nonzero element of a real quadratic field with positive norm is either
totally positive or totally negative. In the latter case, its negative is
totally positive. -/
theorem isTotallyPositive_or_neg_isTotallyPositive_of_norm_pos
    (hd : 0 < d)
    {γ : (FractionRing OK)ˣ}
    (hNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv OK K (γ : FractionRing OK)) : ℝ)) :
    NarrowClassGroup.IsTotallyPositive (γ : FractionRing OK) ∨
      NarrowClassGroup.IsTotallyPositive
        ((-γ : (FractionRing OK)ˣ) : FractionRing OK) := by
  let e : FractionRing OK ≃ₐ[OK] K := FractionRing.algEquiv OK K
  let z : K := e (γ : FractionRing OK)
  have hdR : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  have hprod :
      0 < Qsqrtd.realEmbeddingPos d hdR z *
        Qsqrtd.realEmbeddingNeg d hdR z := by
    simpa [z, e] using
      (by rwa [← Qsqrtd.norm_eq_realEmbeddingPos_mul_realEmbeddingNeg d hdR z])
  rcases mul_pos_iff.mp hprod with hsign | hsign
  · left
    intro σ
    rcases Qsqrtd.fractionRing_ringHom_eq_realEmbeddingPos_or_neg d hdR σ with hσ | hσ
    · rw [hσ]
      simpa [z, e, RingHom.comp_apply] using hsign.1
    · rw [hσ]
      simpa [z, e, RingHom.comp_apply] using hsign.2
  · right
    intro σ
    rcases Qsqrtd.fractionRing_ringHom_eq_realEmbeddingPos_or_neg d hdR σ with hσ | hσ
    · rw [hσ]
      simpa [z, e, RingHom.comp_apply] using neg_pos.mpr hsign.1
    · rw [hσ]
      simpa [z, e, RingHom.comp_apply] using neg_pos.mpr hsign.2

/-- A nonzero algebraic integer of positive algebra norm is totally positive
up to multiplication by `-1`. -/
theorem isTotallyPositive_algebraMap_or_neg_of_algebraNorm_pos
    (hd : 0 < d) {α : OK} (hNormPos : 0 < Algebra.norm ℤ α) :
    NarrowClassGroup.IsTotallyPositive (algebraMap OK (FractionRing OK) α) ∨
      NarrowClassGroup.IsTotallyPositive
        (algebraMap OK (FractionRing OK) (-α)) := by
  have hα : α ≠ 0 := Algebra.norm_ne_zero_iff.mp hNormPos.ne'
  have hαF : algebraMap OK (FractionRing OK) α ≠ 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff OK (FractionRing OK)).not.mpr hα
  let γ : (FractionRing OK)ˣ :=
    Units.mk0 (algebraMap OK (FractionRing OK) α) hαF
  have hcompare :
      Qsqrtd.norm (FractionRing.algEquiv OK K (γ : FractionRing OK)) =
        (Algebra.norm ℤ α : ℚ) := by
    have he :
        FractionRing.algEquiv OK K (γ : FractionRing OK) =
          algebraMap OK K α := by
      simp [γ]
    rw [he, ← Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm,
      ← Algebra.coe_norm_int α]
  have hNormPosQ :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv OK K (γ : FractionRing OK)) : ℝ) := by
    rw [hcompare]
    exact_mod_cast hNormPos
  rcases isTotallyPositive_or_neg_isTotallyPositive_of_norm_pos d hd hNormPosQ with
    hγ | hnegγ
  · left
    simpa [γ] using hγ
  · right
    simpa [γ] using hnegγ

/-- The algebra norm of an integral unit in a quadratic field is `1` or `-1`. -/
theorem unit_algebraNorm_eq_one_or_neg_one (ε : OKˣ) :
    Algebra.norm ℤ (ε : OK) = 1 ∨ Algebra.norm ℤ (ε : OK) = -1 := by
  have hunit : IsUnit (Algebra.norm ℤ (ε : OK)) :=
    (Units.map (Algebra.norm ℤ : OK →* ℤ) ε).isUnit
  simpa using (Int.isUnit_iff.mp hunit)

/-- The quadratic norm of an integral unit agrees with its algebra norm after
passing to the fraction field. -/
theorem norm_unitToFractionRing_eq_algebraNorm (ε : OKˣ) :
    Qsqrtd.norm
        (FractionRing.algEquiv OK K
          ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) =
      (Algebra.norm ℤ (ε : OK) : ℚ) := by
  have he :
      FractionRing.algEquiv OK K
          ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK) =
        algebraMap OK K (ε : OK) := by
    simp [unitToFractionRing]
  rw [he, ← Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm,
    ← Algebra.coe_norm_int (ε : OK)]

/-- A norm-`-1` integral unit is positive at one of the two real embeddings. -/
theorem exists_pos_embedding_of_unit_algebraNorm_eq_neg_one
    (hd : 0 < d) (ε : OKˣ) (hε_norm : Algebra.norm ℤ (ε : OK) = -1) :
    ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK) := by
  let e : FractionRing OK ≃ₐ[OK] K := FractionRing.algEquiv OK K
  let z : K := e ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)
  have hdR : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  have hnorm : (Qsqrtd.norm z : ℝ) = -1 := by
    exact_mod_cast (norm_unitToFractionRing_eq_algebraNorm d ε).trans (by
      simp [hε_norm])
  have hprod :
      Qsqrtd.realEmbeddingPos d hdR z * Qsqrtd.realEmbeddingNeg d hdR z < 0 := by
    rw [← Qsqrtd.norm_eq_realEmbeddingPos_mul_realEmbeddingNeg d hdR z, hnorm]
    norm_num
  rcases mul_neg_iff.mp hprod with hsign | hsign
  · exact ⟨(Qsqrtd.realEmbeddingPos d hdR).toRingHom.comp e.toRingHom, by
      simpa [z, e, RingHom.comp_apply] using hsign.1⟩
  · exact ⟨(Qsqrtd.realEmbeddingNeg d hdR).toRingHom.comp e.toRingHom, by
      simpa [z, e, RingHom.comp_apply] using hsign.2⟩

/-- After normalizing an integral unit to be positive at one real embedding,
it is totally positive exactly when its algebra norm is `1`. -/
theorem isTotallyPositive_unit_iff_algebraNorm_eq_one
    (hd : 0 < d) (ε : OKˣ)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    NarrowClassGroup.IsTotallyPositive
          ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK) ↔
      Algebra.norm ℤ (ε : OK) = 1 := by
  let εF : (FractionRing OK)ˣ := unitToFractionRing d ε
  have hcompare :
      Qsqrtd.norm (FractionRing.algEquiv OK K (εF : FractionRing OK)) =
        (Algebra.norm ℤ (ε : OK) : ℚ) := by
    simpa [εF] using norm_unitToFractionRing_eq_algebraNorm d ε
  constructor
  · intro hε_tp
    rcases unit_algebraNorm_eq_one_or_neg_one d ε with hnorm | hnorm
    · exact hnorm
    · exfalso
      have hdR : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
      let e : FractionRing OK ≃ₐ[OK] K := FractionRing.algEquiv OK K
      let z : K := e (εF : FractionRing OK)
      have he : z = algebraMap OK K (ε : OK) := by
        simp [z, e, εF, unitToFractionRing]
      have hpos : 0 < (Qsqrtd.norm z : ℝ) := by
        apply Qsqrtd.norm_pos_of_realEmbedding_pos d hdR
        · simpa [he, RingHom.comp_apply] using
            hε_tp ((Qsqrtd.realEmbeddingPos d hdR).toRingHom.comp e.toRingHom)
        · simpa [he, RingHom.comp_apply] using
            hε_tp ((Qsqrtd.realEmbeddingNeg d hdR).toRingHom.comp e.toRingHom)
      have hneg : (Qsqrtd.norm z : ℝ) = -1 := by
        exact_mod_cast hcompare.trans (by simp [hnorm])
      linarith
  · intro hnorm_one
    have hNormPos :
        0 <
          (Qsqrtd.norm
            (FractionRing.algEquiv OK K (εF : FractionRing OK)) : ℝ) := by
      rw [hcompare, hnorm_one]
      norm_num
    rcases isTotallyPositive_or_neg_isTotallyPositive_of_norm_pos d hd hNormPos with
      hε_tp | hnegε_tp
    · exact hε_tp
    · obtain ⟨σ, hσpos⟩ := hε_pos
      have hσneg := hnegε_tp σ
      have : σ ((-εF : (FractionRing OK)ˣ) : FractionRing OK) =
          -σ (εF : FractionRing OK) := by simp
      rw [this] at hσneg
      linarith

/-- A norm-`-1` integral unit makes the narrow-to-wide comparison bijective. -/
theorem narrowToClassGroup_bijective_of_unit_algebraNorm_eq_neg_one
    (hd : 0 < d) (ε : OKˣ)
    (hε_norm : Algebra.norm ℤ (ε : OK) = -1) :
    Function.Bijective (narrowToClassGroup d) := by
  have hε_pos :=
    exists_pos_embedding_of_unit_algebraNorm_eq_neg_one d hd ε hε_norm
  have hε_not_tp : ¬ NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK) := by
    rw [isTotallyPositive_unit_iff_algebraNorm_eq_one d hd ε hε_pos]
    omega
  exact ⟨narrowToClassGroup_injective_of_mixed_sign_unit
      d hd ε hε_pos hε_not_tp,
    NarrowClassGroup.toClassGroup_surjective OK⟩

/-- A norm-`-1` integral unit makes the narrow-to-wide comparison kernel
trivial. -/
theorem card_narrowToClassGroup_ker_eq_one_of_unit_algebraNorm_eq_neg_one
    (hd : 0 < d) (ε : OKˣ)
    (hε_norm : Algebra.norm ℤ (ε : OK) = -1) :
    Nat.card (narrowToClassGroup d).ker = 1 := by
  rw [Subgroup.card_eq_one, MonoidHom.ker_eq_bot_iff]
  exact (narrowToClassGroup_bijective_of_unit_algebraNorm_eq_neg_one
    d hd ε hε_norm).1

/-- A norm-`1` fundamental unit makes the narrow-to-wide comparison kernel
have order two. -/
theorem card_narrowToClassGroup_ker_eq_two_of_fundamentalUnit_algebraNorm_eq_one
    (hd : 0 < d) (ε : OKˣ)
    (hε : Units.IsFundamentalUnit ε)
    (hε_norm : Algebra.norm ℤ (ε : OK) = 1) :
    Nat.card (narrowToClassGroup d).ker = 2 := by
  have hnorm_pos : 0 < Algebra.norm ℤ (ε : OK) := by omega
  rcases isTotallyPositive_algebraMap_or_neg_of_algebraNorm_pos d hd hnorm_pos with
    hε_tp | hnegε_tp
  · exact card_narrowToClassGroup_ker_eq_two_of_isTotallyPositive_fundamentalUnit
      d hd ε hε (by simpa [unitToFractionRing] using hε_tp)
  · exact card_narrowToClassGroup_ker_eq_two_of_isTotallyPositive_fundamentalUnit
      d hd (-ε) hε.neg (by simpa [unitToFractionRing] using hnegε_tp)

/-- Fixed totally positive ring units in a real quadratic standard model are trivial.

This is the concrete fixed-unit form of the `H²(<σ>, (O_Lˣ)⁺) = 1` input in
Emerton's item 10. If a totally positive unit of `𝓞(ℚ(√d))` is fixed by
conjugation, then it is the positive rational algebraic-integer unit `1`. -/
theorem fixed_totallyPositiveRingUnit_eq_one (hd : 0 < d)
    {u : OKˣ}
    (hu_pos : NarrowClassGroup.IsTotallyPositive (((u : OKˣ) : OK) : K))
    (hfix : star (((u : OKˣ) : OK) : K) = (((u : OKˣ) : OK) : K)) :
    u = 1 := by
  have hdR : 0 ≤ (d : ℝ) := by
    exact_mod_cast le_of_lt hd
  have hq_pos : 0 < ((((u : OKˣ) : OK) : K).re) :=
    re_pos_of_forall_algHom_pos_of_star_self d hdR
      ((NarrowClassGroup.isTotallyPositive_iff_forall_ratAlgHom
        (((u : OKˣ) : OK) : K)).mp hu_pos)
      hfix
  exact ringOfIntegers_unit_eq_one_of_star_self_of_re_pos (d := d) hfix hq_pos

/-- Subgroup version of `fixed_totallyPositiveRingUnit_eq_one`.

This states the same fixed-unit triviality directly for the group
`(𝓞(ℚ(√d))ˣ)⁺`. -/
theorem fixed_totallyPositiveRingUnits_eq_one
    (hd : 0 < d)
    {u : NarrowClassGroup.totallyPositiveRingUnits OK K}
    (hfix :
      star ((((u : NarrowClassGroup.totallyPositiveRingUnits OK K) : OKˣ) : OK) : K) =
        ((((u : NarrowClassGroup.totallyPositiveRingUnits OK K) : OKˣ) : OK) : K)) :
    u = 1 :=
  Subtype.ext (fixed_totallyPositiveRingUnit_eq_one d hd (u := (u : OKˣ)) (by
    exact u.2) hfix)

/-- Concrete positive Hilbert 90 for the real quadratic standard model.

This is the `H¹(G, (Lˣ)⁺) = 1` part of Emerton's item 10, written without a
group-cohomology wrapper: if `a` is totally positive and satisfies
`a * conjugate a = 1`, then `a = b / conjugate b` for a totally positive unit
`b`. The proof is the explicit choice `b = 1 + a`. -/
theorem exists_positive_coboundary_of_mul_star_eq_one
    (hd : 0 < d)
    {a : (Qsqrtd (d : ℚ))ˣ}
    (ha_pos : NarrowClassGroup.IsTotallyPositive (a : Qsqrtd (d : ℚ)))
    (ha_norm : (a : Qsqrtd (d : ℚ)) * star (a : Qsqrtd (d : ℚ)) = 1) :
    ∃ b : (Qsqrtd (d : ℚ))ˣ,
      NarrowClassGroup.IsTotallyPositive (b : Qsqrtd (d : ℚ)) ∧
        (a : Qsqrtd (d : ℚ)) = (b : Qsqrtd (d : ℚ)) / star (b : Qsqrtd (d : ℚ)) := by
  have hdR : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  letI : Nonempty (Qsqrtd (d : ℚ) →+* ℝ) :=
    ⟨(realEmbeddingPos d hdR).toRingHom⟩
  simpa [Qsqrtd.starAlgEquiv_apply] using
    (NarrowClassGroup.exists_positive_coboundary_of_mul_apply_eq_one
      (τ := (starAlgEquiv (d : ℚ)).toRingEquiv)
      (a := a) ha_pos (by simpa [Qsqrtd.starAlgEquiv_apply] using ha_norm))

end Real

end Qsqrtd

end QuadraticNumberFields
