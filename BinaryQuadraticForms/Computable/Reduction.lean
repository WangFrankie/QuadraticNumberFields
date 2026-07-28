/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Gauss.Composition
import BinaryQuadraticForms.Core.Enumeration
import BinaryQuadraticForms.Core.Reduction

/-!
# Computable Gauss Reduction

This file provides a computable Gauss reduction algorithm `reduceForm` for
primitive positive-definite binary quadratic forms.

## Algorithm

Given `Q = (a, b, c)` with `a > 0` and `disc < 0`:

1. **Normalise** `b` into `(-a, a]` by a translation `T^k`.
2. If `a > c`, **swap** `(a, c)` and negate `b`, then recurse.
3. Otherwise, if `a = c` and `b < 0`, flip the sign of `b`.
4. Return the result.

Termination: the swap step replaces `a` with `c` where `a > c`, and both are
positive by the positive-definite hypothesis, so the `Nat` measure decreases.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section NormalizeB

/-- The value of `b` after normalisation into `(-a, a]`.  Computed as
`b mod (2a)`, shifted into that interval. -/
@[nolint defsWithUnderscore]
def normalizeB_b (a b : ℤ) (_ha : 0 < a) : ℤ :=
  let r := b % (2 * a)
  if r ≤ a then r else r - 2 * a

/-- The `k` in `T^k` that achieves the normalisation. -/
@[nolint defsWithUnderscore]
def normalizeB_k (a b : ℤ) (ha : 0 < a) : ℤ :=
  (normalizeB_b a b ha - b) / (2 * a)

/-- Apply the translation `T^k` to normalise the middle coefficient. -/
def normalizeB (Q : BinaryQuadraticForm) (ha : 0 < Q.a) : BinaryQuadraticForm :=
  let k := normalizeB_k Q.a Q.b ha
  transform Q (translateSL2Z k)

@[simp] theorem normalizeB_a (Q : BinaryQuadraticForm) (ha : 0 < Q.a) :
    (normalizeB Q ha).a = Q.a := by
  simp [normalizeB]

/-- Explicit formula for `normalizeB_b` when the remainder is ≤ a. -/
private theorem normalizeB_b_eq_r (a b : ℤ) (ha : 0 < a) (h : b % (2 * a) ≤ a) :
    normalizeB_b a b ha = b % (2 * a) := by
  unfold normalizeB_b; simp [h]

/-- Explicit formula for `normalizeB_b` when the remainder is > a. -/
private theorem normalizeB_b_eq_r_sub (a b : ℤ) (ha : 0 < a) (h : ¬ b % (2 * a) ≤ a) :
    normalizeB_b a b ha = b % (2 * a) - 2 * a := by
  unfold normalizeB_b; simp [h]

/-- Explicit formula for the `k` in `normalizeB` when the remainder is ≤ a. -/
private theorem normalizeB_k_eq_div1 (a b : ℤ) (ha : 0 < a) (h : b % (2 * a) ≤ a) :
    normalizeB_k a b ha = (b % (2 * a) - b) / (2 * a) := by
  unfold normalizeB_k; rw [normalizeB_b_eq_r a b ha h]

/-- Explicit formula for the `k` in `normalizeB` when the remainder is > a. -/
private theorem normalizeB_k_eq_div2 (a b : ℤ) (ha : 0 < a) (h : ¬ b % (2 * a) ≤ a) :
    normalizeB_k a b ha = ((b % (2 * a) - 2 * a) - b) / (2 * a) := by
  unfold normalizeB_k; rw [normalizeB_b_eq_r_sub a b ha h]

/-- Exact-division cancellation for the expression that shifts `b` to a congruent value `r`. -/
private theorem add_mul_ediv_sub_of_dvd {b r d : ℤ} (h : d ∣ r - b) :
    b + d * ((r - b) / d) = r := by
  calc
    b + d * ((r - b) / d) = b + (r - b) := by rw [Int.mul_ediv_cancel_of_dvd h]
    _ = r := by ring

/-- Key modular identity: `b + d * ((b % d - b) / d) = b % d`. -/
private theorem mod_cancel (b d : ℤ) : b + d * ((b % d - b) / d) = b % d := by
  exact add_mul_ediv_sub_of_dvd (by simpa using (Int.dvd_emod_sub_self (x := b) (m := d)))

/-- Modular identity with shift: `b + d * (((b % d - d) - b) / d) = b % d - d`. -/
private theorem mod_cancel_sub (b d : ℤ) :
    b + d * (((b % d - d) - b) / d) = b % d - d := by
  refine add_mul_ediv_sub_of_dvd ?_
  have h : d ∣ b % d - b := by simpa using (Int.dvd_emod_sub_self (x := b) (m := d))
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using dvd_sub h dvd_rfl

/-- The middle coefficient after normalisation equals the modular-adjusted value. -/
theorem normalizeB_b_eq (Q : BinaryQuadraticForm) (ha : 0 < Q.a) :
    (normalizeB Q ha).b = normalizeB_b Q.a Q.b ha := by
  set d := 2 * Q.a
  rw [normalizeB, transform_translate_b]
  by_cases h : Q.b % d ≤ Q.a
  · rw [normalizeB_k_eq_div1 Q.a Q.b ha h, normalizeB_b_eq_r Q.a Q.b ha h]
    exact mod_cancel Q.b d
  · rw [normalizeB_k_eq_div2 Q.a Q.b ha h, normalizeB_b_eq_r_sub Q.a Q.b ha h]
    exact mod_cancel_sub Q.b d

/-- The middle coefficient after normalisation lies in `(-a, a]`. -/
theorem normalizeB_bounds (Q : BinaryQuadraticForm) (ha : 0 < Q.a) :
    let Q' := normalizeB Q ha
    (-Q.a < Q'.b ∧ Q'.b ≤ Q.a) := by
  intro Q'
  have hb_eq : Q'.b = normalizeB_b Q.a Q.b ha := normalizeB_b_eq Q ha
  rw [hb_eq]
  have hd_pos : 0 < 2 * Q.a := by nlinarith
  by_cases h : Q.b % (2 * Q.a) ≤ Q.a
  · rw [normalizeB_b_eq_r Q.a Q.b ha h]
    have h_r_nonneg : 0 ≤ Q.b % (2 * Q.a) := Int.emod_nonneg _ (by nlinarith)
    have h_left : -Q.a < Q.b % (2 * Q.a) := by nlinarith
    exact ⟨h_left, h⟩
  · rw [normalizeB_b_eq_r_sub Q.a Q.b ha h]
    have h_r_lt : Q.b % (2 * Q.a) < 2 * Q.a := Int.emod_lt_of_pos _ hd_pos
    have h_r_gt_a : Q.a < Q.b % (2 * Q.a) := Int.not_le.mp h
    have h_left : -Q.a < Q.b % (2 * Q.a) - 2 * Q.a := by nlinarith
    have h_right : Q.b % (2 * Q.a) - 2 * Q.a ≤ Q.a := by nlinarith
    exact ⟨h_left, h_right⟩

end NormalizeB

section Reduce

/-- **Positive c** lemma: for a positive-definite form with `a > 0`,
the trailing coefficient `c` is also positive.  This follows from
`disc = b² - 4ac < 0`. -/
theorem c_pos_of_isPositiveDefinite {Q : BinaryQuadraticForm}
    (hpos : Q.IsPositiveDefinite) : 0 < Q.c := by
  rcases hpos with ⟨ha, hdisc⟩
  have hdisc' : Q.b ^ 2 - 4 * Q.a * Q.c < 0 := by
    simpa [disc] using hdisc
  have hsq_nonneg : 0 ≤ Q.b ^ 2 := pow_two_nonneg _
  nlinarith

private theorem swap_isPositiveDefinite {Q : BinaryQuadraticForm}
    (hpos : Q.IsPositiveDefinite) :
    (BinaryQuadraticForm.mk Q.c (-Q.b) Q.a).IsPositiveDefinite := by
  refine ⟨c_pos_of_isPositiveDefinite hpos, ?_⟩
  calc
    (BinaryQuadraticForm.mk Q.c (-Q.b) Q.a).disc = Q.disc := by
      simp [disc]
      ring
    _ < 0 := hpos.2

/-- Computable Gauss reduction for positive-definite binary quadratic forms.

Termination: the swap step replaces `a` with `c` where `a > c`.  Since
positive-definite forms have `a > 0` and `c > 0`, the natural-number measure
`a.natAbs` strictly decreases. -/
def reduceForm (Q : BinaryQuadraticForm) (hpos : Q.IsPositiveDefinite) :
    BinaryQuadraticForm :=
  have ha_pos : 0 < Q.a := hpos.1
  let Q₁ := normalizeB Q ha_pos
  -- Q₁ has the same discriminant as Q (translation preserves disc)
  have hdisc₁ : Q₁.disc < 0 := by
    have h_eq : Q₁.disc = Q.disc :=
      disc_transform Q (translateSL2Z (normalizeB_k Q.a Q.b ha_pos))
    rw [h_eq]
    exact hpos.2
  -- Q₁.a = Q.a (translation preserves a)
  have ha₁_eq : Q₁.a = Q.a := normalizeB_a Q ha_pos
  -- Q₁.a > 0
  have ha₁_pos : 0 < Q₁.a := by rw [ha₁_eq]; exact ha_pos
  have hpos₁ : Q₁.IsPositiveDefinite := ⟨ha₁_pos, hdisc₁⟩
  if h_swap : Q₁.a > Q₁.c then
    -- Swap a ↔ c and negate b, then recurse.
    let Q₂ : BinaryQuadraticForm := ⟨Q₁.c, -Q₁.b, Q₁.a⟩
    have hpos₂ : Q₂.IsPositiveDefinite := by
      simpa [Q₂] using swap_isPositiveDefinite hpos₁
    reduceForm Q₂ hpos₂
  else
    -- No swap needed: check the boundary condition a = c ∧ b < 0
    if Q₁.a = Q₁.c ∧ Q₁.b < 0 then
      ⟨Q₁.a, -Q₁.b, Q₁.c⟩
    else
      Q₁
termination_by Q.a.natAbs
decreasing_by
  -- Goal: Q₂.a.natAbs < Q.a.natAbs, i.e., Q₁.c.natAbs < Q.a.natAbs
  have hc₁_pos : 0 < Q₁.c := c_pos_of_isPositiveDefinite hpos₁
  have h_lt : Q₁.c < Q.a := by
    calc
      Q₁.c < Q₁.a := h_swap
      _ = Q.a := ha₁_eq
  apply Int.ofNat_lt.mp
  calc
    (Q₁.c.natAbs : ℤ) = Q₁.c := Int.natAbs_of_nonneg (le_of_lt hc₁_pos)
    _ < Q.a := h_lt
    _ = (Q.a.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hpos.1)).symm

/-- The swap matrix `(x, y) ↦ (y, -x)` used in the recursive reduction step. -/
private def swapSL2Z : SL2Z := by
  refine ⟨![![0, 1], ![-1, 0]], ?_⟩
  norm_num [Matrix.det_fin_two]

@[simp] private theorem transform_swapSL2Z (Q : BinaryQuadraticForm) :
    transform Q swapSL2Z = ⟨Q.c, -Q.b, Q.a⟩ := by
  ext
  · change Q.a * 0 ^ 2 + Q.b * 0 * (-1) + Q.c * (-1) ^ 2 = Q.c
    norm_num
  · change 2 * Q.a * 0 * 1 + Q.b * (0 * 0 + 1 * (-1)) + 2 * Q.c * (-1) * 0 =
      -Q.b
    norm_num
  · change Q.a * 1 ^ 2 + Q.b * 1 * 0 + Q.c * 0 ^ 2 = Q.a
    norm_num

private theorem normalizeB_properEquivalent (Q : BinaryQuadraticForm) (ha : 0 < Q.a) :
    ProperEquivalent Q (normalizeB Q ha) :=
  ⟨translateSL2Z (normalizeB_k Q.a Q.b ha), rfl⟩

private theorem swap_properEquivalent (Q : BinaryQuadraticForm) :
    ProperEquivalent Q ⟨Q.c, -Q.b, Q.a⟩ :=
  ⟨swapSL2Z, by simp⟩

private theorem boundary_flip_properEquivalent {Q : BinaryQuadraticForm}
    (hac : Q.a = Q.c) : ProperEquivalent Q ⟨Q.a, -Q.b, Q.c⟩ :=
  ⟨swapSL2Z, by ext <;> simp [hac]⟩

private theorem isReduced_of_normalized_no_swap {Q : BinaryQuadraticForm}
    (hb_left : -Q.a < Q.b) (hb_abs : |Q.b| ≤ Q.a) (hno_swap : ¬ Q.a > Q.c)
    (hboundary : ¬ (Q.a = Q.c ∧ Q.b < 0)) :
    Q.IsReduced := by
  refine ⟨hb_abs, le_of_not_gt hno_swap, ?_, ?_⟩
  · intro hb_eq
    by_contra hb_nonneg
    have hb_neg : Q.b < 0 := lt_of_not_ge hb_nonneg
    have hb_abs_eq : |Q.b| = -Q.b := abs_of_neg hb_neg
    have hneg_eq : -Q.b = Q.a := by
      simpa [hb_abs_eq] using hb_eq
    linarith
  · intro hac
    by_contra hb_nonneg
    exact hboundary ⟨hac, lt_of_not_ge hb_nonneg⟩

private theorem isReduced_boundary_flip {Q : BinaryQuadraticForm}
    (hb_abs : |Q.b| ≤ Q.a) (hno_swap : ¬ Q.a > Q.c) (hboundary : Q.a = Q.c ∧ Q.b < 0) :
    (BinaryQuadraticForm.mk Q.a (-Q.b) Q.c).IsReduced := by
  rw [isReduced_mk_iff]
  have hb_nonneg : 0 ≤ -Q.b := by linarith
  refine ⟨?_, le_of_not_gt hno_swap, ?_, ?_⟩
  · simpa [abs_neg] using hb_abs
  · intro _
    exact hb_nonneg
  · intro _
    exact hb_nonneg

private theorem reduceForm_eq (Q : BinaryQuadraticForm) (hpos : Q.IsPositiveDefinite) :
    reduceForm Q hpos =
      (have ha_pos : 0 < Q.a := hpos.1
       let Q₁ := normalizeB Q ha_pos
       have hdisc₁ : Q₁.disc < 0 := by
         have h_eq : Q₁.disc = Q.disc :=
           disc_transform Q (translateSL2Z (normalizeB_k Q.a Q.b ha_pos))
         rw [h_eq]
         exact hpos.2
       have ha₁_eq : Q₁.a = Q.a := normalizeB_a Q ha_pos
       have ha₁_pos : 0 < Q₁.a := by
         rw [ha₁_eq]
         exact ha_pos
       have hpos₁ : Q₁.IsPositiveDefinite := ⟨ha₁_pos, hdisc₁⟩
       if _h_swap : Q₁.a > Q₁.c then
         let Q₂ : BinaryQuadraticForm := ⟨Q₁.c, -Q₁.b, Q₁.a⟩
         have hpos₂ : Q₂.IsPositiveDefinite := by
           simpa [Q₂] using swap_isPositiveDefinite hpos₁
         reduceForm Q₂ hpos₂
       else
         if Q₁.a = Q₁.c ∧ Q₁.b < 0 then
           ⟨Q₁.a, -Q₁.b, Q₁.c⟩
         else
           Q₁) := by
  unfold reduceForm
  rfl

private theorem reduceForm_correct (Q : BinaryQuadraticForm) (hpos : Q.IsPositiveDefinite) :
    ProperEquivalent Q (reduceForm Q hpos) ∧ (reduceForm Q hpos).IsReduced := by
  let P : ℕ → Prop := fun n => ∀ Q : BinaryQuadraticForm,
    ∀ hpos : Q.IsPositiveDefinite, Q.a.natAbs = n →
      ProperEquivalent Q (reduceForm Q hpos) ∧ (reduceForm Q hpos).IsReduced
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q hpos hn
      have ha_pos : 0 < Q.a := hpos.1
      let Q₁ := normalizeB Q ha_pos
      have hdisc₁ : Q₁.disc < 0 := by
        have h_eq : Q₁.disc = Q.disc :=
          disc_transform Q (translateSL2Z (normalizeB_k Q.a Q.b ha_pos))
        rw [h_eq]
        exact hpos.2
      have ha₁_eq : Q₁.a = Q.a := normalizeB_a Q ha_pos
      have ha₁_pos : 0 < Q₁.a := by rw [ha₁_eq]; exact ha_pos
      have hpos₁ : Q₁.IsPositiveDefinite := ⟨ha₁_pos, hdisc₁⟩
      have hc₁_pos : 0 < Q₁.c := c_pos_of_isPositiveDefinite hpos₁
      have hbounds : -Q.a < Q₁.b ∧ Q₁.b ≤ Q.a := by
        have := normalizeB_bounds Q ha_pos
        simpa [Q₁] using this
      rcases hbounds with ⟨hb_left, hb_right⟩
      have hb_left₁ : -Q₁.a < Q₁.b := by
        simpa [ha₁_eq] using hb_left
      have hb_abs : |Q₁.b| ≤ Q₁.a := by
        rw [ha₁_eq, abs_le]
        constructor <;> linarith
      have hQ_Q₁ : ProperEquivalent Q Q₁ := by
        simpa [Q₁] using normalizeB_properEquivalent Q ha_pos
      rw [reduceForm_eq Q hpos]
      by_cases h_swap : Q₁.a > Q₁.c
      · rw [dif_pos h_swap]
        let Q₂ : BinaryQuadraticForm := ⟨Q₁.c, -Q₁.b, Q₁.a⟩
        have hpos₂ : Q₂.IsPositiveDefinite := by
          simpa [Q₂] using swap_isPositiveDefinite hpos₁
        have hmeasure : Q₂.a.natAbs < n := by
          have hnat : Q₁.c.natAbs < Q.a.natAbs := by
            apply Int.ofNat_lt.mp
            calc
              (Q₁.c.natAbs : ℤ) = Q₁.c := Int.natAbs_of_nonneg (le_of_lt hc₁_pos)
              _ < Q₁.a := h_swap
              _ = Q.a := ha₁_eq
              _ = (Q.a.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hpos.1)).symm
          simpa [Q₂, hn] using hnat
        have hrec := ih Q₂.a.natAbs hmeasure Q₂ hpos₂ rfl
        have hQ₁_Q₂ : ProperEquivalent Q₁ Q₂ := by
          simpa [Q₂] using swap_properEquivalent Q₁
        exact ⟨hQ_Q₁.trans (hQ₁_Q₂.trans hrec.1), hrec.2⟩
      · rw [dif_neg h_swap]
        by_cases hboundary : Q₁.a = Q₁.c ∧ Q₁.b < 0
        · rw [if_pos hboundary]
          have hQ₁_flip : ProperEquivalent Q₁ ⟨Q₁.a, -Q₁.b, Q₁.c⟩ :=
            boundary_flip_properEquivalent hboundary.1
          have hred : (BinaryQuadraticForm.mk Q₁.a (-Q₁.b) Q₁.c).IsReduced :=
            isReduced_boundary_flip hb_abs h_swap hboundary
          exact ⟨hQ_Q₁.trans hQ₁_flip, hred⟩
        · rw [if_neg hboundary]
          exact ⟨hQ_Q₁, isReduced_of_normalized_no_swap hb_left₁ hb_abs h_swap hboundary⟩
  exact hP Q.a.natAbs Q hpos rfl

/-- The result of `reduceForm` is properly equivalent to the input. -/
theorem reduceForm_properEquivalent (Q : BinaryQuadraticForm)
    (hpos : Q.IsPositiveDefinite) :
    ProperEquivalent Q (reduceForm Q hpos) := by
  exact (reduceForm_correct Q hpos).1

/-- The result of `reduceForm` is reduced. -/
theorem reduceForm_isReduced (Q : BinaryQuadraticForm)
    (hpos : Q.IsPositiveDefinite) :
    (reduceForm Q hpos).IsReduced := by
  exact (reduceForm_correct Q hpos).2

/-- The computable reduction of a primitive positive definite form of
discriminant `D` belongs to the finite reduced-form enumeration. -/
theorem reduceForm_mem_enum {D : ℤ} (Q : BinaryQuadraticForm)
    (hdisc : Q.HasDiscriminant D) (hprim : Q.IsPrimitive)
    (hpos : Q.IsPositiveDefinite) :
    reduceForm Q hpos ∈ enumPrimitiveReducedForms D := by
  have hpe := reduceForm_properEquivalent Q hpos
  apply mem_enumPrimitiveReducedForms_of_reduced
  · exact (disc_eq_of_properEquivalent hpe).symm.trans hdisc
  · exact isPositiveDefinite_of_properEquivalent hpos hpe
  · exact reduceForm_isReduced Q hpos
  · exact isPrimitive_of_properEquivalent hprim hpe

/-- The computable reduction packaged in the primitive positive definite
carrier. -/
def reduceFormPrimitive {D : ℤ} (Q : PrimitivePositiveDefiniteForm D) :
    PrimitivePositiveDefiniteForm D :=
  let hpos := Q.2.2.2
  let R := reduceForm Q.1 hpos
  have hmem : R ∈ enumPrimitiveReducedForms D :=
    reduceForm_mem_enum Q.1 Q.2.1 Q.2.2.1 hpos
  primitivePositiveDefiniteFormOfMemEnum hmem

/-- Computable reduction preserves the proper-equivalence class. -/
theorem reduceFormPrimitive_mk_eq {D : ℤ} (Q : PrimitivePositiveDefiniteForm D) :
    Quotient.mk (primitivePositiveDefiniteFormSetoid D) (reduceFormPrimitive Q) =
      Quotient.mk (primitivePositiveDefiniteFormSetoid D) Q := by
  apply Quotient.sound
  exact (reduceForm_properEquivalent Q.1 Q.2.2.2).symm

/-! ## Regression: reduction on spike forms

The spike forms from `d = -21` (`disc = -84`) are:
`(1,0,21)`, `(2,2,11)`, `(3,0,7)`, `(5,4,5)`.

All four happen to already be reduced, so `reduceForm` should return them
unchanged.  We also test a non-reduced form `(6, 6, 5)` which reduces to
`(5, 4, 5)`. -/

/-- The principal spike form, evaluated by the reduction regression test below. -/
def testReducePrincipal : BinaryQuadraticForm :=
  let Q := BinaryQuadraticForm.mk 1 0 21
  have hpos : Q.IsPositiveDefinite := by
    refine ⟨by norm_num, ?_⟩
    unfold disc; norm_num
  reduceForm Q hpos

#eval testReducePrincipal
example : testReducePrincipal = BinaryQuadraticForm.mk 1 0 21 := by
  unfold testReducePrincipal
  rw [reduceForm_eq]
  norm_num [normalizeB, normalizeB_k, normalizeB_b, disc]
  exact transform_one _

/-- A nonprincipal reduced spike form, evaluated by the regression test below. -/
def testReduceNonPrincipal : BinaryQuadraticForm :=
  let Q := BinaryQuadraticForm.mk 2 2 11
  have hpos : Q.IsPositiveDefinite := by
    refine ⟨by norm_num, ?_⟩
    unfold disc; norm_num
  reduceForm Q hpos

#eval testReduceNonPrincipal
example : testReduceNonPrincipal = BinaryQuadraticForm.mk 2 2 11 := by
  unfold testReduceNonPrincipal
  rw [reduceForm_eq]
  norm_num [normalizeB, normalizeB_k, normalizeB_b, disc]
  exact transform_one _

/-- A non-reduced spike form, evaluated by the reduction regression test below. -/
def testReduceNonReduced : BinaryQuadraticForm :=
  let Q := BinaryQuadraticForm.mk 6 6 5
  have hpos : Q.IsPositiveDefinite := by
    refine ⟨by norm_num, ?_⟩
    unfold disc; norm_num
  reduceForm Q hpos

#eval testReduceNonReduced
example : testReduceNonReduced = BinaryQuadraticForm.mk 5 4 5 := by
  unfold testReduceNonReduced
  rw [reduceForm_eq]
  norm_num [normalizeB, normalizeB_k, normalizeB_b, disc]
  rw [reduceForm_eq]
  norm_num [normalizeB, normalizeB_k, normalizeB_b, disc]
  rfl

end Reduce

end BinaryQuadraticForm
end QuadraticNumberFields
