/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.ComputableComposition
import QuadraticNumberFields.Forms.ComputableReduction
import QuadraticNumberFields.Forms.ClassGroupLaw
import QuadraticNumberFields.Forms.CoxComposition
import QuadraticNumberFields.Forms.CoxIdealRelation

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

/-!
# Computable Form Class Group

This file connects the computable Dirichlet composition (`composeForm`) and
Gauss reduction (`reduceForm`) to obtain a computable group multiplication
`gaussMul` on finite reduced-form representatives, and states the main
consistency theorem that `gaussMul = reducedFormRepMul`.

## Main definitions

* `gaussMul` — reduced-form multiplication via `reduceForm ∘ composeForm`
* `gaussMul_eq_reducedFormRepMul` — equality with the Cox-transported law

## Regression

The `d = -21` spike (field discriminant `-84`, class number 4) gives a
Klein four-group; `#eval` verifies the multiplication table.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section GaussMul

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The discriminant of the reduced-form representatives for this `d`. -/
local notation "D" => fieldDiscriminant d

/-- Computable group multiplication on reduced-form representatives:
compose two forms via the CRT-adjusted formula, then reduce the result.

The `IsPositiveDefinite` and enumeration-membership proofs of the result
are deferred to the correctness theorems (the function is still computable
because the proofs are `Prop` arguments that are erased at runtime). -/
def gaussMul (hdneg : d < 0) (Q R : ReducedFormRep D) :
    BinaryQuadraticForm :=
  let Qf := Q.1
  let Rf := R.1
  -- Both are in the reduced enumeration, hence primitive, positive definite,
  -- and have discriminant D.
  have hQprim : Qf.IsPrimitive :=
    (of_mem_enumPrimitiveReducedForms Q.2).2.2.2
  have hRprim : Rf.IsPrimitive :=
    (of_mem_enumPrimitiveReducedForms R.2).2.2.2
  have hQpos : Qf.IsPositiveDefinite :=
    (of_mem_enumPrimitiveReducedForms Q.2).2.1
  have hRpos : Rf.IsPositiveDefinite :=
    (of_mem_enumPrimitiveReducedForms R.2).2.1
  have hdiscQ : Qf.disc = D :=
    (of_mem_enumPrimitiveReducedForms Q.2).1
  have hdiscR : Rf.disc = D :=
    (of_mem_enumPrimitiveReducedForms R.2).1
  have hQR : Qf.disc = Rf.disc := by rw [hdiscQ, hdiscR]
  have hQa : Qf.a ≠ 0 := ne_of_gt hQpos.1
  -- Compute composition, then reduce.  `reduceForm` needs a
  -- positive-definite proof for the composed form; this follows from
  -- discriminant preservation (a > 0 by construction, disc < 0 shown below).
  let comp := composeForm Qf Rf hQR hRprim hQa
  have hcomp_pos : comp.IsPositiveDefinite := by
    have ha_pos : 0 < comp.a := by
      rw [composeForm_a]
      apply mul_pos hQpos.1
      -- R'.a = Rf.eval(coprimeEvalVector Rf Qf.a hRprim hQa), positive by
      -- eval_pos_of_isPositiveDefinite from Action.lean
      rw [unitedRep_a]
      have hxy_nonzero : (coprimeEvalVector Rf Qf.a hRprim hQa).1 ≠ 0 ∨
          (coprimeEvalVector Rf Qf.a hRprim hQa).2 ≠ 0 := by
        have hgcd := coprimeEvalVector_gcd Rf Qf.a hRprim hQa
        by_contra! hboth
        rcases hboth with ⟨hx, hy⟩
        rw [hx, hy] at hgcd; simp at hgcd
      exact eval_pos_of_isPositiveDefinite Rf hRpos hxy_nonzero
    have hdisc_lt : comp.disc < 0 := by
      rw [disc_composeForm Qf Rf hQR hRprim hQa hQpos hRpos]
      rw [hdiscQ]
      exact fieldDiscriminant_neg hdneg
    exact ⟨ha_pos, hdisc_lt⟩
  reduceForm comp hcomp_pos

/-! ## Class-group bridge

### Proof strategy (Cox ideal product, generalised)

The Cox ideal of a form `Q = (a, b, c)` is `coxIdeal DD bb a u_Q` where
`2·u_Q = -(b + bb)`.  For united forms the product formula is:

`coxIdeal(a₁, u₁) * coxIdeal(a₂, u₂) = coxIdeal(a₁·a₂, u_crt)`

where `u_crt` solves `u_crt ≡ u₁ (mod a₁)` and `u_crt ≡ u₂ (mod a₂)`.  In
middle-coefficient terms this means `B_crt` satisfies `B_crt ≡ b₁ (mod 2·a₁)`
and `B_crt ≡ b₂ (mod 2·a₂)`, which is exactly `composeMiddleB`.

The existing `coxIdeal_mul_of_concordant` in `CoxComposition.lean` handles
`b₁ = b₂` (concordant).  The general lemma below removes that restriction.

### Roads not taken (for future simplification)

* **Translation to concordant:** `composeForm` is a translation of
  `composeConcordant` only when `R'.a ∣ k₁` (where `k₁ = (Q.b - B) / (2·Q.a)`),
  which is false in general.
* **Concordant representative by translation:** Making united forms concordant
  via `T^k` on `R'` needs `2·R'.a ∣ (Q.b - R'.b)`, not guaranteed.
* **Explicit SL₂ equivalence:** Cox Theorem 3.14 gives an explicit matrix, but
  constructing it requires the full Gauss composition algebra. -/

open CoxIdealRelation

/-- **Generalised Cox ideal product** for united (non-concordant) forms.

The proof adapts `CoxComposition.coxIdeal_mul_of_concordant` to handle different
middle coefficients `B₁ ≠ B₂`, using the CRT congruences to relate `β₁ = ⟨u₁,1⟩`
and `β₂ = ⟨u₂,1⟩` to `β = ⟨u,1⟩` via `β₁ = β - t·A₁`, `β₂ = β - k·A₂`. -/
theorem coxIdeal_mul_of_united
    {DD bb A₁ A₂ C₁ C₂ B B₁ B₂ u₁ u₂ u : ℤ}
    (hdiscQ : B₁ ^ 2 - 4 * A₁ * C₁ = bb ^ 2 + 4 * DD)
    (hdiscR : B₂ ^ 2 - 4 * A₂ * C₂ = bb ^ 2 + 4 * DD)
    (hu₁ : 2 * u₁ = -(B₁ + bb))
    (hu₂ : 2 * u₂ = -(B₂ + bb))
    (hu : 2 * u = -(B + bb))
    (hcop : Int.gcd A₁ A₂ = 1)
    (h_mod_left : B ≡ B₁ [ZMOD 2 * A₁])
    (h_mod_right : B ≡ B₂ [ZMOD 2 * A₂]) :
    CoxIdealRelation.coxIdeal DD bb A₁ u₁ * CoxIdealRelation.coxIdeal DD bb A₂ u₂ =
      CoxIdealRelation.coxIdeal DD bb (A₁ * A₂) u := by
  exact CoxComposition.coxIdeal_mul_of_united hdiscQ hdiscR hu₁ hu₂ hu hcop h_mod_left
    h_mod_right

private theorem even_of_modEq_even {B b a : ℤ} (hb : Even b)
    (hB : B ≡ b [ZMOD 2 * a]) : Even B := by
  rcases hb with ⟨m, hm⟩
  rcases Int.modEq_iff_dvd.mp hB with ⟨k, hk⟩
  use m - a * k
  have hB_eq : B = b - 2 * a * k := by linarith
  rw [hB_eq, hm]
  ring

private theorem odd_of_modEq_odd {B b a : ℤ} (hb : Odd b)
    (hB : B ≡ b [ZMOD 2 * a]) : Odd B := by
  rcases hb with ⟨m, hm⟩
  rcases Int.modEq_iff_dvd.mp hB with ⟨k, hk⟩
  use m - a * k
  have hB_eq : B = b - 2 * a * k := by linarith
  rw [hB_eq, hm]
  ring

/-- Wrap the coprime right-factor replacement as a primitive positive definite
form. -/
def unitedRepPrimitiveOfCoprime
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0) :
    PrimitivePositiveDefiniteForm (fieldDiscriminant d) :=
  let R' := unitedRep Q.1 R.1 hRprim hQa
  have hRpe : ProperEquivalent R.1 R' :=
    unitedRep_properEquivalent Q.1 R.1 hRprim hQa
  have hdiscR' : R'.HasDiscriminant (fieldDiscriminant d) := by
    rw [BinaryQuadraticForm.HasDiscriminant]
    exact (disc_eq_of_properEquivalent hRpe).symm.trans R.2.1
  have hprimR' : R'.IsPrimitive :=
    isPrimitive_of_properEquivalent R.2.2.1 hRpe
  have hposR' : R'.IsPositiveDefinite :=
    isPositiveDefinite_of_properEquivalent R.2.2.2 hRpe
  ⟨R', hdiscR', hprimR', hposR'⟩

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
/-- The wrapped coprime right-factor replacement is properly equivalent to the
original right factor. -/
theorem unitedRepPrimitiveOfCoprime_properEquivalent
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0) :
    PrimitivePositiveDefiniteForm.ProperEquivalent R
      (unitedRepPrimitiveOfCoprime Q R hRprim hQa) := by
  exact unitedRep_properEquivalent Q.1 R.1 hRprim hQa

/-- Wrap `composeForm` as a `PrimitivePositiveDefiniteForm`.  Requires
`disc_composeForm` and `isPrimitive_composeForm` (already proved). -/
def composeFormPrimitiveOfCoprime (hdneg : d < 0)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    PrimitivePositiveDefiniteForm (fieldDiscriminant d) :=
  have hQprim : Q.1.IsPrimitive := Q.2.2.1
  let F := composeForm Q.1 R.1 hQR hRprim hQa
  have hdiscF : F.HasDiscriminant (fieldDiscriminant d) := by
    rw [BinaryQuadraticForm.HasDiscriminant]
    rw [disc_composeForm Q.1 R.1 hQR hRprim hQa hQpos hRpos, Q.2.1]
  have hprimF : F.IsPrimitive :=
    isPrimitive_composeForm Q.1 R.1 hQR hQprim hRprim hQa hQpos hRpos
  have hposF : F.IsPositiveDefinite := by
    refine ⟨?_, ?_⟩
    · rw [composeForm_a]
      have hR'a_pos : 0 < (unitedRep Q.1 R.1 hRprim hQa).a := by
        rw [unitedRep_a]
        have hxy_gcd : Int.gcd (coprimeEvalVector R.1 Q.1.a hRprim hQa).1
            (coprimeEvalVector R.1 Q.1.a hRprim hQa).2 = 1 :=
          coprimeEvalVector_gcd R.1 Q.1.a hRprim hQa
        have hxy_nonzero : (coprimeEvalVector R.1 Q.1.a hRprim hQa).1 ≠ 0 ∨
            (coprimeEvalVector R.1 Q.1.a hRprim hQa).2 ≠ 0 := by
          by_contra! hboth
          rcases hboth with ⟨hx, hy⟩
          rw [hx, hy] at hxy_gcd; simp at hxy_gcd
        exact eval_pos_of_isPositiveDefinite R.1 hRpos hxy_nonzero
      exact mul_pos hQpos.1 hR'a_pos
    · rw [disc_composeForm Q.1 R.1 hQR hRprim hQa hQpos hRpos, Q.2.1]
      exact fieldDiscriminant_neg hdneg
  ⟨F, ⟨hdiscF, hprimF, ⟨hposF.1, hposF.2⟩⟩⟩

/-- In the non-half-integral branch, the computable CRT composition has the
expected product ideal after replacing the right factor by its coprime
representative. -/
theorem idealOfForm_composeForm_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    idealOfForm_of_mod_four_ne_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos) =
      idealOfForm_of_mod_four_ne_one d hd4 Q *
        idealOfForm_of_mod_four_ne_one d hd4
          (unitedRepPrimitiveOfCoprime Q R hRprim hQa) := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let R'F := unitedRepPrimitiveOfCoprime Q R hRprim hQa
  let R' := R'F.1
  let B := composeMiddleB Q.1 R'
  let u₁ : ℤ := (-Q.1.b) / 2
  let u₂ : ℤ := (-R'.b) / 2
  let u : ℤ := (-B) / 2
  have hcop : Int.gcd Q.1.a R'.a = 1 := by
    simpa [R'F, R'] using gcd_left_a_unitedRep Q.1 R.1 hRprim hQa
  have hdisc_eq : Q.1.disc = R'.disc := by
    simpa [R'F, R'] using
      hQR.trans (disc_eq_of_properEquivalent
        (unitedRep_properEquivalent Q.1 R.1 hRprim hQa))
  have hpar : 2 ∣ R'.b - Q.1.b := by
    rcases even_sub_b_of_same_discriminant hdisc_eq with ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩
  have h_mod_left : B ≡ Q.1.b [ZMOD 2 * Q.1.a] := by
    simpa [B] using composeMiddleB_modEq_left Q.1 R'
  have h_mod_right : B ≡ R'.b [ZMOD 2 * R'.a] := by
    simpa [B] using composeMiddleB_modEq_right Q.1 R' hcop hpar
  have hbQ_even : Even Q.1.b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
  have hbR_even : Even R'.b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 R'F.2.1
  have hB_even : Even B :=
    even_of_modEq_even hbQ_even h_mod_left
  have hu₁ : 2 * u₁ = -(Q.1.b + 0) := by
    simpa [u₁] using
      PrimitivePositiveDefiniteForm.two_mul_neg_div_two_of_even hbQ_even
  have hu₂ : 2 * u₂ = -(R'.b + 0) := by
    simpa [u₂] using
      PrimitivePositiveDefiniteForm.two_mul_neg_div_two_of_even hbR_even
  have hu : 2 * u = -(B + 0) := by
    simpa [u] using
      PrimitivePositiveDefiniteForm.two_mul_neg_div_two_of_even hB_even
  have hdiscQ : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 0 ^ 2 + 4 * d := by
    simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
      fieldDiscriminant_of_mod_four_ne_one hd4] using Q.2.1
  have hdiscR : R'.b ^ 2 - 4 * R'.a * R'.c = 0 ^ 2 + 4 * d := by
    simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
      fieldDiscriminant_of_mod_four_ne_one hd4] using R'F.2.1
  have hcoord :
      CoxIdealRelation.coxIdeal d 0 Q.1.a u₁ *
          CoxIdealRelation.coxIdeal d 0 R'.a u₂ =
        CoxIdealRelation.coxIdeal d 0 (Q.1.a * R'.a) u :=
    coxIdeal_mul_of_united hdiscQ hdiscR hu₁ hu₂ hu hcop h_mod_left h_mod_right
  calc
    idealOfForm_of_mod_four_ne_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos)
        = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)
            (CoxIdealRelation.coxIdeal d 0 (Q.1.a * R'.a) u) := by
          simp [idealOfForm_of_mod_four_ne_one, composeFormPrimitiveOfCoprime,
            unitedRepPrimitiveOfCoprime, composeForm, CoxIdealRelation.coxIdeal, Int.cast_mul,
            e, R'F, R', B, u]
    _ = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)
          (CoxIdealRelation.coxIdeal d 0 Q.1.a u₁ *
            CoxIdealRelation.coxIdeal d 0 R'.a u₂) := by
          rw [hcoord]
    _ = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)
          (CoxIdealRelation.coxIdeal d 0 Q.1.a u₁) *
        Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)
          (CoxIdealRelation.coxIdeal d 0 R'.a u₂) := by
          rw [PrimitivePositiveDefiniteForm.comap_mul_of_ringEquiv]
    _ = idealOfForm_of_mod_four_ne_one d hd4 Q *
        idealOfForm_of_mod_four_ne_one d hd4 R'F := by
          simp [idealOfForm_of_mod_four_ne_one, CoxIdealRelation.coxIdeal, e, R'F, R',
            u₁, u₂]

/-- In the non-half-integral branch, computable CRT composition multiplies Cox
ideal classes after replacing the right factor by its coprime representative. -/
theorem idealClassOfForm_composeForm_unitedRep_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos) =
      idealClassOfForm_of_mod_four_ne_one d hd4 Q *
        idealClassOfForm_of_mod_four_ne_one d hd4
          (unitedRepPrimitiveOfCoprime Q R hRprim hQa) := by
  unfold idealClassOfForm_of_mod_four_ne_one
  rw [← map_mul]
  apply congrArg ClassGroup.mk0
  apply Subtype.ext
  exact idealOfForm_composeForm_of_mod_four_ne_one hdneg hd4 Q R hQR hRprim hQa hQpos hRpos

/-- In the non-half-integral branch, computable CRT composition multiplies
Cox ideal classes. -/
theorem idealClassOfForm_composeForm_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos) =
      idealClassOfForm_of_mod_four_ne_one d hd4 Q *
        idealClassOfForm_of_mod_four_ne_one d hd4 R := by
  let R'F := unitedRepPrimitiveOfCoprime Q R hRprim hQa
  have hraw :=
    idealClassOfForm_composeForm_unitedRep_of_mod_four_ne_one
      hdneg hd4 Q R hQR hRprim hQa hQpos hRpos
  have hRclass :
      idealClassOfForm_of_mod_four_ne_one d hd4 R =
        idealClassOfForm_of_mod_four_ne_one d hd4 R'F :=
    idealClassOfForm_of_mod_four_ne_one_eq_of_properEquivalent d hd4 R R'F
      (unitedRepPrimitiveOfCoprime_properEquivalent Q R hRprim hQa)
  calc
    idealClassOfForm_of_mod_four_ne_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos)
        = idealClassOfForm_of_mod_four_ne_one d hd4 Q *
          idealClassOfForm_of_mod_four_ne_one d hd4 R'F := hraw
    _ = idealClassOfForm_of_mod_four_ne_one d hd4 Q *
        idealClassOfForm_of_mod_four_ne_one d hd4 R := by
          rw [← hRclass]

/-- **Class-group consistency of computable composition.**

Under the Cox equivalence, the CRT-adjusted `composeForm` represents the
product of form classes.  This is the linchpin connecting the computable
Gauss pipeline to the existing transported `CommGroup` on `FormClass`.

Uses `coxIdeal_mul_of_united` (above) for the ideal-product identity,
`unitedRep_properEquivalent` for right-factor replacement, and
`formClassEquivClassGroup` injectivity for the quotient lift. -/
theorem composeForm_mk (hdneg : d < 0)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    haveI := formClassCommGroup hdneg
    Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d))
      (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos) =
      @Mul.mul (FormClass (fieldDiscriminant d)) (formClassCommGroup hdneg).toMul
        (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q :
          FormClass (fieldDiscriminant d))
        (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R :
          FormClass (fieldDiscriminant d)) := by
  apply (formClassEquivClassGroup hdneg).injective
  -- Reduces to equality of ideal classes via the Cox 7.7 map.
  -- `formClassToClassGroup d (mk (composeForm …))`
  --   = class of `coxIdeal(composeForm)`
  --   = class of `coxIdeal(Q) * coxIdeal(R')`   (by coxIdeal_mul_of_united)
  --   = class of `coxIdeal(Q) * coxIdeal(R)`    (R' ~ R ⇒ same ideal class)
  --   = `formClassToClassGroup d (mk Q) * formClassToClassGroup d (mk R)`
  sorry

/-- The computable Gauss multiplication equals the Cox-transported
class-group law on reduced-form representatives
(both as `BinaryQuadraticForm` values). -/
theorem gaussMul_eq_reducedFormRepMul_val
    (hdneg : d < 0) (Q R : ReducedFormRep D) :
    gaussMul hdneg Q R = (reducedFormRepMul hdneg Q R).1 := by
  -- Both sides are the unique reduced representative of the product class.
  -- By `composeForm_mk`, the composition represents the product class.
  -- By `reduceForm_properEquivalent`, the reduction is in the same class.
  -- By `reducedFormRepMul_formClass`, `reducedFormRepMul` also represents
  -- the product class.  Both are reduced, so they are equal by uniqueness
  -- (`eq_of_isReduced_of_mk_eq_mk` / `reducedRepresentativeRep_formClass_leftInverse`).
  --
  -- Dependency: `composeForm_mk` (above) and `reduceForm_mem_enum` (proved).
  sorry

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
/-- The `gaussMul` result belongs to the reduced-form enumeration. -/
theorem mem_enum_of_gaussMul (hdneg : d < 0) (Q R : ReducedFormRep D) :
    gaussMul hdneg Q R ∈ enumPrimitiveReducedForms D := by
  unfold gaussMul
  let Qf := Q.1
  let Rf := R.1
  have hQprim : Qf.IsPrimitive := (of_mem_enumPrimitiveReducedForms Q.2).2.2.2
  have hRprim : Rf.IsPrimitive := (of_mem_enumPrimitiveReducedForms R.2).2.2.2
  have hQpos : Qf.IsPositiveDefinite := (of_mem_enumPrimitiveReducedForms Q.2).2.1
  have hRpos : Rf.IsPositiveDefinite := (of_mem_enumPrimitiveReducedForms R.2).2.1
  have hdiscQ : Qf.disc = D := (of_mem_enumPrimitiveReducedForms Q.2).1
  have hdiscR : Rf.disc = D := (of_mem_enumPrimitiveReducedForms R.2).1
  have hQR : Qf.disc = Rf.disc := by rw [hdiscQ, hdiscR]
  have hQa : Qf.a ≠ 0 := ne_of_gt hQpos.1
  let comp := composeForm Qf Rf hQR hRprim hQa
  have hcomp_pos : comp.IsPositiveDefinite := by
    have ha_pos : 0 < comp.a := by
      rw [composeForm_a]
      apply mul_pos hQpos.1
      rw [unitedRep_a]
      have hxy_gcd : Int.gcd (coprimeEvalVector Rf Qf.a hRprim hQa).1
          (coprimeEvalVector Rf Qf.a hRprim hQa).2 = 1 :=
        coprimeEvalVector_gcd Rf Qf.a hRprim hQa
      have hxy_nonzero : (coprimeEvalVector Rf Qf.a hRprim hQa).1 ≠ 0 ∨
          (coprimeEvalVector Rf Qf.a hRprim hQa).2 ≠ 0 := by
        by_contra! hboth
        rcases hboth with ⟨hx, hy⟩
        rw [hx, hy] at hxy_gcd; simp at hxy_gcd
      exact eval_pos_of_isPositiveDefinite Rf hRpos hxy_nonzero
    have hdisc_lt : comp.disc < 0 := by
      rw [disc_composeForm Qf Rf hQR hRprim hQa hQpos hRpos, hdiscQ]
      exact fieldDiscriminant_neg hdneg
    exact ⟨ha_pos, hdisc_lt⟩
  have hcomp_disc : comp.HasDiscriminant D := by
    rw [BinaryQuadraticForm.HasDiscriminant,
      disc_composeForm Qf Rf hQR hRprim hQa hQpos hRpos, hdiscQ]
  have hcomp_prim : comp.IsPrimitive :=
    isPrimitive_composeForm Qf Rf hQR hQprim hRprim hQa hQpos hRpos
  exact reduceForm_mem_enum comp hcomp_disc hcomp_prim hcomp_pos

/-- The computable Gauss multiplication, lifted to `ReducedFormRep`,
agrees with the Cox-transported law. -/
theorem gaussMul_eq_reducedFormRepMul
    (hdneg : d < 0) (Q R : ReducedFormRep D) :
    (⟨gaussMul hdneg Q R, mem_enum_of_gaussMul hdneg Q R⟩ : ReducedFormRep D) =
      reducedFormRepMul hdneg Q R := by
  apply Subtype.ext
  exact gaussMul_eq_reducedFormRepMul_val hdneg Q R

end GaussMul

/-! ## Regression: multiplication table for `d = -21`

The spike confirms: `fieldDiscriminant (-21 : ℚ) = -84`, reduced forms
`[(1,0,21), (2,2,11), (3,0,7), (5,4,5)]`, class group ≅ `ℤ/2 × ℤ/2`.

We verify via `#eval` that the composition pipeline
(`composeForm` → `reduceForm`) reproduces the Klein four-group structure
on concrete forms. -/

section Regression_d21

/-- All four reduced forms for discriminant `-84`. -/
def f1 : BinaryQuadraticForm := BinaryQuadraticForm.mk 1 0 21
def f2 : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 2 11
def f3 : BinaryQuadraticForm := BinaryQuadraticForm.mk 3 0 7
def f4 : BinaryQuadraticForm := BinaryQuadraticForm.mk 5 4 5

/-- Compose and reduce two forms in one step (for `#eval` testing). -/
def composeAndReduce (Q R : BinaryQuadraticForm) : BinaryQuadraticForm :=
  if hQR : Q.disc = R.disc then
    if hRprim : R.IsPrimitive then
      if hQa : Q.a ≠ 0 then
        let comp := composeForm Q R hQR hRprim hQa
        if hcomp_pos : comp.IsPositiveDefinite then
          reduceForm comp hcomp_pos
        else
          comp
      else
        Q
    else
      Q
  else
    Q

-- `#eval` the full pipeline on `(2,2,11) × (2,2,11)` (order-2 element).
#eval composeAndReduce f2 f2
-- Expected: identity form `(1,0,21)`.
example : composeAndReduce f2 f2 = f1 := by
  native_decide

-- `#eval` the full pipeline on `(3,0,7) × (3,0,7)` (order-2 element).
#eval composeAndReduce f3 f3
example : composeAndReduce f3 f3 = f1 := by
  native_decide

-- `#eval` the full pipeline on `(5,4,5) × (5,4,5)` (order-2 element).
#eval composeAndReduce f4 f4
example : composeAndReduce f4 f4 = f1 := by
  native_decide

-- `#eval` the full pipeline on `(2,2,11) × (3,0,7)`.
#eval composeAndReduce f2 f3
-- Product of the two distinct non-identity elements gives the third.
example : composeAndReduce f2 f3 = f4 := by
  native_decide

-- `#eval` the full pipeline on `(2,2,11) × (5,4,5)`.
#eval composeAndReduce f2 f4
example : composeAndReduce f2 f4 = f3 := by
  native_decide

-- `#eval` the full pipeline on `(3,0,7) × (5,4,5)`.
#eval composeAndReduce f3 f4
example : composeAndReduce f3 f4 = f2 := by
  native_decide

-- Identity: `(1,0,21) × anything = anything`.
#eval composeAndReduce f1 f2
example : composeAndReduce f1 f2 = f2 := by native_decide
#eval composeAndReduce f1 f3
example : composeAndReduce f1 f3 = f3 := by native_decide
#eval composeAndReduce f1 f4
example : composeAndReduce f1 f4 = f4 := by native_decide

/-- Full Klein four-group verified: all 10 non-trivial table entries match. -/
example : composeAndReduce f1 f1 = f1 := by native_decide

end Regression_d21

end BinaryQuadraticForm
end QuadraticNumberFields
