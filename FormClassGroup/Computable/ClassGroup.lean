/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Computable.Composition
import BinaryQuadraticForms.Computable.Reduction
import FormClassGroup.ClassGroup.Law
import FormClassGroup.ClassGroup.CoxComposition
import BinaryQuadraticForms.Cox.IdealRelation
import QNFMathlib.Data.Int.Parity

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
  have _hDneg : D < 0 := fieldDiscriminant_neg hdneg
  -- Both are in the reduced enumeration, hence positive definite and have
  -- discriminant D; the right factor is primitive for composition.
  have hRprim : Rf.IsPrimitive :=
    by simpa [Rf] using R.isPrimitive
  have hQpos : Qf.IsPositiveDefinite :=
    by simpa [Qf] using Q.isPositiveDefinite
  have hRpos : Rf.IsPositiveDefinite :=
    by simpa [Rf] using R.isPositiveDefinite
  have hdiscQ : Qf.disc = D :=
    by simpa [Qf] using Q.disc_eq
  have hdiscR : Rf.disc = D :=
    by simpa [Rf] using R.disc_eq
  have hQR : Qf.disc = Rf.disc := by rw [hdiscQ, hdiscR]
  have hQa : Qf.a ≠ 0 := ne_of_gt hQpos.1
  -- Compute composition, then reduce.
  let comp := composeForm Qf Rf hQR hRprim hQa
  have hcomp_pos : comp.IsPositiveDefinite :=
    composeForm_isPositiveDefinite Qf Rf hQR hRprim hQa hQpos hRpos
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
  have _hDneg : fieldDiscriminant d < 0 := fieldDiscriminant_neg hdneg
  have hQprim : Q.1.IsPrimitive := Q.2.2.1
  let F := composeForm Q.1 R.1 hQR hRprim hQa
  have hdiscF : F.HasDiscriminant (fieldDiscriminant d) := by
    rw [BinaryQuadraticForm.HasDiscriminant]
    rw [disc_composeForm Q.1 R.1 hQR hRprim hQa hQpos hRpos, Q.2.1]
  have hprimF : F.IsPrimitive :=
    isPrimitive_composeForm Q.1 R.1 hQR hQprim hRprim hQa hQpos hRpos
  have hposF : F.IsPositiveDefinite :=
    composeForm_isPositiveDefinite Q.1 R.1 hQR hRprim hQa hQpos hRpos
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
    Int.even_of_modEq_even hbQ_even h_mod_left
  have hu₁ : 2 * u₁ = -(Q.1.b + 0) := by
    simpa [u₁] using
      Int.two_mul_neg_ediv_two_of_even hbQ_even
  have hu₂ : 2 * u₂ = -(R'.b + 0) := by
    simpa [u₂] using
      Int.two_mul_neg_ediv_two_of_even hbR_even
  have hu : 2 * u = -(B + 0) := by
    simpa [u] using
      Int.two_mul_neg_ediv_two_of_even hB_even
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
    CoxComposition.coxIdeal_mul_of_united hdiscQ hdiscR hu₁ hu₂ hu hcop h_mod_left
      h_mod_right
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
          rw [Ideal.comap_mul_of_ringEquiv]
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

/-- In the half-integral branch, the computable CRT composition has the
expected product ideal after replacing the right factor by its coprime
representative. -/
theorem idealOfForm_composeForm_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    idealOfForm_of_mod_four_eq_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos) =
      idealOfForm_of_mod_four_eq_one d hd4 Q *
        idealOfForm_of_mod_four_eq_one d hd4
          (unitedRepPrimitiveOfCoprime Q R hRprim hQa) := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let R'F := unitedRepPrimitiveOfCoprime Q R hRprim hQa
  let R' := R'F.1
  let B := composeMiddleB Q.1 R'
  let u₁ : ℤ := -(Q.1.b + 1) / 2
  let u₂ : ℤ := -(R'.b + 1) / 2
  let u : ℤ := -(B + 1) / 2
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
  have hbQ_odd : Odd Q.1.b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
  have hbR_odd : Odd R'.b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 R'F.2.1
  have hB_odd : Odd B :=
    Int.odd_of_modEq_odd hbQ_odd h_mod_left
  have hu₁ : 2 * u₁ = -(Q.1.b + 1) := by
    simpa [u₁] using
      Int.two_mul_neg_succ_ediv_two_of_odd hbQ_odd
  have hu₂ : 2 * u₂ = -(R'.b + 1) := by
    simpa [u₂] using
      Int.two_mul_neg_succ_ediv_two_of_odd hbR_odd
  have hu : 2 * u = -(B + 1) := by
    simpa [u] using
      Int.two_mul_neg_succ_ediv_two_of_odd hB_odd
  have hdiscQ : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 1 ^ 2 + 4 * (d / 4) := by
    have hdisc_d : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = d := by
      simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
        fieldDiscriminant_of_mod_four_eq_one hd4] using Q.2.1
    omega
  have hdiscR : R'.b ^ 2 - 4 * R'.a * R'.c = 1 ^ 2 + 4 * (d / 4) := by
    have hdisc_d : R'.b ^ 2 - 4 * R'.a * R'.c = d := by
      simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
        fieldDiscriminant_of_mod_four_eq_one hd4] using R'F.2.1
    omega
  have hcoord :
      CoxIdealRelation.coxIdeal (d / 4) 1 Q.1.a u₁ *
          CoxIdealRelation.coxIdeal (d / 4) 1 R'.a u₂ =
        CoxIdealRelation.coxIdeal (d / 4) 1 (Q.1.a * R'.a) u :=
    CoxComposition.coxIdeal_mul_of_united hdiscQ hdiscR hu₁ hu₂ hu hcop h_mod_left
      h_mod_right
  calc
    idealOfForm_of_mod_four_eq_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos)
        = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))
            (CoxIdealRelation.coxIdeal (d / 4) 1 (Q.1.a * R'.a) u) := by
          simp [idealOfForm_of_mod_four_eq_one, composeFormPrimitiveOfCoprime,
            unitedRepPrimitiveOfCoprime, composeForm, CoxIdealRelation.coxIdeal, Int.cast_mul,
            e, R'F, R', B, u]
    _ = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))
          (CoxIdealRelation.coxIdeal (d / 4) 1 Q.1.a u₁ *
            CoxIdealRelation.coxIdeal (d / 4) 1 R'.a u₂) := by
          rw [hcoord]
    _ = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))
          (CoxIdealRelation.coxIdeal (d / 4) 1 Q.1.a u₁) *
        Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))
          (CoxIdealRelation.coxIdeal (d / 4) 1 R'.a u₂) := by
          rw [Ideal.comap_mul_of_ringEquiv]
    _ = idealOfForm_of_mod_four_eq_one d hd4 Q *
        idealOfForm_of_mod_four_eq_one d hd4 R'F := by
          simp [idealOfForm_of_mod_four_eq_one, CoxIdealRelation.coxIdeal, e, R'F, R',
            u₁, u₂]

/-- In the half-integral branch, computable CRT composition multiplies Cox
ideal classes after replacing the right factor by its coprime representative. -/
theorem idealClassOfForm_composeForm_unitedRep_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos) =
      idealClassOfForm_of_mod_four_eq_one d hd4 Q *
        idealClassOfForm_of_mod_four_eq_one d hd4
          (unitedRepPrimitiveOfCoprime Q R hRprim hQa) := by
  unfold idealClassOfForm_of_mod_four_eq_one
  rw [← map_mul]
  apply congrArg ClassGroup.mk0
  apply Subtype.ext
  exact idealOfForm_composeForm_of_mod_four_eq_one hdneg hd4 Q R hQR hRprim hQa hQpos hRpos

/-- In the half-integral branch, computable CRT composition multiplies Cox ideal
classes. -/
theorem idealClassOfForm_composeForm_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos) =
      idealClassOfForm_of_mod_four_eq_one d hd4 Q *
        idealClassOfForm_of_mod_four_eq_one d hd4 R := by
  let R'F := unitedRepPrimitiveOfCoprime Q R hRprim hQa
  have hraw :=
    idealClassOfForm_composeForm_unitedRep_of_mod_four_eq_one
      hdneg hd4 Q R hQR hRprim hQa hQpos hRpos
  have hRclass :
      idealClassOfForm_of_mod_four_eq_one d hd4 R =
        idealClassOfForm_of_mod_four_eq_one d hd4 R'F :=
    idealClassOfForm_of_mod_four_eq_one_eq_of_properEquivalent d hd4 R R'F
      (unitedRepPrimitiveOfCoprime_properEquivalent Q R hRprim hQa)
  calc
    idealClassOfForm_of_mod_four_eq_one d hd4
        (composeFormPrimitiveOfCoprime hdneg Q R hQR hRprim hQa hQpos hRpos)
        = idealClassOfForm_of_mod_four_eq_one d hd4 Q *
          idealClassOfForm_of_mod_four_eq_one d hd4 R'F := hraw
    _ = idealClassOfForm_of_mod_four_eq_one d hd4 Q *
        idealClassOfForm_of_mod_four_eq_one d hd4 R := by
          rw [← hRclass]

/-- **Class-group consistency of computable composition.**

Under the Cox equivalence, the CRT-adjusted `composeForm` represents the
product of form classes.  This is the linchpin connecting the computable
Gauss pipeline to the existing transported `CommGroup` on `FormClass`.

Uses `CoxComposition.coxIdeal_mul_of_united` for the ideal-product identity,
`unitedRep_properEquivalent` for right-factor replacement, and
`formClassEquivClassGroup` injectivity for the quotient lift. -/
theorem composeForm_mk [Fact (d < 0)]
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : Q.1.disc = R.1.disc) (hRprim : R.1.IsPrimitive) (hQa : Q.1.a ≠ 0)
    (hQpos : Q.1.IsPositiveDefinite) (hRpos : R.1.IsPositiveDefinite) :
    Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d))
      (composeFormPrimitiveOfCoprime (Fact.out : d < 0) Q R hQR hRprim hQa hQpos hRpos) =
      (((Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q :
          FormClass (fieldDiscriminant d)) *
        (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R :
          FormClass (fieldDiscriminant d))) :
        FormClass (fieldDiscriminant d)) := by
  let hdneg : d < 0 := Fact.out
  apply (formClassEquivClassGroup hdneg).injective
  let q : FormClass (fieldDiscriminant d) :=
    Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q
  let r : FormClass (fieldDiscriminant d) :=
    Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R
  change formClassToClassGroup d
      (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d))
        (composeFormPrimitiveOfCoprime (Fact.out : d < 0) Q R hQR hRprim hQa hQpos hRpos)) =
    formClassToClassGroup d (q * r)
  rw [show formClassToClassGroup d
      (q * r) = formClassToClassGroup d q * formClassToClassGroup d r by
    simpa [q, r] using formClassEquivClassGroup_mul hdneg q r]
  by_cases hd4 : d % 4 = 1
  · rw [formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4]
    rw [formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4]
    rw [formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4]
    exact idealClassOfForm_composeForm_of_mod_four_eq_one
      (Fact.out : d < 0) hd4 Q R hQR hRprim hQa hQpos hRpos
  · rw [formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4]
    rw [formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4]
    rw [formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4]
    exact idealClassOfForm_composeForm_of_mod_four_ne_one
      (Fact.out : d < 0) hd4 Q R hQR hRprim hQa hQpos hRpos

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
/-- The `gaussMul` result belongs to the reduced-form enumeration. -/
theorem mem_enum_of_gaussMul (hdneg : d < 0) (Q R : ReducedFormRep D) :
    gaussMul hdneg Q R ∈ enumPrimitiveReducedForms D := by
  unfold gaussMul
  let Qf := Q.1
  let Rf := R.1
  have hQprim : Qf.IsPrimitive := by simpa [Qf] using Q.isPrimitive
  have hRprim : Rf.IsPrimitive := by simpa [Rf] using R.isPrimitive
  have hQpos : Qf.IsPositiveDefinite := by simpa [Qf] using Q.isPositiveDefinite
  have hRpos : Rf.IsPositiveDefinite := by simpa [Rf] using R.isPositiveDefinite
  have hdiscQ : Qf.disc = D := by simpa [Qf] using Q.disc_eq
  have hdiscR : Rf.disc = D := by simpa [Rf] using R.disc_eq
  have hQR : Qf.disc = Rf.disc := by rw [hdiscQ, hdiscR]
  have hQa : Qf.a ≠ 0 := ne_of_gt hQpos.1
  let comp := composeForm Qf Rf hQR hRprim hQa
  have hcomp_pos : comp.IsPositiveDefinite :=
    composeForm_isPositiveDefinite Qf Rf hQR hRprim hQa hQpos hRpos
  have hcomp_disc : comp.HasDiscriminant D := by
    rw [BinaryQuadraticForm.HasDiscriminant,
      disc_composeForm Qf Rf hQR hRprim hQa hQpos hRpos, hdiscQ]
  have hcomp_prim : comp.IsPrimitive :=
    isPrimitive_composeForm Qf Rf hQR hQprim hRprim hQa hQpos hRpos
  exact reduceForm_mem_enum comp hcomp_disc hcomp_prim hcomp_pos

/-- The computable Gauss multiplication equals the Cox-transported
class-group law on reduced-form representatives
(both as `BinaryQuadraticForm` values). -/
theorem gaussMul_eq_reducedFormRepMul_val
    (hdneg : d < 0) (Q R : ReducedFormRep D) :
    gaussMul hdneg Q R = (reducedFormRepMul hdneg Q R).1 := by
  letI := formClassCommGroup hdneg
  let Qp : PrimitivePositiveDefiniteForm D := primitivePositiveDefiniteFormOfMemEnum Q.2
  let Rp : PrimitivePositiveDefiniteForm D := primitivePositiveDefiniteFormOfMemEnum R.2
  have hQprim : Q.1.IsPrimitive := Q.isPrimitive
  have hRprim : R.1.IsPrimitive := R.isPrimitive
  have hQpos : Q.1.IsPositiveDefinite := Q.isPositiveDefinite
  have hRpos : R.1.IsPositiveDefinite := R.isPositiveDefinite
  have hdiscQ : Q.1.disc = D := Q.disc_eq
  have hdiscR : R.1.disc = D := R.disc_eq
  have hQR : Q.1.disc = R.1.disc := by rw [hdiscQ, hdiscR]
  have hQa : Q.1.a ≠ 0 := ne_of_gt hQpos.1
  let compP : PrimitivePositiveDefiniteForm D :=
    composeFormPrimitiveOfCoprime hdneg Qp Rp hQR hRprim hQa hQpos hRpos
  let G : ReducedFormRep D := ⟨gaussMul hdneg Q R, mem_enum_of_gaussMul hdneg Q R⟩
  have hG_class :
      G.formClass =
        Quotient.mk (primitivePositiveDefiniteFormSetoid D) compP := by
    apply Quotient.sound
    change ProperEquivalent (primitivePositiveDefiniteFormOfMemEnum G.2).1 compP.1
    apply ProperEquivalent.symm
    unfold G gaussMul compP composeFormPrimitiveOfCoprime Qp Rp
    simpa using reduceForm_properEquivalent
      (composeForm Q.1 R.1 hQR hRprim hQa)
      (composeForm_isPositiveDefinite Q.1 R.1 hQR hRprim hQa hQpos hRpos)
  have hcomp_class :
      Quotient.mk (primitivePositiveDefiniteFormSetoid D) compP = Q.formClass * R.formClass := by
    letI : Fact (d < 0) := ⟨hdneg⟩
    simpa [Qp, Rp, ReducedFormRep.formClass] using
      composeForm_mk Qp Rp hQR hRprim hQa hQpos hRpos
  have hG_product : G.formClass = Q.formClass * R.formClass := hG_class.trans hcomp_class
  have hG_eq : G = reducedFormRepMul hdneg Q R := by
    calc
      G = reducedRepresentativeRep G.formClass := by
        exact (reducedRepresentativeRep_formClass_leftInverse G).symm
      _ = reducedRepresentativeRep (Q.formClass * R.formClass) := by
        rw [hG_product]
      _ = reducedFormRepMul hdneg Q R := by
        rfl
  exact congrArg Subtype.val hG_eq

/-- The computable Gauss multiplication, lifted to `ReducedFormRep`,
agrees with the Cox-transported law. -/
theorem gaussMul_eq_reducedFormRepMul
    (hdneg : d < 0) (Q R : ReducedFormRep D) :
    (⟨gaussMul hdneg Q R, mem_enum_of_gaussMul hdneg Q R⟩ : ReducedFormRep D) =
      reducedFormRepMul hdneg Q R := by
  apply Subtype.ext
  exact gaussMul_eq_reducedFormRepMul_val hdneg Q R

/-- Finite reduced-form representatives, with the transported multiplication,
are multiplicatively equivalent to the ideal class group. -/
noncomputable def reducedFormRepMulEquivClassGroup (hdneg : d < 0) :
    letI := reducedFormRepCommGroup hdneg
    ReducedFormRep (fieldDiscriminant d) ≃* ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  letI := reducedFormRepCommGroup hdneg
  refine
    { toEquiv := reducedFormRepEquivClassGroup hdneg
      map_mul' := ?_ }
  intro Q R
  simp [Equiv.mul_def]

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
set_option linter.hashCommand false

#eval composeAndReduce f2 f2
-- Expected: identity form `(1,0,21)`.
#guard composeAndReduce f2 f2 == f1

-- `#eval` the full pipeline on `(3,0,7) × (3,0,7)` (order-2 element).
#eval composeAndReduce f3 f3
#guard composeAndReduce f3 f3 == f1

-- `#eval` the full pipeline on `(5,4,5) × (5,4,5)` (order-2 element).
#eval composeAndReduce f4 f4
#guard composeAndReduce f4 f4 == f1

-- `#eval` the full pipeline on `(2,2,11) × (3,0,7)`.
#eval composeAndReduce f2 f3
-- Product of the two distinct non-identity elements gives the third.
#guard composeAndReduce f2 f3 == f4

-- `#eval` the full pipeline on `(2,2,11) × (5,4,5)`.
#eval composeAndReduce f2 f4
#guard composeAndReduce f2 f4 == f3

-- `#eval` the full pipeline on `(3,0,7) × (5,4,5)`.
#eval composeAndReduce f3 f4
#guard composeAndReduce f3 f4 == f2

-- Identity: `(1,0,21) × anything = anything`.
#eval composeAndReduce f1 f2
#guard composeAndReduce f1 f2 == f2
#eval composeAndReduce f1 f3
#guard composeAndReduce f1 f3 == f3
#eval composeAndReduce f1 f4
#guard composeAndReduce f1 f4 == f4

-- Full Klein four-group verified: all 10 non-trivial table entries match.
#guard composeAndReduce f1 f1 == f1

end Regression_d21

end BinaryQuadraticForm
end QuadraticNumberFields
