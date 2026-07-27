/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.FractionalIdeal.RingEquiv
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.ClassGroup.Ambiguous.Conjugation
import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.RingOfIntegers.Conj

/-!
# Conjugation Coboundary (Narrow Hilbert 90)

Norm-one / totally-positive principal multipliers are ordinary conjugation
coboundaries (Hilbert 90), and the coboundary representative can be chosen totally
positive.

The calculation threaded through the file is:
`I * (x) = τ(I) → |N(x)| = 1 → N(x) = 1 → x = y / τ(y)`,
then the representative is adjusted to a totally positive `z` with
`x = z / τ(z)`.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped nonZeroDivisors
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra

section Hilbert90

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
local notation "conjOK" => conjAutRingOfIntegers (Qsqrtd (d : ℚ))

private noncomputable abbrev qsqrtdConjFracRingEquiv :
    FractionRing (OK) ≃+* FractionRing (OK) :=
  (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv

/-- A totally positive fraction-field unit in `Q(√d)` has nonnegative field norm
after transport to the standard field model. -/
private theorem algebra_norm_nonneg_of_isTotallyPositive_fractionRing_algEquiv_qsqrtd
    {x : (FractionRing (OK))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (OK))) :
    0 ≤ Algebra.norm ℚ
      (FractionRing.algEquiv (OK)
        (Qsqrtd (d : ℚ))
        (x : FractionRing (OK))) := by
  let R := OK
  let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv R (Qsqrtd (d : ℚ))
  let z : Qsqrtd (d : ℚ) := e (x : FractionRing R)
  change 0 ≤ Algebra.norm ℚ z
  rw [Qsqrtd.algebraNorm_eq_qsqrtdNorm]
  by_cases hdneg : d < 0
  · exact Qsqrtd.norm_nonneg_of_neg hdneg z
  have hd_ne_zero : d ≠ 0 := Squarefree.ne_zero (Fact.out : Squarefree d)
  have hdpos : 0 < d := by omega
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hdpos
  have hzpos : ∀ σ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ, 0 < σ z := by
    intro σ
    simpa [z, e, R] using hxpos (σ.toRingHom.comp e.toRingHom)
  exact (Qsqrtd.norm_pos_of_forall_algHom_pos d hd_nonneg_real hzpos).le

/-- Norm-one extraction boundary. A totally positive principal multiplier
relating an ideal to its conjugate has field norm `1`.

From `I * (x) = τ(I)`, absolute norms give
`N(I) * |N_{K/ℚ}(x)| = N(τ(I)) = N(I)`, hence `|N_{K/ℚ}(x)| = 1`.
Total positivity rules out the negative sign, so `N_{K/ℚ}(x) = 1`. -/
private theorem norm_eq_one_of_tp_multiplier_to_conjAut
    (I : (Ideal (OK))⁰)
    {x : (FractionRing (OK))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (OK)))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (OK)) I *
          toPrincipalIdeal (OK)
            (FractionRing (OK)) x =
        FractionalIdeal.mk0
          (FractionRing (OK))
          (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    Algebra.norm ℚ
      (FractionRing.algEquiv (OK)
        (Qsqrtd (d : ℚ))
        (x : FractionRing (OK))) = 1 := by
  let R := OK
  let e := FractionRing.algEquiv R (Qsqrtd (d : ℚ))
  have habs_map_rat :
      (Ideal.absNorm
          (Ideal.map (conjOK : R →+* R)
            (I : Ideal R)) : ℚ) =
        Ideal.absNorm (I : Ideal R) := by
    exact_mod_cast
      (Ideal.absNorm_map_equiv conjOK (I : Ideal R))
  have hnorm_abs : |Algebra.norm ℚ (e (x : FractionRing R))| = 1 := by
    let E := FractionalIdeal.canonicalEquiv R⁰ (FractionRing R) (Qsqrtd (d : ℚ))
    have h :=
      congrArg
        (fun J : (FractionalIdeal R⁰ (FractionRing R))ˣ =>
          FractionalIdeal.absNorm (E (J : FractionalIdeal R⁰ (FractionRing R))))
        hconj
    have hIne : (Ideal.absNorm (I : Ideal R) : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Ideal.absNorm_pos_of_nonZeroDivisors I))
    have h' :
        (Ideal.absNorm (I : Ideal R) : ℚ) *
            |Algebra.norm ℚ (e (x : FractionRing R))| =
          (Ideal.absNorm (I : Ideal R) : ℚ) := by
      change
        FractionalIdeal.absNorm
            (E (((FractionalIdeal.mk0 (FractionRing R) I) *
              toPrincipalIdeal R (FractionRing R) x :
                (FractionalIdeal R⁰ (FractionRing R))ˣ) :
              FractionalIdeal R⁰ (FractionRing R))) =
          FractionalIdeal.absNorm
            (E ((FractionalIdeal.mk0 (FractionRing R)
                (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I) :
                  (FractionalIdeal R⁰ (FractionRing R))ˣ) :
              FractionalIdeal R⁰ (FractionRing R))) at h
      rw [Units.val_mul, map_mul, FractionalIdeal.absNorm.map_mul] at h
      simpa [R, e, E, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
        coe_toPrincipalIdeal, FractionalIdeal.canonicalEquiv_spanSingleton,
        FractionalIdeal.absNorm_span_singleton, coe_conjAutNonzeroIdealMulEquiv_apply,
        habs_map_rat] using h
    exact mul_left_cancel₀ hIne (by simpa using h')
  have hnorm_nonneg : 0 ≤ Algebra.norm ℚ (e (x : FractionRing R)) :=
    algebra_norm_nonneg_of_isTotallyPositive_fractionRing_algEquiv_qsqrtd d hxpos
  simpa [abs_of_nonneg hnorm_nonneg] using hnorm_abs

/-- Positivity adjustment boundary for the quadratic Hilbert-90 coboundary. If a
totally positive multiplier is an ordinary conjugation coboundary, the
coboundary representative can be chosen totally positive.

Starting from `x = y / τ(y)`, the proof also has `x * τ(x) = 1`. The
real-embedding positivity lemma replaces `y` by a totally positive `z` while
preserving the same coboundary equation `x = z / τ(z)`. -/
private theorem exists_totallyPositive_conjAut_coboundary_of_conjAut_coboundary
    {x y : (FractionRing (OK))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (OK)))
    (hy :
      x =
        y * (Units.mapEquiv (qsqrtdConjFracRingEquiv d) y)⁻¹) :
    ∃ z : (FractionRing (OK))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (z : FractionRing (OK)) ∧
        x =
          z *
            (Units.mapEquiv (qsqrtdConjFracRingEquiv d) z)⁻¹ := by
  let τ : FractionRing (OK) ≃+* FractionRing (OK) := qsqrtdConjFracRingEquiv d
  by_cases hreal : Nonempty (FractionRing (OK) →+* ℝ)
  · haveI : Nonempty (FractionRing (OK) →+* ℝ) := hreal
    have hττ_units :
        Units.mapEquiv (τ : FractionRing (OK) ≃* FractionRing (OK))
            (Units.mapEquiv (τ : FractionRing (OK) ≃* FractionRing (OK)) y) = y := by
      ext
      exact conjAutFractionRingAlgEquiv_apply_apply (Qsqrtd (d : ℚ))
        (y : FractionRing (OK))
    have hx_norm_units :
        x * Units.mapEquiv (τ : FractionRing (OK) ≃* FractionRing (OK)) x = 1 := by
      simp [hy, τ, hττ_units]
    have hx_norm : (x : FractionRing (OK)) * τ (x : FractionRing (OK)) = 1 := by
      simpa [τ] using congrArg Units.val hx_norm_units
    obtain ⟨z, hzpos, hz⟩ :=
      NarrowClassGroup.exists_positive_coboundary_of_mul_apply_eq_one
        (τ := τ) (a := x) hxpos hx_norm
    exact ⟨z, hzpos, Units.ext (by simpa [τ, div_eq_mul_inv] using hz)⟩
  · exact ⟨y, (fun σ ↦ False.elim (hreal ⟨σ⟩)), hy⟩

/-- Narrow Hilbert-90 boundary. A totally positive principal multiplier relating
an ideal to its conjugate is a totally positive conjugation coboundary.

In formulas, a totally positive `x` satisfying `I * (x) = τ(I)` is represented as
`x = y / τ(y)` for some totally positive fraction-field unit `y`. -/
theorem exists_totallyPositive_conjAut_coboundary_of_tp_multiplier_to_conjAut
    {I : (Ideal (OK))⁰}
    {x : (FractionRing (OK))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (OK)))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (OK)) I *
          toPrincipalIdeal (OK)
            (FractionRing (OK)) x =
        FractionalIdeal.mk0
          (FractionRing (OK))
          (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    ∃ y : (FractionRing (OK))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (y : FractionRing (OK)) ∧
        x =
          y *
            (Units.mapEquiv (qsqrtdConjFracRingEquiv d) y)⁻¹ := by
  obtain ⟨y, hy⟩ :=
    exists_conjAut_coboundary_of_norm_eq_one (Qsqrtd (d : ℚ))
      (norm_eq_one_of_tp_multiplier_to_conjAut d I hxpos hconj)
  exact exists_totallyPositive_conjAut_coboundary_of_conjAut_coboundary d hxpos hy

end Hilbert90

end Ambiguous
end ClassGroup
end QuadraticNumberFields
