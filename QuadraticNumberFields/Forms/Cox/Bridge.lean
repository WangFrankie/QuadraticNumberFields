/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Core.Class
import BinaryQuadraticForms.Core.ClassReduced
import BinaryQuadraticForms.Cox.IdealRelation
import QuadraticNumberFields.RingOfIntegers.Classification
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.ClassGroup

/-!
# Cox 7.7 Bridge from Forms to Ideal Classes

This module builds the imaginary-side Cox 7.7 bridge from primitive positive
definite form classes to ideal classes of the ring of integers of `ℚ(√d)`.
The form-class carrier and reduction interface live in `Forms.Core.Class` and
`Forms.Core.ClassReduced`; the shared ideal-relation algebra lives in
`Forms.Cox.IdealRelation`.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## Cox 7.7 class-group bridge -/

private theorem comap_span_singleton_mul_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : S) (I : Ideal S) :
    Ideal.comap (e : R →+* S) (Ideal.span ({x} : Set S) * I) =
      Ideal.span ({e.symm x} : Set R) * Ideal.comap (e : R →+* S) I := by
  have hmap_inj : Function.Injective (fun J : Ideal R => Ideal.map (e : R →+* S) J) := by
    intro J K hJK
    have h := congrArg (fun L : Ideal S => Ideal.map (e.symm : S →+* R) L) hJK
    simpa using h
  apply hmap_inj
  change Ideal.map (e : R →+* S)
      (Ideal.comap (e : R →+* S) (Ideal.span ({x} : Set S) * I)) =
    Ideal.map (e : R →+* S)
      (Ideal.span ({e.symm x} : Set R) * Ideal.comap (e : R →+* S) I)
  rw [Ideal.map_comap_of_surjective (f := (e : R →+* S)) e.surjective]
  rw [Ideal.map_mul]
  rw [Ideal.map_comap_of_surjective (f := (e : R →+* S)) e.surjective]
  rw [Ideal.map_span]
  simp

private theorem two_mul_neg_div_two_of_even {b : ℤ} (hb : Even b) : 2 * ((-b) / 2) = -b := by
  rcases hb with ⟨k, hk⟩
  omega

private theorem two_mul_neg_succ_div_two_of_odd {b : ℤ} (hb : Odd b) :
    2 * (-(b + 1) / 2) = -(b + 1) := by
  rcases hb with ⟨k, hk⟩
  omega

private theorem sl2z_det_fin_two (g : SL2Z) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  simpa using h

private theorem cox_zsqrtd_lam_ne_zero {D A p q r s u : ℤ}
    (hA : A ≠ 0) (hdet : p * s - q * r = 1) :
    (((p * A : ℤ) : Zsqrtd D) - (r : Zsqrtd D) * (⟨u, 1⟩ : Zsqrtd D)) ≠ 0 :=
  CoxIdealRelation.lam_ne_zero (DD := D) (bb := 0) hA hdet

private theorem cox_zsqrtd_ideal_relation {D A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hdisc : B ^ 2 - 4 * A * C = 4 * D)
    (hu : 2 * u = -B)
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s)) :
    Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : Zsqrtd D)} :
          Set (Zsqrtd D)) *
      Ideal.span ({(A : Zsqrtd D), (⟨u, 1⟩ : Zsqrtd D)} : Set (Zsqrtd D)) =
    Ideal.span
        ({(((p * A : ℤ) : Zsqrtd D) - (r : Zsqrtd D) * (⟨u, 1⟩ : Zsqrtd D))} :
          Set (Zsqrtd D)) *
      Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : Zsqrtd D),
          (⟨v, 1⟩ : Zsqrtd D)} : Set (Zsqrtd D)) :=
  CoxIdealRelation.ideal_relation (DD := D) (bb := 0) hdet (by simpa using hdisc)
    (by simpa using hu) (by simpa using hv)

private theorem cox_zsqrtd_ideal_relation_transform_of_mod_four_ne_one
    {d : ℤ} (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z) :
    Ideal.span ({(((transform Q.1 g).a : ℤ) : Zsqrtd d)} : Set (Zsqrtd d)) *
      Ideal.span
        ({((Q.1.a : ℤ) : Zsqrtd d), (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)} :
          Set (Zsqrtd d)) =
    Ideal.span
        ({(((g 0 0 * Q.1.a : ℤ) : Zsqrtd d) -
          (g 1 0 : Zsqrtd d) * (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d))} :
          Set (Zsqrtd d)) *
      Ideal.span
        ({(((transform Q.1 g).a : ℤ) : Zsqrtd d),
          (⟨(-(transform Q.1 g).b) / 2, 1⟩ : Zsqrtd d)} :
          Set (Zsqrtd d)) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := sl2z_det_fin_two g
  have hdisc : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 4 * d := by
    simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using Q.2.1
  have hb_even : Even Q.1.b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
  have hdisc_transform : (transform Q.1 g).HasDiscriminant (fieldDiscriminant d) := by
    simpa [HasDiscriminant, disc_transform] using Q.2.1
  have hb_transform_even : Even (transform Q.1 g).b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 hdisc_transform
  have hu : 2 * ((-Q.1.b) / 2) = -Q.1.b :=
    two_mul_neg_div_two_of_even hb_even
  have hv : 2 * ((-(transform Q.1 g).b) / 2) =
      -(2 * Q.1.a * g 0 0 * g 0 1 +
        Q.1.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) + 2 * Q.1.c * g 1 0 * g 1 1) := by
    simpa [transform_b] using two_mul_neg_div_two_of_even hb_transform_even
  simpa [transform_a] using
    cox_zsqrtd_ideal_relation (D := d) (A := Q.1.a) (B := Q.1.b) (C := Q.1.c)
      (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1)
      (u := (-Q.1.b) / 2) (v := (-(transform Q.1 g).b) / 2)
      hdet hdisc hu hv

private theorem cox_zomega_ideal_relation {k A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hdisc : B ^ 2 - 4 * A * C = 1 + 4 * k)
    (hu : 2 * u = -(B + 1))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + 1)) :
    Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : ZOnePlusSqrtdOverTwo k)} :
          Set (ZOnePlusSqrtdOverTwo k)) *
      Ideal.span
        ({(A : ZOnePlusSqrtdOverTwo k), (⟨u, 1⟩ : ZOnePlusSqrtdOverTwo k)} :
          Set (ZOnePlusSqrtdOverTwo k)) =
    Ideal.span
        ({(((p * A : ℤ) : ZOnePlusSqrtdOverTwo k) -
          (r : ZOnePlusSqrtdOverTwo k) * (⟨u, 1⟩ : ZOnePlusSqrtdOverTwo k))} :
          Set (ZOnePlusSqrtdOverTwo k)) *
      Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : ZOnePlusSqrtdOverTwo k),
          (⟨v, 1⟩ : ZOnePlusSqrtdOverTwo k)} : Set (ZOnePlusSqrtdOverTwo k)) :=
  CoxIdealRelation.ideal_relation (DD := k) (bb := 1) hdet (by simpa using hdisc)
    (by simpa using hu) (by simpa [add_comm] using hv)

private theorem cox_zomega_ideal_relation_transform_of_mod_four_eq_one
    {d : ℤ} (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z) :
    Ideal.span
        ({(((transform Q.1 g).a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))) *
      Ideal.span
        ({((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
          (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))) =
    Ideal.span
        ({(((g 0 0 * Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) -
          (g 1 0 : ZOnePlusSqrtdOverTwo (d / 4)) *
            (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4)))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))) *
      Ideal.span
        ({(((transform Q.1 g).a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
          (⟨-((transform Q.1 g).b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := sl2z_det_fin_two g
  have hdisc_d : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = d := by
    simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using Q.2.1
  have hd_eq : d = 1 + 4 * (d / 4) := by omega
  have hdisc : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 1 + 4 * (d / 4) :=
    hdisc_d.trans hd_eq
  have hb_odd : Odd Q.1.b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
  have hdisc_transform : (transform Q.1 g).HasDiscriminant (fieldDiscriminant d) := by
    simpa [HasDiscriminant, disc_transform] using Q.2.1
  have hb_transform_odd : Odd (transform Q.1 g).b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 hdisc_transform
  have hu : 2 * (-(Q.1.b + 1) / 2) = -(Q.1.b + 1) :=
    two_mul_neg_succ_div_two_of_odd hb_odd
  have hv : 2 * (-((transform Q.1 g).b + 1) / 2) =
      -(2 * Q.1.a * g 0 0 * g 0 1 +
        Q.1.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) + 2 * Q.1.c * g 1 0 * g 1 1 +
          1) := by
    simpa [transform_b] using two_mul_neg_succ_div_two_of_odd hb_transform_odd
  simpa [transform_a] using
    cox_zomega_ideal_relation (k := d / 4) (A := Q.1.a) (B := Q.1.b) (C := Q.1.c)
      (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1)
      (u := -(Q.1.b + 1) / 2) (v := -((transform Q.1 g).b + 1) / 2)
      hdet hdisc hu hv

private theorem cox_zomega_lam_ne_zero {k A p q r s u : ℤ}
    (hA : A ≠ 0) (hdet : p * s - q * r = 1) :
    (((p * A : ℤ) : ZOnePlusSqrtdOverTwo k) -
      (r : ZOnePlusSqrtdOverTwo k) * (⟨u, 1⟩ : ZOnePlusSqrtdOverTwo k)) ≠ 0 :=
  CoxIdealRelation.lam_ne_zero (DD := k) (bb := 1) hA hdet

/-- The Cox ideal `(a, (-b + √D) / 2)` in the `d % 4 ≠ 1` branch, transported
from the `Zsqrtd d` model back to the ring of integers of `Qsqrtd d`.

For forms of discriminant `fieldDiscriminant d = 4 * d`, the second generator is
represented in `Zsqrtd d` by `(-b / 2) + √d`. The divisibility-by-two fact is a
property of the discriminant hypotheses and is intentionally left to later Cox
bridge lemmas rather than baked into this definition. -/
noncomputable def idealOfForm_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    Ideal (𝓞 (Qsqrtd (d : ℚ))) :=
  Ideal.comap
    (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4).toRingHom
    (Ideal.span
      ({((Q.1.a : ℤ) : Zsqrtd d), (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)} :
        Set (Zsqrtd d)))

/-- The Cox ideal relation in the ring of integers for a proper transform in
the `d % 4 ≠ 1` branch.  If `R = Q ∘ g`, then the transformed leading
coefficient and the Cox multiplier `λ` give the principal-ideal identity
relating the Cox ideals attached to `Q` and `R`. -/
theorem cox_ringOfIntegers_ideal_relation_transform_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z)
    (hR : R.1 = transform Q.1 g) :
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    let lam : Zsqrtd d :=
      ((g 0 0 * Q.1.a : ℤ) : Zsqrtd d) -
        (g 1 0 : Zsqrtd d) * (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
    Ideal.span ({e.symm (((R.1.a : ℤ) : Zsqrtd d))} :
        Set (𝓞 (Qsqrtd (d : ℚ)))) *
      idealOfForm_of_mod_four_ne_one d hd4 Q =
    Ideal.span ({e.symm lam} : Set (𝓞 (Qsqrtd (d : ℚ)))) *
      idealOfForm_of_mod_four_ne_one d hd4 R := by
  intro e lam
  have hcoord := cox_zsqrtd_ideal_relation_transform_of_mod_four_ne_one hd4 Q g
  have hcomap := congrArg (Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)) hcoord
  rw [comap_span_singleton_mul_of_ringEquiv e (((transform Q.1 g).a : ℤ) : Zsqrtd d)
      (Ideal.span
        ({((Q.1.a : ℤ) : Zsqrtd d), (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)} :
          Set (Zsqrtd d)))] at hcomap
  rw [comap_span_singleton_mul_of_ringEquiv e lam
      (Ideal.span
        ({(((transform Q.1 g).a : ℤ) : Zsqrtd d),
          (⟨(-(transform Q.1 g).b) / 2, 1⟩ : Zsqrtd d)} :
          Set (Zsqrtd d)))] at hcomap
  simpa [idealOfForm_of_mod_four_ne_one, hR] using hcomap

/-- The Cox ideal `(a, (-b + √d) / 2)` in the `d % 4 = 1` branch, transported
from the `ZOnePlusSqrtdOverTwo (d / 4)` model back to the ring of integers of
`Qsqrtd d`.

In the basis `1, ω` with `ω = (1 + √d) / 2`, the second generator has coordinates
`(-(b + 1) / 2, 1)`. The oddness of `b` follows from the discriminant hypotheses
and is left as a later Cox bridge lemma. -/
noncomputable def idealOfForm_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    Ideal (𝓞 (Qsqrtd (d : ℚ))) :=
  Ideal.comap
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4).toRingHom
    (Ideal.span
      ({((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
        (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
        Set (ZOnePlusSqrtdOverTwo (d / 4))))

/-- The Cox ideal relation in the ring of integers for a proper transform in
the `d % 4 = 1` branch.  This is the half-integral analogue of
`cox_ringOfIntegers_ideal_relation_transform_of_mod_four_ne_one`. -/
theorem cox_ringOfIntegers_ideal_relation_transform_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z)
    (hR : R.1 = transform Q.1 g) :
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
    let lam : ZOnePlusSqrtdOverTwo (d / 4) :=
      ((g 0 0 * Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) -
        (g 1 0 : ZOnePlusSqrtdOverTwo (d / 4)) *
          (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))
    Ideal.span ({e.symm (((R.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)))} :
        Set (𝓞 (Qsqrtd (d : ℚ)))) *
      idealOfForm_of_mod_four_eq_one d hd4 Q =
    Ideal.span ({e.symm lam} : Set (𝓞 (Qsqrtd (d : ℚ)))) *
      idealOfForm_of_mod_four_eq_one d hd4 R := by
  intro e lam
  have hcoord := cox_zomega_ideal_relation_transform_of_mod_four_eq_one hd4 Q g
  have hcomap := congrArg
    (Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))) hcoord
  rw [comap_span_singleton_mul_of_ringEquiv e
      (((transform Q.1 g).a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))
      (Ideal.span
        ({((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
          (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))))] at hcomap
  rw [comap_span_singleton_mul_of_ringEquiv e lam
      (Ideal.span
        ({(((transform Q.1 g).a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
          (⟨-((transform Q.1 g).b + 1) / 2, 1⟩ :
            ZOnePlusSqrtdOverTwo (d / 4))} : Set (ZOnePlusSqrtdOverTwo (d / 4))))] at hcomap
  simpa [idealOfForm_of_mod_four_eq_one, hR] using hcomap

/-- The Cox ideal in the `d % 4 ≠ 1` branch is nonzero, because it contains the
nonzero positive integer coefficient `a`. -/
theorem idealOfForm_of_mod_four_ne_one_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    idealOfForm_of_mod_four_ne_one d hd4 Q ≠ 0 := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let x : 𝓞 (Qsqrtd (d : ℚ)) := e.symm ((Q.1.a : Zsqrtd d))
  have hxmem : x ∈ idealOfForm_of_mod_four_ne_one d hd4 Q := by
    change e x ∈ Ideal.span
      ({((Q.1.a : ℤ) : Zsqrtd d), (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)} :
        Set (Zsqrtd d))
    rw [show e x = ((Q.1.a : ℤ) : Zsqrtd d) by simp [x, e]]
    exact Ideal.subset_span (by simp)
  intro hI
  have hxzero : x = 0 := by
    have hxmem0 : x ∈ (0 : Ideal (𝓞 (Qsqrtd (d : ℚ)))) := by
      simpa [hI] using hxmem
    simpa using hxmem0
  have haZ : ((Q.1.a : ℤ) : Zsqrtd d) = 0 := by
    have := congrArg e hxzero
    simpa [x, e] using this
  have ha0 : Q.1.a = 0 := by
    exact_mod_cast congrArg QuadraticAlgebra.re haZ
  exact (ne_of_gt Q.2.2.2.1) ha0

/-- The Cox ideal in the `d % 4 = 1` branch is nonzero, because it contains the
nonzero positive integer coefficient `a`. -/
theorem idealOfForm_of_mod_four_eq_one_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    idealOfForm_of_mod_four_eq_one d hd4 Q ≠ 0 := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let x : 𝓞 (Qsqrtd (d : ℚ)) :=
    e.symm ((Q.1.a : ZOnePlusSqrtdOverTwo (d / 4)))
  have hxmem : x ∈ idealOfForm_of_mod_four_eq_one d hd4 Q := by
    change e x ∈ Ideal.span
      ({((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
        (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
        Set (ZOnePlusSqrtdOverTwo (d / 4)))
    rw [show e x = ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) by simp [x, e]]
    exact Ideal.subset_span (by simp)
  intro hI
  have hxzero : x = 0 := by
    have hxmem0 : x ∈ (0 : Ideal (𝓞 (Qsqrtd (d : ℚ)))) := by
      simpa [hI] using hxmem
    simpa using hxmem0
  have haZ : ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) = 0 := by
    have := congrArg e hxzero
    simpa [x, e] using this
  have ha0 : Q.1.a = 0 := by
    exact_mod_cast congrArg QuadraticAlgebra.re haZ
  exact (ne_of_gt Q.2.2.2.1) ha0

/-- The Cox ideal in the `d % 4 ≠ 1` branch as a nonzero ideal. -/
noncomputable def nonzeroIdealOfForm_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))) :=
  ⟨idealOfForm_of_mod_four_ne_one d hd4 Q,
    mem_nonZeroDivisors_iff_ne_zero.mpr
      (idealOfForm_of_mod_four_ne_one_ne_zero d hd4 Q)⟩

/-- The Cox ideal in the `d % 4 = 1` branch as a nonzero ideal. -/
noncomputable def nonzeroIdealOfForm_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))) :=
  ⟨idealOfForm_of_mod_four_eq_one d hd4 Q,
    mem_nonZeroDivisors_iff_ne_zero.mpr
      (idealOfForm_of_mod_four_eq_one_ne_zero d hd4 Q)⟩

/-- The ideal class attached to a single primitive positive definite form in the
`d % 4 ≠ 1` branch, used as the representative-level input for the descended
`FormClass` map. -/
noncomputable def idealClassOfForm_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) :=
  ClassGroup.mk0 (nonzeroIdealOfForm_of_mod_four_ne_one d hd4 Q)

/-- The ideal class attached to a single primitive positive definite form in the
`d % 4 = 1` branch, used as the representative-level input for the descended
`FormClass` map. -/
noncomputable def idealClassOfForm_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) :=
  ClassGroup.mk0 (nonzeroIdealOfForm_of_mod_four_eq_one d hd4 Q)

/-- Properly transforming a form does not change the associated Cox ideal class
in the `d % 4 ≠ 1` branch, in the representative-level form where the
transforming matrix is specified. -/
theorem idealClassOfForm_of_mod_four_ne_one_eq_of_transform
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z)
    (hR : R.1 = transform Q.1 g) :
    idealClassOfForm_of_mod_four_ne_one d hd4 Q =
      idealClassOfForm_of_mod_four_ne_one d hd4 R := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let lam : Zsqrtd d :=
    ((g 0 0 * Q.1.a : ℤ) : Zsqrtd d) -
      (g 1 0 : Zsqrtd d) * (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
  let x : 𝓞 (Qsqrtd (d : ℚ)) := e.symm (((R.1.a : ℤ) : Zsqrtd d))
  let y : 𝓞 (Qsqrtd (d : ℚ)) := e.symm lam
  have hx : x ≠ 0 := by
    intro hx0
    have hxZ : (((R.1.a : ℤ) : Zsqrtd d)) = 0 := by
      have := congrArg e hx0
      simpa [x, e] using this
    have ha0 : R.1.a = 0 := by
      exact_mod_cast congrArg QuadraticAlgebra.re hxZ
    exact (ne_of_gt R.2.2.2.1) ha0
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := sl2z_det_fin_two g
  have hlam : lam ≠ 0 :=
    cox_zsqrtd_lam_ne_zero (D := d) (A := Q.1.a) (p := g 0 0)
      (q := g 0 1) (r := g 1 0) (s := g 1 1) (u := (-Q.1.b) / 2)
      (ne_of_gt Q.2.2.2.1) hdet
  have hy : y ≠ 0 := by
    intro hy0
    apply hlam
    have := congrArg e hy0
    simpa [y, e] using this
  have hideal :=
    cox_ringOfIntegers_ideal_relation_transform_of_mod_four_ne_one d hd4 Q R g hR
  unfold idealClassOfForm_of_mod_four_ne_one
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa [x, y, lam, nonzeroIdealOfForm_of_mod_four_ne_one] using hideal

/-- Properly equivalent forms have the same associated Cox ideal class in the
`d % 4 ≠ 1` branch. -/
theorem idealClassOfForm_of_mod_four_ne_one_eq_of_properEquivalent
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : PrimitivePositiveDefiniteForm.ProperEquivalent Q R) :
    idealClassOfForm_of_mod_four_ne_one d hd4 Q =
      idealClassOfForm_of_mod_four_ne_one d hd4 R := by
  rcases hQR with ⟨g, hg⟩
  exact idealClassOfForm_of_mod_four_ne_one_eq_of_transform d hd4 Q R g hg.symm

/-- Properly transforming a form does not change the associated Cox ideal class
in the `d % 4 = 1` branch, in the representative-level form where the
transforming matrix is specified. -/
theorem idealClassOfForm_of_mod_four_eq_one_eq_of_transform
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z)
    (hR : R.1 = transform Q.1 g) :
    idealClassOfForm_of_mod_four_eq_one d hd4 Q =
      idealClassOfForm_of_mod_four_eq_one d hd4 R := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let lam : ZOnePlusSqrtdOverTwo (d / 4) :=
    ((g 0 0 * Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) -
      (g 1 0 : ZOnePlusSqrtdOverTwo (d / 4)) *
        (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))
  let x : 𝓞 (Qsqrtd (d : ℚ)) :=
    e.symm (((R.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)))
  let y : 𝓞 (Qsqrtd (d : ℚ)) := e.symm lam
  have hx : x ≠ 0 := by
    intro hx0
    have hxZ : (((R.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))) = 0 := by
      have := congrArg e hx0
      simpa [x, e] using this
    have ha0 : R.1.a = 0 := by
      exact_mod_cast congrArg QuadraticAlgebra.re hxZ
    exact (ne_of_gt R.2.2.2.1) ha0
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := sl2z_det_fin_two g
  have hlam : lam ≠ 0 :=
    cox_zomega_lam_ne_zero (k := d / 4) (A := Q.1.a) (p := g 0 0)
      (q := g 0 1) (r := g 1 0) (s := g 1 1) (u := -(Q.1.b + 1) / 2)
      (ne_of_gt Q.2.2.2.1) hdet
  have hy : y ≠ 0 := by
    intro hy0
    apply hlam
    have := congrArg e hy0
    simpa [y, e] using this
  have hideal :=
    cox_ringOfIntegers_ideal_relation_transform_of_mod_four_eq_one d hd4 Q R g hR
  unfold idealClassOfForm_of_mod_four_eq_one
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa [x, y, lam, nonzeroIdealOfForm_of_mod_four_eq_one] using hideal

/-- Properly equivalent forms have the same associated Cox ideal class in the
`d % 4 = 1` branch. -/
theorem idealClassOfForm_of_mod_four_eq_one_eq_of_properEquivalent
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : PrimitivePositiveDefiniteForm.ProperEquivalent Q R) :
    idealClassOfForm_of_mod_four_eq_one d hd4 Q =
      idealClassOfForm_of_mod_four_eq_one d hd4 R := by
  rcases hQR with ⟨g, hg⟩
  exact idealClassOfForm_of_mod_four_eq_one_eq_of_transform d hd4 Q R g hg.symm

/-- Map from form classes to ideal classes in the `d % 4 ≠ 1` branch. -/
noncomputable def formClassToClassGroup_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1) :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  exact Quotient.lift (idealClassOfForm_of_mod_four_ne_one d hd4)
    (idealClassOfForm_of_mod_four_ne_one_eq_of_properEquivalent d hd4)

/-- Map from form classes to ideal classes in the `d % 4 = 1` branch. -/
noncomputable def formClassToClassGroup_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1) :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  exact Quotient.lift (idealClassOfForm_of_mod_four_eq_one d hd4)
    (idealClassOfForm_of_mod_four_eq_one_eq_of_properEquivalent d hd4)

/-- Cox map from primitive positive definite form classes to ideal classes,
dispatching between the two integer-ring models by the field discriminant
congruence. -/
noncomputable def formClassToClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  by_cases hd4 : d % 4 = 1
  · exact formClassToClassGroup_of_mod_four_eq_one d hd4
  · exact formClassToClassGroup_of_mod_four_ne_one d hd4

theorem formClassToClassGroup_eq_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1) :
    formClassToClassGroup d = formClassToClassGroup_of_mod_four_eq_one d hd4 := by
  simp [formClassToClassGroup, hd4]

theorem formClassToClassGroup_eq_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1) :
    formClassToClassGroup d = formClassToClassGroup_of_mod_four_ne_one d hd4 := by
  simp [formClassToClassGroup, hd4]

/-- On a form representative, the branch-independent Cox map computes to the
explicit Cox ideal class in the `d % 4 ≠ 1` branch. -/
theorem formClassToClassGroup_mk_eq_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    formClassToClassGroup d (Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q) =
      idealClassOfForm_of_mod_four_ne_one d hd4 Q := by
  rw [formClassToClassGroup_eq_of_mod_four_ne_one d hd4]
  rfl

/-- On a form representative, the branch-independent Cox map computes to the
explicit Cox ideal class in the `d % 4 = 1` branch. -/
theorem formClassToClassGroup_mk_eq_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    formClassToClassGroup d (Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q) =
      idealClassOfForm_of_mod_four_eq_one d hd4 Q := by
  rw [formClassToClassGroup_eq_of_mod_four_eq_one d hd4]
  rfl

end BinaryQuadraticForm
end QuadraticNumberFields
