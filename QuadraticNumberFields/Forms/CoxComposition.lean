/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.GaussCompositionClass
import QuadraticNumberFields.Forms.Structure

/-!
# Cox Ideal Multiplicativity for Concordant Gauss Composition

This file proves that Cox ideal classes multiply under direct concordant
Gauss composition. The shared algebra is kept in the generic
`QuadraticAlgebra ℤ DD bb` coordinate model before specializing to the two
integer-ring branches.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

namespace CoxComposition

open QuadraticNumberFields.CoxIdealRelation

section Generic

variable {DD bb A B C A' C' u : ℤ}

/-- If all four products of a pair of generators lie in an ideal, then the
product of the two generated pair ideals is contained in that ideal. -/
private theorem span_pair_mul_span_pair_le {R : Type*} [CommRing R]
    {a b c d : R} {K : Ideal R}
    (hac : a * c ∈ K) (had : a * d ∈ K)
    (hbc : b * c ∈ K) (hbd : b * d ∈ K) :
    Ideal.span ({a, b} : Set R) * Ideal.span ({c, d} : Set R) ≤ K := by
  rw [Ideal.mul_le]
  intro r hr s hs
  induction hr using Submodule.span_induction with
  | mem x hx =>
      rcases hx with rfl | rfl
      · induction hs using Submodule.span_induction with
        | mem y hy =>
            rcases hy with rfl | rfl
            · exact hac
            · exact had
        | zero => simp
        | add y z _ _ hy hz => simpa [mul_add] using K.add_mem hy hz
        | smul t y _ hy => simpa [mul_assoc, mul_comm, mul_left_comm] using K.mul_mem_left t hy
      · induction hs using Submodule.span_induction with
        | mem y hy =>
            rcases hy with rfl | rfl
            · exact hbc
            · exact hbd
        | zero => simp
        | add y z _ _ hy hz => simpa [mul_add] using K.add_mem hy hz
        | smul t y _ hy => simpa [mul_assoc, mul_comm, mul_left_comm] using K.mul_mem_left t hy
  | zero => simp
  | add y z _ _ hy hz => simpa [add_mul] using K.add_mem hy hz
  | smul t y _ hy => simpa [mul_assoc] using K.mul_mem_left t hy

/-- The product of two concordant Cox ideals in the generic
`QuadraticAlgebra ℤ DD bb` coordinate model is the Cox ideal attached to the
composed leading coefficient. -/
theorem coxIdeal_mul_of_concordant
    (hdiscQ : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD)
    (hdiscR : B ^ 2 - 4 * A' * C' = bb ^ 2 + 4 * DD)
    (hu : 2 * u = -(B + bb))
    (hcop : Int.gcd A A' = 1) :
    CoxIdealRelation.coxIdeal DD bb A u * CoxIdealRelation.coxIdeal DD bb A' u =
      CoxIdealRelation.coxIdeal DD bb (A * A') u := by
  let β : QuadraticAlgebra ℤ DD bb := ⟨u, 1⟩
  let K : Ideal (QuadraticAlgebra ℤ DD bb) := CoxIdealRelation.coxIdeal DD bb (A * A') u
  have hB : B = -2 * u - bb := by omega
  have hDD : DD = u ^ 2 + bb * u - A * C := by
    rw [hB] at hdiscQ
    nlinarith
  have hAC : A * C = A' * C' := by
    nlinarith [hdiscQ, hdiscR]
  have hbez : (1 : ℤ) = A * Int.gcdA A A' + A' * Int.gcdB A A' := by
    rw [← Int.gcd_eq_gcd_ab A A', hcop]
    norm_num
  have hA'_dvd_C : ∃ k : ℤ, C = A' * k := by
    refine ⟨C' * Int.gcdA A A' + C * Int.gcdB A A', ?_⟩
    calc
      C = 1 * C := by ring
      _ = (A * Int.gcdA A A' + A' * Int.gcdB A A') * C := by rw [← hbez]
      _ = A' * (C' * Int.gcdA A A' + C * Int.gcdB A A') := by
        rw [show (A * Int.gcdA A A' + A' * Int.gcdB A A') * C =
          (A * C) * Int.gcdA A A' + A' * C * Int.gcdB A A' by ring]
        rw [hAC]
        ring
  have hAA'_mem_K : (((A * A' : ℤ) : QuadraticAlgebra ℤ DD bb)) ∈ K := by
    exact CoxIdealRelation.self_mem_coxIdeal DD bb (A * A') u
  have hβ_mem_K : β ∈ K := by
    exact Ideal.subset_span (by simp [β])
  have hAβ_mem_K : ((A : QuadraticAlgebra ℤ DD bb) * β) ∈ K :=
    K.mul_mem_left (A : QuadraticAlgebra ℤ DD bb) hβ_mem_K
  have hA'β_mem_K : ((A' : QuadraticAlgebra ℤ DD bb) * β) ∈ K :=
    K.mul_mem_left (A' : QuadraticAlgebra ℤ DD bb) hβ_mem_K
  have hAC_mem_K : (((A * C : ℤ) : QuadraticAlgebra ℤ DD bb)) ∈ K := by
    rcases hA'_dvd_C with ⟨k, hk⟩
    have hmul :
        (((A * C : ℤ) : QuadraticAlgebra ℤ DD bb)) =
          (k : QuadraticAlgebra ℤ DD bb) *
            (((A * A' : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
      rw [hk]
      push_cast
      ring
    rw [hmul]
    exact K.mul_mem_left (k : QuadraticAlgebra ℤ DD bb) hAA'_mem_K
  have hβ_sq :
      β * β = -(B : QuadraticAlgebra ℤ DD bb) * β -
        (((A * C : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
    apply QuadraticAlgebra.ext
    · simp [β]
      rw [hB, hDD]
      ring
    · simp [β]
      rw [hB]
      ring
  apply le_antisymm
  · dsimp [CoxIdealRelation.coxIdeal]
    apply span_pair_mul_span_pair_le
    · change ((A : QuadraticAlgebra ℤ DD bb) * (A' : QuadraticAlgebra ℤ DD bb)) ∈ K
      simpa [Int.cast_mul] using hAA'_mem_K
    · change ((A : QuadraticAlgebra ℤ DD bb) * β) ∈ K
      exact hAβ_mem_K
    · change (β * (A' : QuadraticAlgebra ℤ DD bb)) ∈ K
      simpa [mul_comm] using hA'β_mem_K
    · change β * β ∈ K
      rw [hβ_sq]
      have hnegBβ : (-(B : QuadraticAlgebra ℤ DD bb) * β) ∈ K := by
        simpa [neg_mul] using
          K.neg_mem (K.mul_mem_left (B : QuadraticAlgebra ℤ DD bb) hβ_mem_K)
      exact K.sub_mem hnegBβ hAC_mem_K
  · intro z hz
    let P : Ideal (QuadraticAlgebra ℤ DD bb) :=
      CoxIdealRelation.coxIdeal DD bb A u * CoxIdealRelation.coxIdeal DD bb A' u
    change z ∈ P
    have hAA'_prod : (((A * A' : ℤ) : QuadraticAlgebra ℤ DD bb)) ∈ P := by
      have hA : ((A : QuadraticAlgebra ℤ DD bb)) ∈ CoxIdealRelation.coxIdeal DD bb A u :=
        CoxIdealRelation.self_mem_coxIdeal DD bb A u
      have hA' : ((A' : QuadraticAlgebra ℤ DD bb)) ∈
          CoxIdealRelation.coxIdeal DD bb A' u :=
        CoxIdealRelation.self_mem_coxIdeal DD bb A' u
      simpa [P, Int.cast_mul] using Ideal.mul_mem_mul hA hA'
    have hβ_prod : β ∈ P := by
      have hAβ : ((A : QuadraticAlgebra ℤ DD bb) * β) ∈ P := by
        have hA : ((A : QuadraticAlgebra ℤ DD bb)) ∈
            CoxIdealRelation.coxIdeal DD bb A u :=
          CoxIdealRelation.self_mem_coxIdeal DD bb A u
        have hβ' : β ∈ CoxIdealRelation.coxIdeal DD bb A' u :=
          Ideal.subset_span (by simp [β])
        simpa [P] using Ideal.mul_mem_mul hA hβ'
      have hA'β : ((A' : QuadraticAlgebra ℤ DD bb) * β) ∈ P := by
        have hβ : β ∈ CoxIdealRelation.coxIdeal DD bb A u :=
          Ideal.subset_span (by simp [β])
        have hA' : ((A' : QuadraticAlgebra ℤ DD bb)) ∈
            CoxIdealRelation.coxIdeal DD bb A' u :=
          CoxIdealRelation.self_mem_coxIdeal DD bb A' u
        simpa [P, mul_comm] using Ideal.mul_mem_mul hβ hA'
      have hlin :
          β =
            (Int.gcdA A A' : QuadraticAlgebra ℤ DD bb) *
                ((A : QuadraticAlgebra ℤ DD bb) * β) +
              (Int.gcdB A A' : QuadraticAlgebra ℤ DD bb) *
                ((A' : QuadraticAlgebra ℤ DD bb) * β) := by
        calc
          β = (1 : QuadraticAlgebra ℤ DD bb) * β := by simp
          _ =
              ((A * Int.gcdA A A' + A' * Int.gcdB A A' : ℤ) :
                  QuadraticAlgebra ℤ DD bb) * β := by rw [← hbez]; simp
          _ =
              (Int.gcdA A A' : QuadraticAlgebra ℤ DD bb) *
                  ((A : QuadraticAlgebra ℤ DD bb) * β) +
                (Int.gcdB A A' : QuadraticAlgebra ℤ DD bb) *
                  ((A' : QuadraticAlgebra ℤ DD bb) * β) := by
            push_cast
            ring
      rw [hlin]
      exact P.add_mem (P.mul_mem_left _ hAβ) (P.mul_mem_left _ hA'β)
    have hz' :
        z ∈ Ideal.span
          ({(((A * A' : ℤ) : QuadraticAlgebra ℤ DD bb)), β} :
            Set (QuadraticAlgebra ℤ DD bb)) := by
      simpa [K, CoxIdealRelation.coxIdeal, β] using hz
    exact Submodule.span_induction
      (p := fun x _ => x ∈ P)
      (fun x hx => by
        rcases hx with rfl | rfl
        · exact hAA'_prod
        · exact hβ_prod)
      P.zero_mem
      (fun _ _ _ _ hy hz => P.add_mem hy hz)
      (fun t _ _ hy => by simpa using P.mul_mem_left t hy)
      hz'

end Generic

end CoxComposition

namespace PrimitivePositiveDefiniteForm

private theorem comap_mul_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I J : Ideal S) :
    Ideal.comap (e : R →+* S) (I * J) =
      Ideal.comap (e : R →+* S) I * Ideal.comap (e : R →+* S) J := by
  apply_fun Ideal.map (e : R →+* S) using fun A B h =>
    calc
      A = Ideal.comap (e : R →+* S) (Ideal.map (e : R →+* S) A) := by
        rw [Ideal.comap_map_of_bijective (f := (e : R →+* S)) e.bijective]
      _ = Ideal.comap (e : R →+* S) (Ideal.map (e : R →+* S) B) := by rw [h]
      _ = B := by
        rw [Ideal.comap_map_of_bijective (f := (e : R →+* S)) e.bijective]
  rw [Ideal.map_comap_of_surjective (e : R →+* S) e.surjective]
  rw [Ideal.map_mul]
  rw [Ideal.map_comap_of_surjective (e : R →+* S) e.surjective]
  rw [Ideal.map_comap_of_surjective (e : R →+* S) e.surjective]

private theorem two_mul_neg_div_two_of_even {b : ℤ} (hb : Even b) :
    2 * ((-b) / 2) = -b := by
  rcases hb with ⟨k, hk⟩
  rw [hk]
  omega

private theorem two_mul_neg_succ_div_two_of_odd {b : ℤ} (hb : Odd b) :
    2 * (-(b + 1) / 2) = -(b + 1) := by
  rcases hb with ⟨k, hk⟩
  rw [hk]
  omega

/-- In the non-half-integral branch, Cox ideals multiply under direct
concordant Gauss composition. -/
theorem idealOfForm_composeConcordant_of_mod_four_ne_one
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (h : Q.1.IsConcordant R.1) :
    idealOfForm_of_mod_four_ne_one d hd4 (composeConcordant Q R h) =
      idealOfForm_of_mod_four_ne_one d hd4 Q *
        idealOfForm_of_mod_four_ne_one d hd4 R := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let u : ℤ := (-Q.1.b) / 2
  have hb_even : Even Q.1.b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
  have hu : 2 * u = -(Q.1.b + 0) := by
    simpa [u] using two_mul_neg_div_two_of_even hb_even
  have hdiscQ : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 0 ^ 2 + 4 * d := by
    simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
      fieldDiscriminant_of_mod_four_ne_one hd4] using Q.2.1
  have hdiscR : Q.1.b ^ 2 - 4 * R.1.a * R.1.c = 0 ^ 2 + 4 * d := by
    have hRdisc : R.1.b ^ 2 - 4 * R.1.a * R.1.c = 0 ^ 2 + 4 * d := by
      simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
        fieldDiscriminant_of_mod_four_ne_one hd4] using R.2.1
    simpa [h.2.1] using hRdisc
  have hcoord :
      CoxIdealRelation.coxIdeal d 0 Q.1.a u *
          CoxIdealRelation.coxIdeal d 0 R.1.a u =
        CoxIdealRelation.coxIdeal d 0 (Q.1.a * R.1.a) u :=
    CoxComposition.coxIdeal_mul_of_concordant hdiscQ hdiscR hu h.2.2
  calc
    idealOfForm_of_mod_four_ne_one d hd4 (composeConcordant Q R h)
        = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)
            (CoxIdealRelation.coxIdeal d 0 (Q.1.a * R.1.a) u) := by
          simp [idealOfForm_of_mod_four_ne_one, PrimitivePositiveDefiniteForm.composeConcordant,
            BinaryQuadraticForm.composeConcordant, CoxIdealRelation.coxIdeal, Int.cast_mul, e, u]
    _ = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)
          (CoxIdealRelation.coxIdeal d 0 Q.1.a u *
            CoxIdealRelation.coxIdeal d 0 R.1.a u) := by
          rw [hcoord]
    _ = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)
          (CoxIdealRelation.coxIdeal d 0 Q.1.a u) *
        Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)
          (CoxIdealRelation.coxIdeal d 0 R.1.a u) := by
          rw [comap_mul_of_ringEquiv]
    _ = idealOfForm_of_mod_four_ne_one d hd4 Q *
        idealOfForm_of_mod_four_ne_one d hd4 R := by
          simp [idealOfForm_of_mod_four_ne_one, CoxIdealRelation.coxIdeal, e, u, ← h.2.1]

/-- In the non-half-integral branch, Cox ideal classes multiply under direct
concordant Gauss composition. -/
theorem idealClassOfForm_composeConcordant_of_mod_four_ne_one
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (h : Q.1.IsConcordant R.1) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (composeConcordant Q R h) =
      idealClassOfForm_of_mod_four_ne_one d hd4 Q *
        idealClassOfForm_of_mod_four_ne_one d hd4 R := by
  unfold idealClassOfForm_of_mod_four_ne_one
  rw [← map_mul]
  apply congrArg ClassGroup.mk0
  apply Subtype.ext
  exact idealOfForm_composeConcordant_of_mod_four_ne_one hd4 Q R h

/-- In the half-integral branch, Cox ideals multiply under direct concordant
Gauss composition. -/
theorem idealOfForm_composeConcordant_of_mod_four_eq_one
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (h : Q.1.IsConcordant R.1) :
    idealOfForm_of_mod_four_eq_one d hd4 (composeConcordant Q R h) =
      idealOfForm_of_mod_four_eq_one d hd4 Q *
        idealOfForm_of_mod_four_eq_one d hd4 R := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let u : ℤ := -(Q.1.b + 1) / 2
  have hb_odd : Odd Q.1.b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
  have hu : 2 * u = -(Q.1.b + 1) := by
    simpa [u] using two_mul_neg_succ_div_two_of_odd hb_odd
  have hd_eq : d = 1 + 4 * (d / 4) := by omega
  have hdiscQ : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 1 ^ 2 + 4 * (d / 4) := by
    have hdisc_d : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = d := by
      simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
        fieldDiscriminant_of_mod_four_eq_one hd4] using Q.2.1
    omega
  have hdiscR : Q.1.b ^ 2 - 4 * R.1.a * R.1.c = 1 ^ 2 + 4 * (d / 4) := by
    have hRdisc : R.1.b ^ 2 - 4 * R.1.a * R.1.c = d := by
      simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
        fieldDiscriminant_of_mod_four_eq_one hd4] using R.2.1
    rw [← h.2.1] at hRdisc
    omega
  have hcoord :
      CoxIdealRelation.coxIdeal (d / 4) 1 Q.1.a u *
          CoxIdealRelation.coxIdeal (d / 4) 1 R.1.a u =
        CoxIdealRelation.coxIdeal (d / 4) 1 (Q.1.a * R.1.a) u :=
    CoxComposition.coxIdeal_mul_of_concordant hdiscQ hdiscR hu h.2.2
  calc
    idealOfForm_of_mod_four_eq_one d hd4 (composeConcordant Q R h)
        = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))
            (CoxIdealRelation.coxIdeal (d / 4) 1 (Q.1.a * R.1.a) u) := by
          simp [idealOfForm_of_mod_four_eq_one, PrimitivePositiveDefiniteForm.composeConcordant,
            BinaryQuadraticForm.composeConcordant, CoxIdealRelation.coxIdeal, Int.cast_mul, e, u]
    _ = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))
          (CoxIdealRelation.coxIdeal (d / 4) 1 Q.1.a u *
            CoxIdealRelation.coxIdeal (d / 4) 1 R.1.a u) := by
          rw [hcoord]
    _ = Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))
          (CoxIdealRelation.coxIdeal (d / 4) 1 Q.1.a u) *
        Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))
          (CoxIdealRelation.coxIdeal (d / 4) 1 R.1.a u) := by
          rw [comap_mul_of_ringEquiv]
    _ = idealOfForm_of_mod_four_eq_one d hd4 Q *
        idealOfForm_of_mod_four_eq_one d hd4 R := by
          simp [idealOfForm_of_mod_four_eq_one, CoxIdealRelation.coxIdeal, e, u, ← h.2.1]

/-- In the half-integral branch, Cox ideal classes multiply under direct
concordant Gauss composition. -/
theorem idealClassOfForm_composeConcordant_of_mod_four_eq_one
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (h : Q.1.IsConcordant R.1) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (composeConcordant Q R h) =
      idealClassOfForm_of_mod_four_eq_one d hd4 Q *
        idealClassOfForm_of_mod_four_eq_one d hd4 R := by
  unfold idealClassOfForm_of_mod_four_eq_one
  rw [← map_mul]
  apply congrArg ClassGroup.mk0
  apply Subtype.ext
  exact idealOfForm_composeConcordant_of_mod_four_eq_one hd4 Q R h

/-- Branch-independent Cox-map version of ideal-class multiplicativity for
direct concordant Gauss composition. -/
theorem formClassToClassGroup_composeConcordant
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (h : Q.1.IsConcordant R.1) :
    formClassToClassGroup d
        (Quotient.mk (primitivePositiveDefiniteFormSetoid _) (composeConcordant Q R h)) =
      formClassToClassGroup d
          (Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q) *
        formClassToClassGroup d
          (Quotient.mk (primitivePositiveDefiniteFormSetoid _) R) := by
  by_cases hd4 : d % 4 = 1
  · rw [formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4]
    rw [formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4]
    rw [formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4]
    exact idealClassOfForm_composeConcordant_of_mod_four_eq_one hd4 Q R h
  · rw [formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4]
    rw [formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4]
    rw [formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4]
    exact idealClassOfForm_composeConcordant_of_mod_four_ne_one hd4 Q R h

end PrimitivePositiveDefiniteForm

namespace FormClass

/-- The Cox map sends chosen-representative concordant composition to the product
of the Cox images of the input classes. -/
theorem formClassToClassGroup_composeConcordantOfRepresentatives
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (h : Q.1.IsConcordant R.1) :
    formClassToClassGroup d (composeConcordantOfRepresentatives Q R h) =
      formClassToClassGroup d
          (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q) *
        formClassToClassGroup d
          (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R) := by
  unfold composeConcordantOfRepresentatives
  exact PrimitivePositiveDefiniteForm.formClassToClassGroup_composeConcordant Q R h

/-- Chosen-representative concordant composition agrees with the transported
product on form classes. -/
theorem composeConcordantOfRepresentatives_eq_mul
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (h : Q.1.IsConcordant R.1) :
    composeConcordantOfRepresentatives Q R h =
      @Mul.mul (FormClass (fieldDiscriminant d)) (formClassCommGroup hdneg).toMul
        (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q :
          FormClass (fieldDiscriminant d))
        (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R :
          FormClass (fieldDiscriminant d)) := by
  letI := formClassCommGroup hdneg
  apply (formClassEquivClassGroup hdneg).injective
  change formClassToClassGroup d (composeConcordantOfRepresentatives Q R h) =
    formClassToClassGroup d
      (@Mul.mul (FormClass (fieldDiscriminant d)) (formClassCommGroup hdneg).toMul
        (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q :
          FormClass (fieldDiscriminant d))
        (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R :
          FormClass (fieldDiscriminant d)))
  rw [formClassToClassGroup_composeConcordantOfRepresentatives]
  exact (formClassEquivClassGroup_mul hdneg
    (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q)
    (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R)).symm

/-- Chosen-representative concordant composition is independent of the chosen
concordant representatives for the same two form classes. -/
theorem composeConcordantOfRepresentatives_eq_of_mk_eq
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    {Q₁ Q₂ R₁ R₂ : PrimitivePositiveDefiniteForm (fieldDiscriminant d)}
    (hQ : (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q₁ :
        FormClass (fieldDiscriminant d)) =
      Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q₂)
    (hR : (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R₁ :
        FormClass (fieldDiscriminant d)) =
      Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R₂)
    (h₁ : Q₁.1.IsConcordant R₁.1)
    (h₂ : Q₂.1.IsConcordant R₂.1) :
    composeConcordantOfRepresentatives Q₁ R₁ h₁ =
      composeConcordantOfRepresentatives Q₂ R₂ h₂ := by
  rw [composeConcordantOfRepresentatives_eq_mul hdneg Q₁ R₁ h₁,
    composeConcordantOfRepresentatives_eq_mul hdneg Q₂ R₂ h₂, hQ, hR]

end FormClass

end BinaryQuadraticForm
end QuadraticNumberFields
