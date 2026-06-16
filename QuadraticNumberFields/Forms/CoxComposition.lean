/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.GaussCompositionClass

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
    coxIdeal DD bb A u * coxIdeal DD bb A' u =
      coxIdeal DD bb (A * A') u := by
  let β : QuadraticAlgebra ℤ DD bb := ⟨u, 1⟩
  let K : Ideal (QuadraticAlgebra ℤ DD bb) := coxIdeal DD bb (A * A') u
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
    exact self_mem_coxIdeal DD bb (A * A') u
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
  · dsimp [coxIdeal]
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
    let P : Ideal (QuadraticAlgebra ℤ DD bb) := coxIdeal DD bb A u * coxIdeal DD bb A' u
    change z ∈ P
    have hAA'_prod : (((A * A' : ℤ) : QuadraticAlgebra ℤ DD bb)) ∈ P := by
      have hA : ((A : QuadraticAlgebra ℤ DD bb)) ∈ coxIdeal DD bb A u :=
        self_mem_coxIdeal DD bb A u
      have hA' : ((A' : QuadraticAlgebra ℤ DD bb)) ∈ coxIdeal DD bb A' u :=
        self_mem_coxIdeal DD bb A' u
      simpa [P, Int.cast_mul] using Ideal.mul_mem_mul hA hA'
    have hβ_prod : β ∈ P := by
      have hAβ : ((A : QuadraticAlgebra ℤ DD bb) * β) ∈ P := by
        have hA : ((A : QuadraticAlgebra ℤ DD bb)) ∈ coxIdeal DD bb A u :=
          self_mem_coxIdeal DD bb A u
        have hβ' : β ∈ coxIdeal DD bb A' u := Ideal.subset_span (by simp [β])
        simpa [P] using Ideal.mul_mem_mul hA hβ'
      have hA'β : ((A' : QuadraticAlgebra ℤ DD bb) * β) ∈ P := by
        have hβ : β ∈ coxIdeal DD bb A u := Ideal.subset_span (by simp [β])
        have hA' : ((A' : QuadraticAlgebra ℤ DD bb)) ∈ coxIdeal DD bb A' u :=
          self_mem_coxIdeal DD bb A' u
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
      simpa [K, coxIdeal, β] using hz
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

end PrimitivePositiveDefiniteForm

end BinaryQuadraticForm
end QuadraticNumberFields
