/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Gauss.CompositionClass
import QuadraticNumberFields.Forms.ClassGroup.Structure
import QNFMathlib.Data.Int.Parity
import QNFMathlib.RingTheory.Ideal.Span

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

/-- The product of the two integer generators lies in the product of the two
Cox ideals. -/
private theorem cast_mul_mem_coxIdeal_mul {DD bb A A' u u' : ℤ} :
    (((A * A' : ℤ) : QuadraticAlgebra ℤ DD bb)) ∈
      CoxIdealRelation.coxIdeal DD bb A u * CoxIdealRelation.coxIdeal DD bb A' u' := by
  rw [Int.cast_mul]
  exact Ideal.mul_mem_mul
    (CoxIdealRelation.self_mem_coxIdeal DD bb A u)
    (CoxIdealRelation.self_mem_coxIdeal DD bb A' u')

/-- The Cox beta generator belongs to its Cox ideal. -/
private theorem beta_mem_coxIdeal {DD bb A u : ℤ} :
    (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb) ∈ CoxIdealRelation.coxIdeal DD bb A u :=
  Ideal.subset_span (by simp)

/-- The product of the first integer generator and any element of the second
Cox ideal lies in the product of the two Cox ideals. -/
private theorem cast_mul_mem_coxIdeal_mul_right {DD bb A A' u u' : ℤ}
    {x : QuadraticAlgebra ℤ DD bb}
    (hx : x ∈ CoxIdealRelation.coxIdeal DD bb A' u') :
    ((A : QuadraticAlgebra ℤ DD bb) * x) ∈
      CoxIdealRelation.coxIdeal DD bb A u * CoxIdealRelation.coxIdeal DD bb A' u' := by
  exact Ideal.mul_mem_mul
    (CoxIdealRelation.self_mem_coxIdeal DD bb A u)
    hx

/-- The product of any element of the first Cox ideal and the second integer
generator lies in the product of the two Cox ideals. -/
private theorem mem_mul_cast_mem_coxIdeal_mul_left {DD bb A A' u u' : ℤ}
    {x : QuadraticAlgebra ℤ DD bb}
    (hx : x ∈ CoxIdealRelation.coxIdeal DD bb A u) :
    (x * (A' : QuadraticAlgebra ℤ DD bb)) ∈
      CoxIdealRelation.coxIdeal DD bb A u * CoxIdealRelation.coxIdeal DD bb A' u' := by
  exact Ideal.mul_mem_mul
    hx
    (CoxIdealRelation.self_mem_coxIdeal DD bb A' u')

/-- Reverse containment for the generalized united Cox ideal product.  This is
split out because the span induction and Bézout recombination are reusable and
expensive to elaborate inside the full arithmetic proof. -/
private theorem coxIdeal_mul_of_united_reverse
    {DD bb A₁ A₂ u₁ u₂ u t k : ℤ}
    (hcop : Int.gcd A₁ A₂ = 1)
    (hβ₁_eq :
      (⟨u₁, 1⟩ : QuadraticAlgebra ℤ DD bb) =
        (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb) -
          (t : QuadraticAlgebra ℤ DD bb) * (A₁ : QuadraticAlgebra ℤ DD bb))
    (hβ₂_eq :
      (⟨u₂, 1⟩ : QuadraticAlgebra ℤ DD bb) =
        (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb) -
          (k : QuadraticAlgebra ℤ DD bb) * (A₂ : QuadraticAlgebra ℤ DD bb)) :
    CoxIdealRelation.coxIdeal DD bb (A₁ * A₂) u ≤
      CoxIdealRelation.coxIdeal DD bb A₁ u₁ * CoxIdealRelation.coxIdeal DD bb A₂ u₂ := by
  intro z hz
  let β₁ : QuadraticAlgebra ℤ DD bb := ⟨u₁, 1⟩
  let β₂ : QuadraticAlgebra ℤ DD bb := ⟨u₂, 1⟩
  let β : QuadraticAlgebra ℤ DD bb := ⟨u, 1⟩
  let P : Ideal (QuadraticAlgebra ℤ DD bb) :=
    CoxIdealRelation.coxIdeal DD bb A₁ u₁ * CoxIdealRelation.coxIdeal DD bb A₂ u₂
  change z ∈ P
  have hβ₁_eq' : β₁ = β - (t : QuadraticAlgebra ℤ DD bb) *
      (A₁ : QuadraticAlgebra ℤ DD bb) := hβ₁_eq
  have hβ₂_eq' : β₂ = β - (k : QuadraticAlgebra ℤ DD bb) *
      (A₂ : QuadraticAlgebra ℤ DD bb) := hβ₂_eq
  have hAA_prod : (((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) ∈ P := by
    exact cast_mul_mem_coxIdeal_mul (DD := DD) (bb := bb) (A := A₁) (A' := A₂)
      (u := u₁) (u' := u₂)
  have hA₁β₂ : ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β₂ ∈ P := by
    have hβ₂ : β₂ ∈ CoxIdealRelation.coxIdeal DD bb A₂ u₂ :=
      beta_mem_coxIdeal (DD := DD) (bb := bb) (A := A₂) (u := u₂)
    exact cast_mul_mem_coxIdeal_mul_right (DD := DD) (bb := bb) (A := A₁) (A' := A₂)
      (u := u₁) (u' := u₂) hβ₂
  have hβ₁A₂ : β₁ * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) ∈ P := by
    have hβ₁ : β₁ ∈ CoxIdealRelation.coxIdeal DD bb A₁ u₁ :=
      beta_mem_coxIdeal (DD := DD) (bb := bb) (A := A₁) (u := u₁)
    exact mem_mul_cast_mem_coxIdeal_mul_left (DD := DD) (bb := bb) (A := A₁) (A' := A₂)
      (u := u₁) (u' := u₂) hβ₁
  have hA₁β : ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β ∈ P := by
    have h_eq : ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β =
        ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β₂ +
          (k : ℤ) * (((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
      rw [show β = β₂ + (k : QuadraticAlgebra ℤ DD bb) *
        ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) from by rw [hβ₂_eq']; abel]
      push_cast
      ring
    rw [h_eq]
    exact P.add_mem hA₁β₂ (P.mul_mem_left _ hAA_prod)
  have hβA₂ : β * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) ∈ P := by
    have h_eq : β * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) =
        β₁ * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) +
          (t : ℤ) * (((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
      rw [show β = β₁ + (t : QuadraticAlgebra ℤ DD bb) *
        ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) from by rw [hβ₁_eq']; abel]
      push_cast
      ring
    rw [h_eq]
    exact P.add_mem hβ₁A₂ (P.mul_mem_left _ hAA_prod)
  have hbez : (1 : ℤ) = A₁ * Int.gcdA A₁ A₂ + A₂ * Int.gcdB A₁ A₂ := by
    rw [← Int.gcd_eq_gcd_ab A₁ A₂, hcop]
    norm_num
  have hβ_prod : β ∈ P := by
    have h_eq : β = ((Int.gcdA A₁ A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) *
        (((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β) +
      ((Int.gcdB A₁ A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) *
        (β * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
      calc
        β = (1 : QuadraticAlgebra ℤ DD bb) * β := by simp
        _ = (((A₁ * Int.gcdA A₁ A₂ + A₂ * Int.gcdB A₁ A₂ : ℤ) :
            QuadraticAlgebra ℤ DD bb)) * β := by rw [← hbez]; simp
        _ = ((Int.gcdA A₁ A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) *
            (((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β) +
          ((Int.gcdB A₁ A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) *
            (β * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
          push_cast
          ring
    rw [h_eq]
    exact P.add_mem (P.mul_mem_left _ hA₁β) (P.mul_mem_left _ hβA₂)
  have hz' : z ∈ Ideal.span
      ({(((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)), β} :
        Set (QuadraticAlgebra ℤ DD bb)) := by
    simpa [CoxIdealRelation.coxIdeal, β] using hz
  exact Submodule.span_induction
    (p := fun x _ => x ∈ P)
    (fun x hx => by
      rcases hx with rfl | rfl
      · exact hAA_prod
      · exact hβ_prod)
    P.zero_mem
    (fun _ _ _ _ hy hz => P.add_mem hy hz)
    (fun t _ _ hy => by simpa using P.mul_mem_left t hy)
    hz'

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
  have hB : B = -2 * u - bb := by linarith
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
    · dsimp [β]
      rw [hB, hDD]
      ring
    · dsimp [β]
      rw [hB]
      ring
  apply le_antisymm
  · dsimp [CoxIdealRelation.coxIdeal]
    apply Ideal.span_pair_mul_span_pair_le
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

/-- **Generalised Cox ideal product** for united (non-concordant) forms.

Given two forms with the same discriminant (parameterised by `DD, bb`) but
possibly **different** middle coefficients `B₁ ≠ B₂` (hence different `u₁, u₂`),
the CRT-chosen `B` satisfying `B ≡ B₁ (mod 2·A₁)` and `B ≡ B₂ (mod 2·A₂)`
(equivalently `u ≡ u₁ (mod A₁)` and `u ≡ u₂ (mod A₂)`) makes the Cox ideals
multiply exactly:

`coxIdeal(A₁, u₁) * coxIdeal(A₂, u₂) = coxIdeal(A₁·A₂, u)`

This subsumes `coxIdeal_mul_of_concordant` (which is the special case `B₁ = B₂ = B`).
The proof adapts the same span-pair framework, expressing `β₁ = β - t·A₁` and
`β₂ = β - k·A₂` via the CRT relations. -/
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
  -- Basic identities for B and u
  have hB : B = -2 * u - bb := by linarith
  have hB₁ : B₁ = -2 * u₁ - bb := by linarith
  have hB₂ : B₂ = -2 * u₂ - bb := by linarith
  -- Discriminant identities: DD in terms of each form
  have hDD₁ : DD = u₁ ^ 2 + bb * u₁ - A₁ * C₁ := by
    rw [hB₁] at hdiscQ; nlinarith
  have hDD₂ : DD = u₂ ^ 2 + bb * u₂ - A₂ * C₂ := by
    rw [hB₂] at hdiscR; nlinarith
  -- CRT relations: u = u₁ + A₁·t, u = u₂ + A₂·k
  have h_2u_eq : (2 : ℤ) * u = -(B + bb) := by linarith
  have h_2u₁_eq : (2 : ℤ) * u₁ = -(B₁ + bb) := by linarith
  have h_2u₂_eq : (2 : ℤ) * u₂ = -(B₂ + bb) := by linarith
  have h_CRT₁ : A₁ ∣ u - u₁ := by
    have h_mod_sum : B + bb ≡ B₁ + bb [ZMOD 2 * A₁] := h_mod_left.add_right bb
    have h_mod_neg : -(B + bb) ≡ -(B₁ + bb) [ZMOD 2 * A₁] := h_mod_sum.neg
    have h_mod_u : (2 : ℤ) * u ≡ (2 : ℤ) * u₁ [ZMOD 2 * A₁] := by
      simpa [h_2u_eq, h_2u₁_eq] using h_mod_neg
    rcases (Int.modEq_iff_dvd.mp h_mod_u) with ⟨q, hq⟩
    -- hq : (2*u₁ - 2*u) = (2*A₁) * q  (→ from modEq_iff_dvd: n ∣ b - a)
    have hq' : u - u₁ = A₁ * (-q) := by linarith
    exact ⟨-q, hq'⟩
  rcases h_CRT₁ with ⟨t, ht⟩
  -- ht : u - u₁ = A₁ * t, so u = u₁ + A₁ * t
  have ht' : u = u₁ + A₁ * t := by linarith
  have h_CRT₂ : A₂ ∣ u - u₂ := by
    have h_mod_sum : B + bb ≡ B₂ + bb [ZMOD 2 * A₂] := h_mod_right.add_right bb
    have h_mod_neg : -(B + bb) ≡ -(B₂ + bb) [ZMOD 2 * A₂] := h_mod_sum.neg
    have h_mod_u : (2 : ℤ) * u ≡ (2 : ℤ) * u₂ [ZMOD 2 * A₂] := by
      simpa [h_2u_eq, h_2u₂_eq] using h_mod_neg
    rcases (Int.modEq_iff_dvd.mp h_mod_u) with ⟨q, hq⟩
    -- hq : (2*u₂ - 2*u) = (2*A₂) * q
    have hq' : u - u₂ = A₂ * (-q) := by linarith
    exact ⟨-q, hq'⟩
  rcases h_CRT₂ with ⟨k, hk⟩
  -- hk : u - u₂ = A₂ * k, so u = u₂ + A₂ * k
  have hk' : u = u₂ + A₂ * k := by linarith
  -- Key divisibility: 4·A₁·A₂ ∣ B² - (bb² + 4·DD)
  have h_dvd_prod : (4 * A₁ * A₂) ∣ B ^ 2 - (bb ^ 2 + 4 * DD) := by
    -- Borrow the same coprime-cancellation argument from disc_composeForm
    -- Step 1: 4·A₁ ∣ B² - D using B ≡ B₁ (mod 2A₁) and hdiscQ
    have h_dvd_left : (4 * A₁) ∣ B ^ 2 - (bb ^ 2 + 4 * DD) := by
      have := (Int.modEq_iff_dvd.mp h_mod_left)
      rcases this with ⟨q, hq⟩
      -- hq: 2*A₁*q = B₁ - B, so B = B₁ - 2*A₁*q
      have hB_expr : B = B₁ - 2 * A₁ * q := by linarith
      rw [hB_expr]
      use A₁ * q ^ 2 - B₁ * q + C₁
      calc
        (B₁ - 2 * A₁ * q) ^ 2 - (bb ^ 2 + 4 * DD)
            = (B₁ - 2 * A₁ * q) ^ 2 - (B₁ ^ 2 - 4 * A₁ * C₁) := by rw [hdiscQ]
        _ = 4 * A₁ * (A₁ * q ^ 2 - B₁ * q + C₁) := by ring
    -- Step 2: 4·A₂ ∣ B² - D using B ≡ B₂ (mod 2A₂) and hdiscR
    have h_dvd_right : (4 * A₂) ∣ B ^ 2 - (bb ^ 2 + 4 * DD) := by
      have := (Int.modEq_iff_dvd.mp h_mod_right)
      rcases this with ⟨q, hq⟩
      have hB_expr : B = B₂ - 2 * A₂ * q := by linarith
      rw [hB_expr]
      use A₂ * q ^ 2 - B₂ * q + C₂
      calc
        (B₂ - 2 * A₂ * q) ^ 2 - (bb ^ 2 + 4 * DD)
            = (B₂ - 2 * A₂ * q) ^ 2 - (B₂ ^ 2 - 4 * A₂ * C₂) := by rw [hdiscR]
        _ = 4 * A₂ * (A₂ * q ^ 2 - B₂ * q + C₂) := by ring
    -- Step 3: coprime cancellation
    rcases h_dvd_left with ⟨X, hX⟩
    rcases h_dvd_right with ⟨Y, hY⟩
    -- 4*A₁*X = B²-D = 4*A₂*Y → A₁*X = A₂*Y
    have h_eq : A₁ * X = A₂ * Y := by nlinarith
    have hA₂_dvd_A₁X : A₂ ∣ A₁ * X := by rw [h_eq]; exact dvd_mul_right _ _
    have hA₂_dvd_X : A₂ ∣ X :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hA₂_dvd_A₁X (by rwa [Int.gcd_comm])
    rcases hA₂_dvd_X with ⟨Z, hZ⟩
    use Z
    calc
      B ^ 2 - (bb ^ 2 + 4 * DD) = 4 * A₁ * X := hX
      _ = 4 * A₁ * (A₂ * Z) := by rw [hZ]
      _ = (4 * A₁ * A₂) * Z := by ring
  rcases h_dvd_prod with ⟨C_prod, hC_prod⟩
  -- Generators of the Cox ideals
  let β₁ : QuadraticAlgebra ℤ DD bb := ⟨u₁, 1⟩
  let β₂ : QuadraticAlgebra ℤ DD bb := ⟨u₂, 1⟩
  let β : QuadraticAlgebra ℤ DD bb := ⟨u, 1⟩
  let K : Ideal (QuadraticAlgebra ℤ DD bb) :=
    CoxIdealRelation.coxIdeal DD bb (A₁ * A₂) u
  -- Express β₁, β₂ in terms of β using the CRT relations
  -- ht: u - u₁ = A₁·t, so u₁ = u - A₁·t → β₁ = β - t·(A₁ : QA)
  have hβ₁_eq : β₁ = β - (t : QuadraticAlgebra ℤ DD bb) *
      ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) := by
    ext
    · -- re: u₁ = u - t*A₁
      simp [β₁, β]
      linarith
    · -- im: both sides are 1
      simp [β₁, β]
  -- hk: u - u₂ = A₂·k, so u₂ = u - A₂·k → β₂ = β - k·(A₂ : QA)
  have hβ₂_eq : β₂ = β - (k : QuadraticAlgebra ℤ DD bb) *
      ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) := by
    ext
    · -- re: u₂ = u - k*A₂
      simp [β₂, β]
      linarith
    · -- im: both sides are 1
      simp [β₂, β]
  -- Key identity: A₁·A₂·C_prod = u² + u·bb - DD
  have h_prod_id : A₁ * A₂ * C_prod = u ^ 2 + u * bb - DD := by
    have h_eq : 4 * A₁ * A₂ * C_prod = 4 * (u ^ 2 + u * bb - DD) := by
      rw [hB] at hC_prod
      nlinarith
    nlinarith
  -- β² formula: β² = -B·β - C_prod·(A₁·A₂)
  have hβ_sq : β * β = -(B : QuadraticAlgebra ℤ DD bb) * β -
      ((C_prod : ℤ) : QuadraticAlgebra ℤ DD bb) *
        (((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
    ext
    · dsimp [β]
      rw [hB]
      nlinarith [h_prod_id]
    · dsimp [β]
      rw [hB]
      ring
  -- Key membership facts for K
  have hAA_mem_K : (((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) ∈ K :=
    CoxIdealRelation.self_mem_coxIdeal DD bb (A₁ * A₂) u
  have hβ_mem_K : β ∈ K :=
    Ideal.subset_span (by simp [β])
  have hA₁β_mem_K : ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β ∈ K :=
    K.mul_mem_left _ hβ_mem_K
  have hβA₂_mem_K : β * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) ∈ K :=
    K.mul_mem_right _ hβ_mem_K
  -- Forward containment: coxIdeal(A₁,u₁) * coxIdeal(A₂,u₂) ≤ K
  have h_forward : CoxIdealRelation.coxIdeal DD bb A₁ u₁ *
      CoxIdealRelation.coxIdeal DD bb A₂ u₂ ≤ K := by
    dsimp [CoxIdealRelation.coxIdeal]
    apply Ideal.span_pair_mul_span_pair_le
    · -- A₁ · A₂ ∈ K
      simpa [Int.cast_mul] using hAA_mem_K
    · -- A₁ · β₂ ∈ K
      have h_expr : ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β₂ =
          ((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β -
            (k : QuadraticAlgebra ℤ DD bb) *
              (((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
        rw [hβ₂_eq]; push_cast; ring
      rw [h_expr]
      exact K.sub_mem (K.mul_mem_left _ hβ_mem_K) (K.mul_mem_left _ hAA_mem_K)
    · -- β₁ · A₂ ∈ K
      have h_expr : β₁ * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) =
          β * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb) -
            (t : QuadraticAlgebra ℤ DD bb) *
              (((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
        rw [hβ₁_eq]; push_cast; ring
      rw [h_expr]
      exact K.sub_mem (K.mul_mem_right _ hβ_mem_K) (K.mul_mem_left _ hAA_mem_K)
    · -- β₁ · β₂ ∈ K
      have h_expr : β₁ * β₂ =
          β * β -
            (k : QuadraticAlgebra ℤ DD bb) * (β * ((A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) -
            (t : QuadraticAlgebra ℤ DD bb) * (((A₁ : ℤ) : QuadraticAlgebra ℤ DD bb) * β) +
            ((t * k : ℤ) : QuadraticAlgebra ℤ DD bb) *
              (((A₁ * A₂ : ℤ) : QuadraticAlgebra ℤ DD bb)) := by
        rw [hβ₁_eq, hβ₂_eq]; push_cast; ring
      rw [h_expr, hβ_sq]
      -- Goal: (-B·β - C_prod·(A₁·A₂)) - k·(β·A₂) - t·(A₁·β)
      --       + (t·k)·(A₁·A₂) ∈ K
      -- = ((X - Y) - Z) + W
      apply K.add_mem
      · -- X - Y - Z ∈ K
        apply K.sub_mem
        · -- X - Y ∈ K
          apply K.sub_mem
          · -- X = -B·β - C_prod·(A₁·A₂) ∈ K
            apply K.sub_mem
            · simpa using K.mul_mem_left (-(B : QuadraticAlgebra ℤ DD bb)) hβ_mem_K
            · simpa using K.mul_mem_left ((C_prod : ℤ) : QuadraticAlgebra ℤ DD bb) hAA_mem_K
          · -- Y = k·(β·A₂) ∈ K
            exact K.mul_mem_left ((k : ℤ) : QuadraticAlgebra ℤ DD bb) hβA₂_mem_K
        · -- Z = t·(A₁·β) ∈ K
          exact K.mul_mem_left ((t : ℤ) : QuadraticAlgebra ℤ DD bb) hA₁β_mem_K
      · -- W = (t·k)·(A₁·A₂) ∈ K
        exact K.mul_mem_left (((t * k : ℤ) : QuadraticAlgebra ℤ DD bb)) hAA_mem_K
  -- Reverse containment: K ≤ coxIdeal(A₁,u₁) * coxIdeal(A₂,u₂)
  have h_reverse : K ≤ CoxIdealRelation.coxIdeal DD bb A₁ u₁ *
      CoxIdealRelation.coxIdeal DD bb A₂ u₂ := by
    exact coxIdeal_mul_of_united_reverse hcop hβ₁_eq hβ₂_eq
  -- Combine forward and reverse
  exact le_antisymm h_forward h_reverse

end Generic

end CoxComposition

namespace PrimitivePositiveDefiniteForm

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
    simpa [u] using Int.two_mul_neg_ediv_two_of_even hb_even
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
          rw [Ideal.comap_mul_of_ringEquiv]
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
    simpa [u] using Int.two_mul_neg_succ_ediv_two_of_odd hb_odd
  have hd_eq : d = 1 + 4 * (d / 4) := by omega
  have hdiscQ : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 1 ^ 2 + 4 * (d / 4) := by
    have hdisc_d : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = d := by
      simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
        fieldDiscriminant_of_mod_four_eq_one hd4] using Q.2.1
    linarith
  have hdiscR : Q.1.b ^ 2 - 4 * R.1.a * R.1.c = 1 ^ 2 + 4 * (d / 4) := by
    have hRdisc : R.1.b ^ 2 - 4 * R.1.a * R.1.c = d := by
      simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc,
        fieldDiscriminant_of_mod_four_eq_one hd4] using R.2.1
    rw [← h.2.1] at hRdisc
    linarith
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
          rw [Ideal.comap_mul_of_ringEquiv]
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
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] [Fact (d < 0)]
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (h : Q.1.IsConcordant R.1) :
    composeConcordantOfRepresentatives Q R h =
      (((Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q :
          FormClass (fieldDiscriminant d)) *
        (Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) R :
          FormClass (fieldDiscriminant d))) :
        FormClass (fieldDiscriminant d)) := by
  let hdneg : d < 0 := Fact.out
  apply (formClassEquivClassGroup hdneg).injective
  change formClassToClassGroup d (composeConcordantOfRepresentatives Q R h) =
    formClassToClassGroup d
      ((Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q :
          FormClass (fieldDiscriminant d)) *
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
  letI : Fact (d < 0) := ⟨hdneg⟩
  rw [composeConcordantOfRepresentatives_eq_mul Q₁ R₁ h₁,
    composeConcordantOfRepresentatives_eq_mul Q₂ R₂ h₂, hQ, hR]

end FormClass

end BinaryQuadraticForm
end QuadraticNumberFields
