/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Forms.Reduction
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Enumeration of Reduced Binary Quadratic Forms

This file defines a computable search space for primitive reduced positive
definite forms of a negative discriminant.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

instance decidableHasDiscriminant (Q : BinaryQuadraticForm) (D : ℤ) :
    Decidable (Q.HasDiscriminant D) := by
  unfold HasDiscriminant
  infer_instance

instance decidableIsPositiveDefinite (Q : BinaryQuadraticForm) :
    Decidable Q.IsPositiveDefinite := by
  unfold IsPositiveDefinite
  infer_instance

instance decidableIsReduced (Q : BinaryQuadraticForm) :
    Decidable Q.IsReduced := by
  unfold IsReduced
  infer_instance

instance decidableIsPrimitive (Q : BinaryQuadraticForm) :
    Decidable Q.IsPrimitive := by
  unfold IsPrimitive
  infer_instance

/-- A simple computable search bound for reduced forms. -/
def searchBound (D : ℤ) : ℕ :=
  Nat.sqrt D.natAbs + 1

/-- A reduced positive definite form has its `a` coefficient within the
enumeration search bound. -/
theorem a_natAbs_le_searchBound (Q : BinaryQuadraticForm)
    (hpos : Q.IsPositiveDefinite) (hred : Q.IsReduced) :
    Q.a.natAbs ≤ searchBound Q.disc := by
  have hbound := three_mul_a_natAbs_sq_le_disc_natAbs Q hpos hred
  have hsq : Q.a.natAbs ^ 2 ≤ Q.disc.natAbs := by
    nlinarith
  exact (Nat.le_sqrt'.mpr hsq).trans (Nat.le_succ _)

/-- Positive `a` candidates up to the search bound. -/
def aCandidates (D : ℤ) : List ℕ :=
  (List.range (searchBound D + 1)).filter fun a => 0 < a

/-- Integer `b` candidates in `[-a, a]`, generated computably from naturals. -/
def bCandidates (a : ℕ) : List ℤ :=
  (List.range (2 * a + 1)).map fun k : ℕ => (k : ℤ) - (a : ℤ)

/-- Candidate triples before the reduced/primitive filters. -/
def candidateForms (D : ℤ) : List BinaryQuadraticForm :=
  (aCandidates D).flatMap fun a : ℕ =>
    (bCandidates a).map fun b : ℤ =>
      BinaryQuadraticForm.mk (a : ℤ) b ((b ^ 2 - D) / (4 * (a : ℤ)))

/-- Primitive reduced positive definite forms of discriminant `D`. -/
def enumPrimitiveReducedFormsList (D : ℤ) : List BinaryQuadraticForm :=
  (candidateForms D).filter fun Q =>
    Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive

/-- Finset view of primitive reduced positive definite forms of discriminant `D`. -/
def enumPrimitiveReducedForms (D : ℤ) : Finset BinaryQuadraticForm :=
  (enumPrimitiveReducedFormsList D).toFinset

/-- Membership in the finset view is membership in the underlying list modulo
`List.toFinset`. -/
theorem mem_enumPrimitiveReducedForms_iff (D : ℤ) (Q : BinaryQuadraticForm) :
    Q ∈ enumPrimitiveReducedForms D ↔
      Q ∈ (enumPrimitiveReducedFormsList D).toFinset := Iff.rfl

/-- Every list-enumerated form satisfies the filter predicates. -/
theorem of_mem_enumPrimitiveReducedFormsList {D : ℤ} {Q : BinaryQuadraticForm}
    (hQ : Q ∈ enumPrimitiveReducedFormsList D) :
    Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive := by
  have hfilter : Q ∈ candidateForms D ∧
      Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive := by
    simpa [enumPrimitiveReducedFormsList] using hQ
  exact hfilter.2

/-- Every finset-enumerated form satisfies the filter predicates. -/
theorem of_mem_enumPrimitiveReducedForms {D : ℤ} {Q : BinaryQuadraticForm}
    (hQ : Q ∈ enumPrimitiveReducedForms D) :
    Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive := by
  apply of_mem_enumPrimitiveReducedFormsList
  simpa [enumPrimitiveReducedForms] using hQ

/-- The positive `a` coefficient of a reduced positive definite form lies in the
`a`-candidate list of its discriminant. -/
theorem a_mem_aCandidates_of_reduced {D : ℤ} {Q : BinaryQuadraticForm}
    (hdisc : Q.HasDiscriminant D) (hpos : Q.IsPositiveDefinite)
    (hred : Q.IsReduced) :
    Q.a.natAbs ∈ aCandidates D := by
  have hle : Q.a.natAbs ≤ searchBound D := by
    have h := a_natAbs_le_searchBound Q hpos hred
    have hd : Q.disc = D := hdisc
    rwa [hd] at h
  have hpos' : 0 < Q.a.natAbs := Int.natAbs_pos.mpr (ne_of_gt hpos.1)
  simp only [aCandidates, List.mem_filter, List.mem_range, decide_eq_true_eq]
  omega

/-- The `b` coefficient of a reduced positive definite form lies in the
`b`-candidate list determined by the reduced bound `|b| ≤ a`. -/
theorem b_mem_bCandidates_of_reduced {Q : BinaryQuadraticForm}
    (hpos : Q.IsPositiveDefinite) (hred : Q.IsReduced) :
    Q.b ∈ bCandidates Q.a.natAbs := by
  have habs := abs_le.mp hred.1
  have ha : 0 < Q.a := hpos.1
  simp only [bCandidates, List.mem_map, List.mem_range]
  exact ⟨(Q.b + Q.a.natAbs).toNat, by omega, by omega⟩

/-- A reduced positive definite form of discriminant `D` occurs among the raw
candidate triples, with `c` recovered as `(b² - D) / (4a)`. -/
theorem mem_candidateForms_of_reduced {D : ℤ} {Q : BinaryQuadraticForm}
    (hdisc : Q.HasDiscriminant D) (hpos : Q.IsPositiveDefinite)
    (hred : Q.IsReduced) :
    Q ∈ candidateForms D := by
  have hacast : (Q.a.natAbs : ℤ) = Q.a := Int.natAbs_of_nonneg (le_of_lt hpos.1)
  have hdiscD : Q.b ^ 2 - 4 * Q.a * Q.c = D := hdisc
  have h4a : (4 : ℤ) * Q.a ≠ 0 := by have := hpos.1; omega
  have hcrec : (Q.b ^ 2 - D) / (4 * (Q.a.natAbs : ℤ)) = Q.c := by
    rw [hacast, ← hdiscD,
      show Q.b ^ 2 - (Q.b ^ 2 - 4 * Q.a * Q.c) = 4 * Q.a * Q.c from by ring]
    exact Int.mul_ediv_cancel_left Q.c h4a
  unfold candidateForms
  exact List.mem_flatMap.mpr ⟨Q.a.natAbs, a_mem_aCandidates_of_reduced hdisc hpos hred,
    List.mem_map.mpr ⟨Q.b, b_mem_bCandidates_of_reduced hpos hred,
      BinaryQuadraticForm.ext hacast rfl hcrec⟩⟩

/-- **Completeness of the reduced-form enumeration.** Every primitive reduced
positive definite form of discriminant `D` appears in `enumPrimitiveReducedForms D`.
Together with `of_mem_enumPrimitiveReducedForms` this characterizes the
enumeration exactly. -/
theorem mem_enumPrimitiveReducedForms_of_reduced {D : ℤ} {Q : BinaryQuadraticForm}
    (hdisc : Q.HasDiscriminant D) (hpos : Q.IsPositiveDefinite)
    (hred : Q.IsReduced) (hprim : Q.IsPrimitive) :
    Q ∈ enumPrimitiveReducedForms D := by
  simp only [enumPrimitiveReducedForms, List.mem_toFinset, enumPrimitiveReducedFormsList,
    List.mem_filter, decide_eq_true_eq]
  exact ⟨mem_candidateForms_of_reduced hdisc hpos hred, hdisc, hpos, hred, hprim⟩

example : bCandidates 1 = [-1, 0, 1] := by
  decide

-- Smoke checks used during development:
-- `#guard (enumPrimitiveReducedFormsList (-20)).length == 2`
-- `#guard (enumPrimitiveReducedFormsList (-163)).length == 1`

end BinaryQuadraticForm
end QuadraticNumberFields
