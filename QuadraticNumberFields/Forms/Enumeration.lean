/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Bridge
import QuadraticNumberFields.Forms.Reduction
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

/-- The `a`-candidate list has no duplicates. -/
theorem aCandidates_nodup (D : ℤ) : (aCandidates D).Nodup :=
  List.Nodup.filter _ List.nodup_range

/-- Integer `b` candidates in `[-a, a]`, generated computably from naturals. -/
def bCandidates (a : ℕ) : List ℤ :=
  (List.range (2 * a + 1)).map fun k : ℕ => (k : ℤ) - (a : ℤ)

/-- The `b`-candidate list has no duplicates. -/
theorem bCandidates_nodup (a : ℕ) : (bCandidates a).Nodup := by
  refine List.Nodup.map ?_ List.nodup_range
  intro k l hkl
  change (k : ℤ) - (a : ℤ) = (l : ℤ) - (a : ℤ) at hkl
  have h : (k : ℤ) = l := by omega
  exact_mod_cast h

private def candidateFormsForA (D : ℤ) (a : ℕ) : List BinaryQuadraticForm :=
  (bCandidates a).map fun b : ℤ =>
    BinaryQuadraticForm.mk (a : ℤ) b ((b ^ 2 - D) / (4 * (a : ℤ)))

/-- Candidate triples before the reduced/primitive filters. -/
def candidateForms (D : ℤ) : List BinaryQuadraticForm :=
  (aCandidates D).flatMap (candidateFormsForA D)

private theorem candidateFormsForA_nodup (D : ℤ) (a : ℕ) :
    (candidateFormsForA D a).Nodup := by
  unfold candidateFormsForA
  refine List.Nodup.map ?_ (bCandidates_nodup a)
  intro b c hbc
  exact congrArg BinaryQuadraticForm.b hbc

private theorem candidateFormsForA_disjoint_of_ne {D : ℤ} {a b : ℕ} (hab : a ≠ b) :
    List.Disjoint (candidateFormsForA D a) (candidateFormsForA D b) := by
  rw [List.disjoint_iff_ne]
  intro Q hQ R hR hQR
  unfold candidateFormsForA at hQ hR
  rw [List.mem_map] at hQ hR
  rcases hQ with ⟨m, _hm, hQeq⟩
  rcases hR with ⟨n, _hn, hReq⟩
  have hab' : (a : ℤ) = b := by
    simpa [← hQeq, ← hReq] using congrArg BinaryQuadraticForm.a hQR
  exact hab (by exact_mod_cast hab')

private theorem aCandidates_pairwise_candidateFormsForA_disjoint (D : ℤ) :
    List.Pairwise (Function.onFun List.Disjoint (candidateFormsForA D)) (aCandidates D) := by
  change List.Pairwise (fun a b => List.Disjoint (candidateFormsForA D a)
    (candidateFormsForA D b)) (aCandidates D)
  exact List.Pairwise.imp (fun hab => candidateFormsForA_disjoint_of_ne hab)
    (aCandidates_nodup D)

/-- Raw candidate triples are generated without duplicates. -/
theorem candidateForms_nodup (D : ℤ) : (candidateForms D).Nodup := by
  rw [candidateForms, List.nodup_flatMap]
  exact ⟨fun a _ha => candidateFormsForA_nodup D a,
    aCandidates_pairwise_candidateFormsForA_disjoint D⟩

/-- Primitive reduced positive definite forms of discriminant `D`. -/
def enumPrimitiveReducedFormsList (D : ℤ) : List BinaryQuadraticForm :=
  (candidateForms D).filter fun Q =>
    Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive

/-- Finset view of primitive reduced positive definite forms of discriminant `D`. -/
def enumPrimitiveReducedForms (D : ℤ) : Finset BinaryQuadraticForm :=
  (enumPrimitiveReducedFormsList D).toFinset

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

/-- Membership in the finset enumeration is exactly the conjunction of the
filtered reduced-form predicates. -/
theorem mem_enumPrimitiveReducedForms_iff {D : ℤ} {Q : BinaryQuadraticForm} :
    Q ∈ enumPrimitiveReducedForms D ↔
      Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive := by
  constructor
  · exact of_mem_enumPrimitiveReducedForms
  · intro hQ
    exact mem_enumPrimitiveReducedForms_of_reduced hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2

/-- View an enumerated reduced primitive positive definite form as a member of
the restricted Cox carrier. -/
def primitivePositiveDefiniteFormOfMemEnum {D : ℤ} {Q : BinaryQuadraticForm}
    (hQ : Q ∈ enumPrimitiveReducedForms D) : PrimitivePositiveDefiniteForm D :=
  let h := of_mem_enumPrimitiveReducedForms hQ
  ⟨Q, h.1, h.2.2.2, h.2.1⟩

/-- Form classes represented by the reduced-form enumeration. -/
noncomputable def reducedFormClasses (D : ℤ) : Finset (FormClass D) := by
  classical
  exact (enumPrimitiveReducedForms D).attach.image fun Q =>
    Quotient.mk (primitivePositiveDefiniteFormSetoid D)
      (primitivePositiveDefiniteFormOfMemEnum Q.2)

/-- Every form class has a representative in the reduced-form enumeration. -/
theorem mem_reducedFormClasses (D : ℤ) (C : FormClass D) : C ∈ reducedFormClasses D := by
  classical
  obtain ⟨R, hRred, hRclass⟩ := exists_isReduced_mk_eq_formClass C
  have hRmem : R.1 ∈ enumPrimitiveReducedForms D :=
    mem_enumPrimitiveReducedForms_of_reduced R.2.1 R.2.2.2 hRred R.2.2.1
  refine Finset.mem_image.mpr ⟨⟨R.1, hRmem⟩, ?_, ?_⟩
  · simp
  · simpa [primitivePositiveDefiniteFormOfMemEnum] using hRclass

noncomputable instance formClassFintype (D : ℤ) : Fintype (FormClass D) :=
  ⟨reducedFormClasses D, mem_reducedFormClasses D⟩

/-- The reduced-form representatives cover all form classes. -/
theorem reducedFormClasses_eq_univ (D : ℤ) : reducedFormClasses D = Finset.univ := by
  classical
  ext C
  exact ⟨fun _ => Finset.mem_univ C, fun _ => mem_reducedFormClasses D C⟩

/-- Passing from reduced forms to form classes does not identify distinct
enumerated forms. -/
theorem reducedFormClasses_card (D : ℤ) :
    (reducedFormClasses D).card = (enumPrimitiveReducedForms D).card := by
  classical
  rw [reducedFormClasses]
  trans (enumPrimitiveReducedForms D).attach.card
  · refine Finset.card_image_of_injective _ ?_
    intro Q R hQR
    have hQ := of_mem_enumPrimitiveReducedForms Q.2
    have hR := of_mem_enumPrimitiveReducedForms R.2
    have hclass :
        Quotient.mk (primitivePositiveDefiniteFormSetoid D)
          (primitivePositiveDefiniteFormOfMemEnum Q.2) =
        Quotient.mk (primitivePositiveDefiniteFormSetoid D)
          (primitivePositiveDefiniteFormOfMemEnum R.2) := by
      simpa using hQR
    have hval : Q.1 = R.1 :=
      congrArg (fun S : PrimitivePositiveDefiniteForm D => S.1)
        (eq_of_isReduced_of_mk_eq_mk hQ.2.2.1 hR.2.2.1 hclass)
    exact Subtype.ext hval
  · simp

/-- The list view of the reduced-form enumeration has no duplicates. -/
theorem enumPrimitiveReducedFormsList_nodup (D : ℤ) :
    (enumPrimitiveReducedFormsList D).Nodup := by
  simpa [enumPrimitiveReducedFormsList] using
    (candidateForms_nodup D).filter (fun Q =>
      Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive)

/-- The finset cardinality agrees with the list length because the list
enumerator is duplicate-free. -/
theorem enumPrimitiveReducedForms_card_eq_length (D : ℤ) :
    (enumPrimitiveReducedForms D).card = (enumPrimitiveReducedFormsList D).length := by
  simpa [enumPrimitiveReducedForms] using
    List.toFinset_card_of_nodup (enumPrimitiveReducedFormsList_nodup D)

/-- The reduced primitive positive definite forms of discriminant `-20` are two. -/
theorem enumPrimitiveReducedFormsList_neg20_length :
    (enumPrimitiveReducedFormsList (-20)).length = 2 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-4` are one. -/
theorem enumPrimitiveReducedFormsList_neg4_length :
    (enumPrimitiveReducedFormsList (-4)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-8` are one. -/
theorem enumPrimitiveReducedFormsList_neg8_length :
    (enumPrimitiveReducedFormsList (-8)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-3` are one. -/
theorem enumPrimitiveReducedFormsList_neg3_length :
    (enumPrimitiveReducedFormsList (-3)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-7` are one. -/
theorem enumPrimitiveReducedFormsList_neg7_length :
    (enumPrimitiveReducedFormsList (-7)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-11` are one. -/
theorem enumPrimitiveReducedFormsList_neg11_length :
    (enumPrimitiveReducedFormsList (-11)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-19` are one. -/
theorem enumPrimitiveReducedFormsList_neg19_length :
    (enumPrimitiveReducedFormsList (-19)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-43` are one. -/
theorem enumPrimitiveReducedFormsList_neg43_length :
    (enumPrimitiveReducedFormsList (-43)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-67` are one. -/
theorem enumPrimitiveReducedFormsList_neg67_length :
    (enumPrimitiveReducedFormsList (-67)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

/-- The reduced primitive positive definite forms of discriminant `-163` are one. -/
theorem enumPrimitiveReducedFormsList_neg163_length :
    (enumPrimitiveReducedFormsList (-163)).length = 1 := by
  norm_num [enumPrimitiveReducedFormsList, candidateForms, candidateFormsForA,
    aCandidates, searchBound, bCandidates]
  all_goals decide

example : bCandidates 1 = [-1, 0, 1] := by
  decide

-- Smoke checks used during development:
-- `#guard (enumPrimitiveReducedFormsList (-20)).length == 2`
-- `#guard (enumPrimitiveReducedFormsList (-163)).length == 1`

end BinaryQuadraticForm
end QuadraticNumberFields
