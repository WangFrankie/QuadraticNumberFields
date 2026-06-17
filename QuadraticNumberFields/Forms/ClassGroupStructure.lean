/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import FiniteAbelianSmith.Correctness
import QuadraticNumberFields.Forms.ComputableClassGroup
import QuadraticNumberFields.Mathlib.Data.Int.Squarefree
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Concrete Class Group Isomorphism Types

This file computes invariant-factor isomorphism types for quadratic class groups
from reduced-form multiplication tables.

The general finite-abelian table classifier is imported from the sibling
classifier project.  This file keeps only the reduced-form enumeration, table
multiplication, and transport from certified table classifications to quadratic
class groups.

## Main results

* `classGroupStandardIsoTypeOfImaginaryParameter`: evaluate the reduced-form
  table for an imaginary quadratic parameter and return a standard type
  description.
* `standardIsoTypeOfReducedFormReps`: run the same classifier on the
  proof-carrying `ReducedFormRep` table.
* `certifiedClassGroupInvariantFactorClassification?`: run the certified
  reduced-form classifier and transport a successful result to the ideal class
  group.
* `standardIsoTypeOfReducedFormReps_eq_classGroupStandardIsoType`: identify the
  proof-carrying representative-table facade with the public raw-form facade.
* `classGroupStandardIsoType_classifies_of_certifiedClassGroupClassifier`:
  upgrade a successful proof-carrying class-group classifier to the public
  standard output.
* `classGroupStandardIsoType_classifies_rawInvariantFactors_of_certifiedClassGroupClassifier`:
  identify that successful public output with the raw invariant-factor
  computation on reduced forms.
* `classGroupStandardIsoType_classifies_of_certifiedStandardIsoType`: transport
  a certified reduced-form table classification across the Cox bridge to the
  ideal class group.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

open FiniteAbelianSmith

/-! ## Reduced-form class-group classifiers -/

/-- The principal reduced form of a negative field discriminant, used as the
identity element for the executable reduced-form table. -/
def principalReducedForm (D : ℤ) : BinaryQuadraticForm :=
  if D % 4 = 0 then
    BinaryQuadraticForm.mk 1 0 (-(D / 4))
  else
    BinaryQuadraticForm.mk 1 1 ((1 - D) / 4)

/-- Compute the standard isomorphism-type description from the reduced-form
table of discriminant `D`. -/
def standardIsoTypeOfReducedForms (D : ℤ) : StandardGroupIsoType :=
  standardIsoTypeOfMulTable (enumPrimitiveReducedFormsList D) (principalReducedForm D)
    composeAndReduce

/-- Given an integer parameter `d`, compute the standard isomorphism-type
description of the imaginary quadratic class group detected by reduced forms.

For negative squarefree `d`, this is the executable facade for the reduced-form
class-group table.  The result is an invariant-factor list whenever the reduced
form table is nonempty. -/
def classGroupStandardIsoTypeOfImaginaryParameter (d : ℤ) : StandardGroupIsoType :=
  standardIsoTypeOfReducedForms (fieldDiscriminant d)

/-- Lift a list-enumerated reduced form into the proof-carrying
`ReducedFormRep` type. -/
def reducedFormRepOfListMem {D : ℤ}
    (Q : { Q : BinaryQuadraticForm // Q ∈ enumPrimitiveReducedFormsList D }) :
    ReducedFormRep D :=
  ⟨Q.1, by
    have hfin : Q.1 ∈ (enumPrimitiveReducedFormsList D).toFinset :=
      List.mem_toFinset.mpr Q.2
    change Q.1 ∈ enumPrimitiveReducedForms D
    exact hfin⟩

/-- Enumerate reduced-form representatives using the executable reduced-form
list as backing data. -/
def reducedFormRepList (D : ℤ) : List (ReducedFormRep D) :=
  (enumPrimitiveReducedFormsList D).attach.map reducedFormRepOfListMem

/-- The reduced-form representative list covers every representative. -/
theorem reducedFormRepList_complete (D : ℤ) :
    ∀ Q : ReducedFormRep D, Q ∈ reducedFormRepList D := by
  intro Q
  unfold reducedFormRepList
  have hfin : Q.1 ∈ (enumPrimitiveReducedFormsList D).toFinset := by
    change Q.1 ∈ (enumPrimitiveReducedFormsList D).toFinset
    exact Q.2
  have hlist : Q.1 ∈ enumPrimitiveReducedFormsList D := List.mem_toFinset.mp hfin
  refine List.mem_map.mpr ⟨⟨Q.1, hlist⟩, ?_, ?_⟩
  · exact List.mem_attach _ ⟨Q.1, hlist⟩
  · exact Subtype.ext rfl

/-- For negative `d`, the canonical principal form is enumerated as a reduced
primitive positive definite form of the field discriminant. -/
theorem principalReducedForm_mem_enum {d : ℤ} (hdneg : d < 0) :
    principalReducedForm (fieldDiscriminant d) ∈
      enumPrimitiveReducedForms (fieldDiscriminant d) := by
  by_cases hd4 : d % 4 = 1
  · have hD : fieldDiscriminant d = d := fieldDiscriminant_of_mod_four_eq_one hd4
    have hDmod : d % 4 ≠ 0 := by omega
    apply mem_enumPrimitiveReducedForms_of_reduced
    · rw [HasDiscriminant, principalReducedForm, hD]
      simp [hDmod, disc]
      omega
    · rw [IsPositiveDefinite, principalReducedForm, hD]
      simp [hDmod, disc]
      omega
    · rw [IsReduced, principalReducedForm, hD]
      simp [hDmod]
      omega
    · rw [IsPrimitive, principalReducedForm, hD]
      simp [hDmod]
  · have hD : fieldDiscriminant d = 4 * d := fieldDiscriminant_of_mod_four_ne_one hd4
    have hDmod : (4 * d) % 4 = 0 := by omega
    apply mem_enumPrimitiveReducedForms_of_reduced
    · rw [HasDiscriminant, principalReducedForm, hD]
      simp [hDmod, disc]
    · rw [IsPositiveDefinite, principalReducedForm, hD]
      simp [hDmod, disc]
      omega
    · rw [IsReduced, principalReducedForm, hD]
      simp [hDmod]
      omega
    · rw [IsPrimitive, principalReducedForm, hD]
      simp [hDmod]

/-- The canonical principal form as a reduced-form representative. -/
def principalReducedFormRep {d : ℤ} (hdneg : d < 0) :
    ReducedFormRep (fieldDiscriminant d) :=
  ⟨principalReducedForm (fieldDiscriminant d), principalReducedForm_mem_enum hdneg⟩

/-- Executable reduced-form table multiplication, backed by `gaussMul`. -/
def reducedFormRepMulForTable
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (Q R : ReducedFormRep (fieldDiscriminant d)) : ReducedFormRep (fieldDiscriminant d) :=
  ⟨gaussMul hdneg Q R, mem_enum_of_gaussMul hdneg Q R⟩

/-- The executable reduced-form table multiplication agrees with the ambient
transported group multiplication. -/
theorem reducedFormRepMulForTable_eq_mul
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    letI := reducedFormRepCommGroup hdneg
    ∀ Q R : ReducedFormRep (fieldDiscriminant d),
      reducedFormRepMulForTable hdneg Q R = Q * R := by
  letI := reducedFormRepCommGroup hdneg
  intro Q R
  rw [reducedFormRep_mul_eq_reducedFormRepMul (d := d) (hdneg := hdneg)]
  rw [← gaussMul_eq_reducedFormRepMul (d := d) (hdneg := hdneg) Q R]
  rfl

/-- On reduced-form representatives, the table multiplication has the same
underlying form as the raw `composeAndReduce` multiplication. -/
theorem reducedFormRepMulForTable_val_eq_composeAndReduce
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (Q R : ReducedFormRep (fieldDiscriminant d)) :
    (reducedFormRepMulForTable hdneg Q R).1 = composeAndReduce Q.1 R.1 := by
  have hQprim : Q.1.IsPrimitive := (of_mem_enumPrimitiveReducedForms Q.2).2.2.2
  have hRprim : R.1.IsPrimitive := (of_mem_enumPrimitiveReducedForms R.2).2.2.2
  have hQpos : Q.1.IsPositiveDefinite := (of_mem_enumPrimitiveReducedForms Q.2).2.1
  have hRpos : R.1.IsPositiveDefinite := (of_mem_enumPrimitiveReducedForms R.2).2.1
  have hdiscQ : Q.1.disc = fieldDiscriminant d := (of_mem_enumPrimitiveReducedForms Q.2).1
  have hdiscR : R.1.disc = fieldDiscriminant d := (of_mem_enumPrimitiveReducedForms R.2).1
  have hQR : Q.1.disc = R.1.disc := by rw [hdiscQ, hdiscR]
  have hQa : Q.1.a ≠ 0 := ne_of_gt hQpos.1
  let comp := composeForm Q.1 R.1 hQR hRprim hQa
  have hcomp_pos : comp.IsPositiveDefinite := by
    have ha_pos : 0 < comp.a := by
      rw [composeForm_a]
      apply mul_pos hQpos.1
      rw [unitedRep_a]
      have hxy_gcd : Int.gcd (coprimeEvalVector R.1 Q.1.a hRprim hQa).1
          (coprimeEvalVector R.1 Q.1.a hRprim hQa).2 = 1 :=
        coprimeEvalVector_gcd R.1 Q.1.a hRprim hQa
      have hxy_nonzero : (coprimeEvalVector R.1 Q.1.a hRprim hQa).1 ≠ 0 ∨
          (coprimeEvalVector R.1 Q.1.a hRprim hQa).2 ≠ 0 := by
        by_contra! hboth
        rcases hboth with ⟨hx, hy⟩
        rw [hx, hy] at hxy_gcd
        simp at hxy_gcd
      exact eval_pos_of_isPositiveDefinite R.1 hRpos hxy_nonzero
    have hdisc_lt : comp.disc < 0 := by
      rw [disc_composeForm Q.1 R.1 hQR hRprim hQa hQpos hRpos, hdiscQ]
      exact fieldDiscriminant_neg hdneg
    exact ⟨ha_pos, hdisc_lt⟩
  unfold reducedFormRepMulForTable gaussMul composeAndReduce
  rw [dif_pos hQR, dif_pos hRprim, dif_pos hQa]
  change reduceForm comp _ = (if h : comp.IsPositiveDefinite then reduceForm comp h else comp)
  rw [dif_pos hcomp_pos]

/-- Powers computed in the reduced-representative table project to powers
computed in the raw reduced-form table. -/
theorem tablePow_reducedFormRepMulForTable_val
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (Q : ReducedFormRep (fieldDiscriminant d)) :
    ∀ n : ℕ,
      (tablePow (reducedFormRepMulForTable hdneg) (principalReducedFormRep hdneg) Q n).1 =
        tablePow composeAndReduce (principalReducedForm (fieldDiscriminant d)) Q.1 n
  | 0 => rfl
  | n + 1 => by
      simp only [tablePow]
      rw [reducedFormRepMulForTable_val_eq_composeAndReduce hdneg]
      rw [tablePow_reducedFormRepMulForTable_val hdneg Q n]

/-- Killed-by-prime-power counts agree for the proof-carrying reduced-form
representative table and the raw reduced-form table. -/
theorem tableKilledByPrimePowerCount_reducedFormRep_eq_reducedForms
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) (p k : ℕ) :
    tableKilledByPrimePowerCount (reducedFormRepList (fieldDiscriminant d))
        (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg) p k =
      tableKilledByPrimePowerCount (enumPrimitiveReducedFormsList (fieldDiscriminant d))
        (principalReducedForm (fieldDiscriminant d)) composeAndReduce p k := by
  unfold tableKilledByPrimePowerCount reducedFormRepList reducedFormRepOfListMem
  change (List.filter (fun x => decide (tablePow (reducedFormRepMulForTable hdneg)
        (principalReducedFormRep hdneg) x (p ^ k) = principalReducedFormRep hdneg))
      (List.map (fun Q => (⟨Q.1, by
        have hfin : Q.1 ∈ (enumPrimitiveReducedFormsList (fieldDiscriminant d)).toFinset :=
          List.mem_toFinset.mpr Q.2
        change Q.1 ∈ enumPrimitiveReducedForms (fieldDiscriminant d)
        exact hfin⟩ : ReducedFormRep (fieldDiscriminant d)))
        (enumPrimitiveReducedFormsList (fieldDiscriminant d)).attach)).length =
      (List.filter (fun x => decide (tablePow composeAndReduce
        (principalReducedForm (fieldDiscriminant d)) x (p ^ k) =
          principalReducedForm (fieldDiscriminant d)))
      (enumPrimitiveReducedFormsList (fieldDiscriminant d))).length
  have hfilter :
      (List.filter (fun x : ReducedFormRep (fieldDiscriminant d) =>
          decide (tablePow composeAndReduce (principalReducedForm (fieldDiscriminant d)) x.1
            (p ^ k) = principalReducedForm (fieldDiscriminant d)))
        (List.map (fun Q => (⟨Q.1, by
          have hfin : Q.1 ∈ (enumPrimitiveReducedFormsList (fieldDiscriminant d)).toFinset :=
            List.mem_toFinset.mpr Q.2
          change Q.1 ∈ enumPrimitiveReducedForms (fieldDiscriminant d)
          exact hfin⟩ : ReducedFormRep (fieldDiscriminant d)))
          (enumPrimitiveReducedFormsList (fieldDiscriminant d)).attach)).map Subtype.val =
        List.filter (fun x => decide (tablePow composeAndReduce
          (principalReducedForm (fieldDiscriminant d)) x (p ^ k) =
            principalReducedForm (fieldDiscriminant d)))
          (enumPrimitiveReducedFormsList (fieldDiscriminant d)) := by
    rw [List.map_filter (f := Subtype.val)
      (p := fun x : ReducedFormRep (fieldDiscriminant d) =>
        decide (tablePow composeAndReduce (principalReducedForm (fieldDiscriminant d)) x.1
          (p ^ k) = principalReducedForm (fieldDiscriminant d))) Subtype.coe_injective]
    simp only [decide_eq_true_eq, Subtype.exists, exists_and_left, exists_prop,
      exists_eq_right_right, Bool.decide_and, List.map_map, Function.comp_apply,
      List.map_subtype, List.unattach_attach, List.map_id_fun', id_eq]
    refine List.filter_congr ?_
    intro x hx
    have hxmem : x ∈ enumPrimitiveReducedForms (fieldDiscriminant d) := by
      change x ∈ (enumPrimitiveReducedFormsList (fieldDiscriminant d)).toFinset
      exact List.mem_toFinset.mpr hx
    simp [hxmem]
  simp [Subtype.ext_iff, tablePow_reducedFormRepMulForTable_val hdneg]
  simpa using congrArg List.length hfilter

/-- Run the table classifier on the proof-carrying reduced-form representative
table. -/
def standardIsoTypeOfReducedFormReps
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    StandardGroupIsoType :=
  standardIsoTypeOfMulTable (reducedFormRepList (fieldDiscriminant d))
    (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg)

/-- The proof-carrying reduced-form representative table and the raw reduced
form table compute the same invariant factors. -/
theorem invariantFactorsOfReducedFormReps_eq_reducedForms
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
        (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg) =
      invariantFactorsOfMulTable (enumPrimitiveReducedFormsList (fieldDiscriminant d))
        (principalReducedForm (fieldDiscriminant d)) composeAndReduce := by
  have hlen :
      (reducedFormRepList (fieldDiscriminant d)).length =
        (enumPrimitiveReducedFormsList (fieldDiscriminant d)).length := by
    simp [reducedFormRepList]
  unfold invariantFactorsOfMulTable primaryInvariantPowersOfMulTable tablePrimaryRankAtLeast
    tableKilledPrimeLog
  simp [hlen, tableKilledByPrimePowerCount_reducedFormRep_eq_reducedForms hdneg]

/-- The proof-carrying reduced-form representative table classifier agrees with
the public raw-form class-group standard-type classifier. -/
theorem standardIsoTypeOfReducedFormReps_eq_classGroupStandardIsoType
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    standardIsoTypeOfReducedFormReps hdneg =
      classGroupStandardIsoTypeOfImaginaryParameter d := by
  unfold standardIsoTypeOfReducedFormReps classGroupStandardIsoTypeOfImaginaryParameter
    standardIsoTypeOfReducedForms standardIsoTypeOfMulTable
  have hlen :
      (reducedFormRepList (fieldDiscriminant d)).length =
        (enumPrimitiveReducedFormsList (fieldDiscriminant d)).length := by
    simp [reducedFormRepList]
  simp [hlen, invariantFactorsOfReducedFormReps_eq_reducedForms hdneg]

/-- The reduced-form representative table classifier always returns a product
in executable invariant-factor normal form. -/
theorem standardIsoTypeOfReducedFormReps_exists_product_isInvariantFactorList
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    ∃ ns, standardIsoTypeOfReducedFormReps hdneg = StandardGroupIsoType.product ns ∧
      isInvariantFactorList ns = true := by
  have hmem : principalReducedFormRep hdneg ∈ reducedFormRepList (fieldDiscriminant d) :=
    reducedFormRepList_complete (fieldDiscriminant d) (principalReducedFormRep hdneg)
  have hne : (reducedFormRepList (fieldDiscriminant d)).length ≠ 0 :=
    ne_of_gt (List.length_pos_of_mem hmem)
  exact standardIsoTypeOfMulTable_exists_product_isInvariantFactorList
    (elems := reducedFormRepList (fieldDiscriminant d))
    (one := principalReducedFormRep hdneg) (mul := reducedFormRepMulForTable hdneg) hne

/-- Run the proof-carrying invariant-factor classifier on reduced-form
representatives.  The returned factors are in normal form and are equipped with
a multiplicative equivalence from `ReducedFormRep`. -/
noncomputable def certifiedReducedFormRepInvariantFactorClassification?
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    letI := reducedFormRepCommGroup hdneg
    Option { ns : List ℕ //
      standardIsoTypeOfReducedFormReps hdneg = StandardGroupIsoType.product ns ∧
        IsInvariantFactorClassification (ReducedFormRep (fieldDiscriminant d)) ns } := by
  letI := reducedFormRepCommGroup hdneg
  exact certifiedInvariantFactorClassification?
    (reducedFormRepList (fieldDiscriminant d))
    (principalReducedFormRep hdneg)
    (reducedFormRepMulForTable hdneg)
    (reducedFormRepList_complete (fieldDiscriminant d))
    (reducedFormRepMulForTable_eq_mul hdneg)

/-- Run the proof-carrying invariant-factor classifier on reduced-form
representatives and transport a successful result to the ideal class group. -/
noncomputable def certifiedClassGroupInvariantFactorClassification?
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    Option { ns : List ℕ //
      standardIsoTypeOfReducedFormReps hdneg = StandardGroupIsoType.product ns ∧
        IsInvariantFactorClassification
          (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ns } := by
  letI := reducedFormRepCommGroup hdneg
  match certifiedReducedFormRepInvariantFactorClassification? hdneg with
  | none => exact none
  | some result =>
      exact some ⟨result.1, result.2.1,
        IsInvariantFactorClassification.ofMulEquiv
          (reducedFormRepMulEquivClassGroup hdneg).symm result.2.2⟩

/-- A successful class-group classifier returns exactly the raw invariant-factor
output of the proof-carrying reduced-form table. -/
theorem certifiedClassGroupInvariantFactorClassification?_factors_eq
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    {result : { ns : List ℕ //
      standardIsoTypeOfReducedFormReps hdneg = StandardGroupIsoType.product ns ∧
        IsInvariantFactorClassification
          (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ns }}
    (hresult : certifiedClassGroupInvariantFactorClassification? d hdneg = some result) :
    result.1 = invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
      (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg) := by
  letI := reducedFormRepCommGroup hdneg
  unfold certifiedClassGroupInvariantFactorClassification? at hresult
  cases hred : certifiedReducedFormRepInvariantFactorClassification? hdneg with
  | none =>
      simp [hred] at hresult
  | some redResult =>
      simp only [hred] at hresult
      cases hresult
      change
        certifiedInvariantFactorClassification?
          (reducedFormRepList (fieldDiscriminant d))
          (principalReducedFormRep hdneg)
          (reducedFormRepMulForTable hdneg)
          (reducedFormRepList_complete (fieldDiscriminant d))
          (reducedFormRepMulForTable_eq_mul hdneg) = some redResult at hred
      exact
        factors_eq_invariantFactorsOfMulTable_of_certifiedInvariantFactorClassification?_eq_some
          hred

/-- A successful proof-carrying class-group classifier semantically classifies
the proof-carrying reduced-form representative table output. -/
theorem standardIsoTypeOfReducedFormReps_classifies_of_certifiedClassGroupClassifier
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (hcert : ∃ result, certifiedClassGroupInvariantFactorClassification? d hdneg = some result) :
    ∃ ns, standardIsoTypeOfReducedFormReps hdneg = StandardGroupIsoType.product ns ∧
      IsInvariantFactorClassification
        (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ns := by
  rcases hcert with ⟨⟨ns, hproduct, hclass⟩, _hcert⟩
  exact ⟨ns, hproduct, hclass⟩

/-- A successful proof-carrying class-group classifier semantically classifies
the public class-group standard output. -/
theorem classGroupStandardIsoType_classifies_of_certifiedClassGroupClassifier
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (hcert : ∃ result, certifiedClassGroupInvariantFactorClassification? d hdneg = some result) :
    ∃ ns, classGroupStandardIsoTypeOfImaginaryParameter d = StandardGroupIsoType.product ns ∧
      IsInvariantFactorClassification
        (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ns := by
  obtain ⟨ns, hproduct, hclass⟩ :=
    standardIsoTypeOfReducedFormReps_classifies_of_certifiedClassGroupClassifier
      hdneg hcert
  exact ⟨ns, (standardIsoTypeOfReducedFormReps_eq_classGroupStandardIsoType hdneg).symm.trans
    hproduct, hclass⟩

/-- A successful class-group classifier semantically classifies the raw
invariant-factor output of the proof-carrying reduced-form table. -/
theorem classGroupStandardIsoType_classifies_rawInvariantFactors_of_certifiedClassGroupClassifier
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (hcert : ∃ result, certifiedClassGroupInvariantFactorClassification? d hdneg = some result) :
    classGroupStandardIsoTypeOfImaginaryParameter d =
        StandardGroupIsoType.product
          (invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
            (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg)) ∧
      IsInvariantFactorClassification
        (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
          (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg)) := by
  rcases hcert with ⟨result, hresult⟩
  have hfactors := certifiedClassGroupInvariantFactorClassification?_factors_eq hdneg hresult
  have hproduct := result.2.1
  have hclass := result.2.2
  constructor
  · rw [hfactors] at hproduct
    exact (standardIsoTypeOfReducedFormReps_eq_classGroupStandardIsoType hdneg).symm.trans
      hproduct
  · simpa [hfactors] using hclass

/-- If a full certificate-data candidate is present in the reduced-form
generator search space, then the proof-carrying reduced-form classifier
succeeds with the raw invariant factors. -/
theorem
    exists_certifiedReducedFormRepInvariantFactorClassification?_eq_some_of_certificateDataChecks
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    {gens : List (ReducedFormRep (fieldDiscriminant d))}
    (hmem : gens ∈ tableGeneratorTuples (reducedFormRepList (fieldDiscriminant d))
      (invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
        (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg)).length)
    (hcheck :
      ({ factors := invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
            (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg),
          generators := gens } :
        TableStandardIsoSearchResult (ReducedFormRep (fieldDiscriminant d))).certificateDataChecks
        (reducedFormRepList (fieldDiscriminant d)) (reducedFormRepMulForTable hdneg)
          (principalReducedFormRep hdneg) = true) :
    letI := reducedFormRepCommGroup hdneg
    ∃ result, certifiedReducedFormRepInvariantFactorClassification? hdneg = some result ∧
      result.1 = invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
        (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg) := by
  letI := reducedFormRepCommGroup hdneg
  have hmemId :
      principalReducedFormRep hdneg ∈ reducedFormRepList (fieldDiscriminant d) :=
    reducedFormRepList_complete (fieldDiscriminant d) (principalReducedFormRep hdneg)
  have hne : (reducedFormRepList (fieldDiscriminant d)).length ≠ 0 :=
    ne_of_gt (List.length_pos_of_mem hmemId)
  obtain ⟨hclass, hresult⟩ :=
    exists_certifiedInvariantFactorClassification?_eq_some_of_certificateDataChecks
      (reducedFormRepList_complete (fieldDiscriminant d))
      (reducedFormRepMulForTable_eq_mul hdneg) hne hmem hcheck
  refine ⟨⟨invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
      (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg), hclass⟩, ?_, rfl⟩
  simpa [certifiedReducedFormRepInvariantFactorClassification?] using hresult

/-- If a full certificate-data candidate is present in the reduced-form
generator search space, then the proof-carrying class-group classifier succeeds
with the raw invariant factors. -/
theorem exists_certifiedClassGroupInvariantFactorClassification?_eq_some_of_certificateDataChecks
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    {gens : List (ReducedFormRep (fieldDiscriminant d))}
    (hmem : gens ∈ tableGeneratorTuples (reducedFormRepList (fieldDiscriminant d))
      (invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
        (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg)).length)
    (hcheck :
      ({ factors := invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
            (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg),
          generators := gens } :
        TableStandardIsoSearchResult (ReducedFormRep (fieldDiscriminant d))).certificateDataChecks
        (reducedFormRepList (fieldDiscriminant d)) (reducedFormRepMulForTable hdneg)
          (principalReducedFormRep hdneg) = true) :
    ∃ result, certifiedClassGroupInvariantFactorClassification? d hdneg = some result ∧
      result.1 = invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
        (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg) := by
  letI := reducedFormRepCommGroup hdneg
  obtain ⟨redResult, hred, hfactors⟩ :=
    exists_certifiedReducedFormRepInvariantFactorClassification?_eq_some_of_certificateDataChecks
      hdneg hmem hcheck
  refine ⟨⟨redResult.1, redResult.2.1, ?_⟩, ?_, hfactors⟩
  · exact IsInvariantFactorClassification.ofMulEquiv
      (reducedFormRepMulEquivClassGroup hdneg).symm redResult.2.2
  · simp [certifiedClassGroupInvariantFactorClassification?, hred]

/-- A full certificate-data candidate in the reduced-form generator search
space semantically classifies the public class-group standard output by the raw
invariant-factor list. -/
theorem classGroupStandardIsoType_classifies_rawInvariantFactors_of_certificateDataChecks
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    {gens : List (ReducedFormRep (fieldDiscriminant d))}
    (hmem : gens ∈ tableGeneratorTuples (reducedFormRepList (fieldDiscriminant d))
      (invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
        (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg)).length)
    (hcheck :
      ({ factors := invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
            (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg),
          generators := gens } :
        TableStandardIsoSearchResult (ReducedFormRep (fieldDiscriminant d))).certificateDataChecks
        (reducedFormRepList (fieldDiscriminant d)) (reducedFormRepMulForTable hdneg)
          (principalReducedFormRep hdneg) = true) :
    classGroupStandardIsoTypeOfImaginaryParameter d =
        StandardGroupIsoType.product
          (invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
            (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg)) ∧
      IsInvariantFactorClassification
        (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (invariantFactorsOfMulTable (reducedFormRepList (fieldDiscriminant d))
          (principalReducedFormRep hdneg) (reducedFormRepMulForTable hdneg)) := by
  obtain ⟨result, hresult, _hfactors⟩ :=
    exists_certifiedClassGroupInvariantFactorClassification?_eq_some_of_certificateDataChecks
      hdneg hmem hcheck
  exact classGroupStandardIsoType_classifies_rawInvariantFactors_of_certifiedClassGroupClassifier
    hdneg ⟨result, hresult⟩

/-- Compose a certified standard decomposition of reduced-form representatives
with the Cox bridge to the mathlib ideal class group. -/
noncomputable def classGroupStandardMulEquivOfReducedFormRepEquiv
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (e : letI := reducedFormRepCommGroup hdneg
      ReducedFormRep (fieldDiscriminant d) ≃*
        (classGroupStandardIsoTypeOfImaginaryParameter d).target) :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter d).target := by
  letI := reducedFormRepCommGroup hdneg
  exact (reducedFormRepMulEquivClassGroup hdneg).symm.trans e

/-- Compose a certified standard decomposition of reduced-form representatives
with the Cox bridge, after checking that the executable classifier returned the
same invariant-factor list. -/
noncomputable def classGroupStandardMulEquivOfReducedFormRepCertificate
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    {ns : List ℕ}
    (hns : classGroupStandardIsoTypeOfImaginaryParameter d = StandardGroupIsoType.product ns)
    (cert : letI := reducedFormRepCommGroup hdneg
      StandardZModProductMulEquivCertificate (ReducedFormRep (fieldDiscriminant d)) ns) :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter d).target := by
  rw [hns]
  letI := reducedFormRepCommGroup hdneg
  exact (reducedFormRepMulEquivClassGroup hdneg).symm.trans cert.toMulEquiv

/-- Compose a proof-carrying certified reduced-form classifier result with the
Cox bridge to the mathlib ideal class group. -/
noncomputable def classGroupStandardMulEquivOfCertifiedStandardIsoType
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (cert : letI := reducedFormRepCommGroup hdneg
      CertifiedTableStandardIsoType (ReducedFormRep (fieldDiscriminant d)))
    (hiso : classGroupStandardIsoTypeOfImaginaryParameter d =
      (letI := reducedFormRepCommGroup hdneg; cert.isoType)) :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter d).target := by
  letI := reducedFormRepCommGroup hdneg
  rw [hiso]
  exact (reducedFormRepMulEquivClassGroup hdneg).symm.trans cert.toMulEquivTarget

/-- Transport a reduced-form invariant-factor classification across the Cox
bridge to the ideal class group. -/
theorem classGroup_isInvariantFactorClassification_of_reducedFormRep
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) {ns : List ℕ}
    (h : letI := reducedFormRepCommGroup hdneg
      IsInvariantFactorClassification (ReducedFormRep (fieldDiscriminant d)) ns) :
    IsInvariantFactorClassification
      (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ns := by
  letI := reducedFormRepCommGroup hdneg
  exact IsInvariantFactorClassification.ofMulEquiv
    (reducedFormRepMulEquivClassGroup hdneg).symm h

/-- A proof-carrying reduced-form table classification gives a semantic
invariant-factor classification of the ideal class group. -/
theorem classGroup_isInvariantFactorClassification_of_certifiedStandardIsoType
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (cert : letI := reducedFormRepCommGroup hdneg
      CertifiedTableStandardIsoType (ReducedFormRep (fieldDiscriminant d))) :
    IsInvariantFactorClassification
      (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
      (letI := reducedFormRepCommGroup hdneg; cert.factors) := by
  letI := reducedFormRepCommGroup hdneg
  exact classGroup_isInvariantFactorClassification_of_reducedFormRep d hdneg
    cert.isInvariantFactorClassification

/-- If the reduced-form certified classifier matches the public class-group
standard type, then that public standard type is a semantic invariant-factor
classification of the ideal class group. -/
theorem classGroupStandardIsoType_classifies_of_certifiedStandardIsoType
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (cert : letI := reducedFormRepCommGroup hdneg
      CertifiedTableStandardIsoType (ReducedFormRep (fieldDiscriminant d)))
    (hiso : classGroupStandardIsoTypeOfImaginaryParameter d =
      (letI := reducedFormRepCommGroup hdneg; cert.isoType)) :
    ∃ ns, classGroupStandardIsoTypeOfImaginaryParameter d = StandardGroupIsoType.product ns ∧
      IsInvariantFactorClassification
        (ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ns := by
  letI := reducedFormRepCommGroup hdneg
  refine ⟨cert.factors, ?_, ?_⟩
  · rw [hiso, cert.isoType_eq]
  · exact classGroup_isInvariantFactorClassification_of_certifiedStandardIsoType d hdneg cert

/-- Compose a certified reduced-form table search with the Cox bridge to the
mathlib ideal class group. -/
noncomputable def classGroupStandardMulEquivOfCertifiedReducedFormSearch
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    {ns : List ℕ}
    (hns : classGroupStandardIsoTypeOfImaginaryParameter d = StandardGroupIsoType.product ns)
    (cert : letI := reducedFormRepCommGroup hdneg
      CertifiedTableStandardIsoSearchResult (ReducedFormRep (fieldDiscriminant d)))
    (hfactors : (letI := reducedFormRepCommGroup hdneg; cert.factors = ns)) :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter d).target := by
  letI := reducedFormRepCommGroup hdneg
  refine classGroupStandardMulEquivOfReducedFormRepCertificate d hdneg hns ?_
  simpa [hfactors] using cert.toMulEquivCertificate
end BinaryQuadraticForm
end QuadraticNumberFields
