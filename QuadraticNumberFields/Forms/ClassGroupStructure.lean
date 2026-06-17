/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import FiniteAbelianSmith.Correctness
import QuadraticNumberFields.Forms.ComputableClassGroup
import QuadraticNumberFields.Examples.SqrtNeg5.Forms
import QuadraticNumberFields.Mathlib.Data.Int.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic.NormNum.Prime

set_option linter.style.nativeDecide false

/-!
# Concrete Class Group Isomorphism Types

This file computes invariant-factor isomorphism types for quadratic class groups
from reduced-form multiplication tables, and applies them to concrete imaginary
quadratic fields such as `ℚ(√-5)`, `ℚ(√-23)`, `ℚ(√-21)`, and `ℚ(√-231)`.

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
* Concrete theorems:
  - `classGroup_qsqrtd_neg5_mulEquiv :
      ClassGroup (𝓞 (Qsqrtd (-5 : ℚ))) ≃* Multiplicative (ZMod 2)`
  - `classGroup_qsqrtd_neg23_mulEquiv :
      ClassGroup (𝓞 (Qsqrtd (-23 : ℚ))) ≃* Multiplicative (ZMod 3)`
  - `classGroup_qsqrtd_neg21_mulEquiv :
      ClassGroup (𝓞 (Qsqrtd (-21 : ℚ))) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)`
  - `classGroup_qsqrtd_neg231_mulEquiv :
      ClassGroup (𝓞 (Qsqrtd (-231 : ℚ))) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 6)`
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

/-! ## Regression: abstract finite abelian tables -/

example : (standardZModProductElems []).length = 1 := by
  native_decide

example : (standardZModProductElems [2, 6]).length = 12 := by
  native_decide

example : (StandardGroupIsoType.product [2, 6]).targetElems.length = 12 := by
  native_decide

example :
    standardZModProductCoords [2, 6]
        (standardZModProductOfCoords [2, 6] [1, 5]) =
      [1, 5] := by
  native_decide

example :
    (standardZModProductElems [2, 2]).map (standardZModProductCoords [2, 2]) =
      [[0, 0], [0, 1], [1, 0], [1, 1]] := by
  native_decide

example :
    tableMapIsStandardMulEquiv (standardZModProductElems [2, 2])
        (fun x y => x * y) [2, 2] id = true := by
  native_decide

example :
    tableCoordinateMapIsStandardMulEquiv (standardZModProductElems [2, 6])
        (fun x y => x * y) [2, 6] (standardZModProductCoords [2, 6]) = true := by
  native_decide

example :
    standardIsoTypeOfMulTable (standardZModProductElems [2, 2])
        (1 : standardZModProduct [2, 2]) (fun x y => x * y) =
      StandardGroupIsoType.product [2, 2] := by
  native_decide

example :
    standardIsoTypeOfMulTable (standardZModProductElems [4, 2])
        (1 : standardZModProduct [4, 2]) (fun x y => x * y) =
      StandardGroupIsoType.product [2, 4] := by
  native_decide

example :
    standardIsoTypeOfMulTable (standardZModProductElems [2, 6])
        (1 : standardZModProduct [2, 6]) (fun x y => x * y) =
      StandardGroupIsoType.product [2, 6] := by
  native_decide

/-! ## Concrete isomorphism types -/

section ConcreteIsomorphisms

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

/-- `-23` is squarefree. -/
instance : Fact (Squarefree (-23 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

/-- `-23` is not `1`. -/
instance : Fact ((-23 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `-21` is squarefree. -/
instance : Fact (Squarefree (-21 : ℤ)) :=
  ⟨Int.squarefree_natAbs.mp (by
    change Squarefree (21 : ℕ)
    rw [show (21 : ℕ) = 3 * 7 by norm_num]
    rw [Nat.squarefree_mul (by norm_num : Nat.Coprime 3 7)]
    exact ⟨Nat.prime_three.squarefree, Nat.prime_seven.squarefree⟩)⟩

/-- `-21` is not `1`. -/
instance : Fact ((-21 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `-231` is squarefree. -/
instance : Fact (Squarefree (-231 : ℤ)) :=
  ⟨Int.squarefree_natAbs.mp (by native_decide : Squarefree (231 : ℕ))⟩

/-- `-231` is not `1`. -/
instance : Fact ((-231 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `ℚ(√-23)` has class number three, computed by reduced forms. -/
theorem classNumber_qsqrtd_neg23 :
    NumberField.classNumber (Qsqrtd ((-23 : ℤ) : ℚ)) = 3 := by
  change classNumberQsqrtd (-23) = 3
  compute_class_number_qsqrtd

/-- **ℚ(√-5)**: the class group is cyclic of order 2, i.e. ≅ ℤ/2ℤ.
This follows from class number 2 (already proved in `Computed.lean`) and the
fact that any non-principal ideal generates the group. -/
noncomputable def classGroup_qsqrtd_neg5_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-5 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 2) :=
  Examples.SqrtNeg5.classGroupMulEquivZMod2

/-- **ℚ(√-5)**: the class group, targeted at the computed standard type. -/
noncomputable def classGroup_qsqrtd_neg5_standardMulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-5 : ℤ) : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter (-5)).target := by
  rw [show classGroupStandardIsoTypeOfImaginaryParameter (-5) =
    StandardGroupIsoType.product [2] by native_decide]
  exact classGroup_qsqrtd_neg5_mulEquiv

/-- **ℚ(√-23)**: the class group is cyclic of order 3, i.e. ≅ ℤ/3ℤ.
Class number 3 is already proved; any non-principal ideal has order 3. -/
noncomputable def classGroup_qsqrtd_neg23_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq (p := 3)
    (G := ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))))
    (G' := Multiplicative (ZMod 3))
    (by
      rw [Nat.card_eq_fintype_card]
      simpa [NumberField.classNumber] using classNumber_qsqrtd_neg23)
    (by
      rw [Nat.card_eq_fintype_card]
      simp)

/-- **ℚ(√-23)**: the class group, targeted at the computed standard type. -/
noncomputable def classGroup_qsqrtd_neg23_standardMulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter (-23)).target := by
  rw [show classGroupStandardIsoTypeOfImaginaryParameter (-23) =
    StandardGroupIsoType.product [3] by native_decide]
  exact classGroup_qsqrtd_neg23_mulEquiv

private abbrev ReducedRepNeg21 :=
  ReducedFormRep (fieldDiscriminant (-21 : ℤ))

private abbrev KleinFour :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

private def reducedRepNeg21Id : ReducedRepNeg21 :=
  ⟨BinaryQuadraticForm.mk 1 0 21, by
    apply mem_enumPrimitiveReducedForms_of_reduced
    · norm_num [HasDiscriminant, disc, fieldDiscriminant]
    · norm_num [IsPositiveDefinite, disc]
    · norm_num [IsReduced]
    · unfold IsPrimitive
      norm_num⟩

private def reducedRepNeg21A : ReducedRepNeg21 :=
  ⟨BinaryQuadraticForm.mk 2 2 11, by
    apply mem_enumPrimitiveReducedForms_of_reduced
    · norm_num [HasDiscriminant, disc, fieldDiscriminant]
    · norm_num [IsPositiveDefinite, disc]
    · norm_num [IsReduced]
    · unfold IsPrimitive
      norm_num⟩

private def reducedRepNeg21B : ReducedRepNeg21 :=
  ⟨BinaryQuadraticForm.mk 3 0 7, by
    apply mem_enumPrimitiveReducedForms_of_reduced
    · norm_num [HasDiscriminant, disc, fieldDiscriminant]
    · norm_num [IsPositiveDefinite, disc]
    · norm_num [IsReduced]
    · unfold IsPrimitive
      norm_num⟩

private def reducedRepNeg21C : ReducedRepNeg21 :=
  ⟨BinaryQuadraticForm.mk 5 4 5, by
    apply mem_enumPrimitiveReducedForms_of_reduced
    · norm_num [HasDiscriminant, disc, fieldDiscriminant]
    · norm_num [IsPositiveDefinite, disc]
    · norm_num [IsReduced]
    · unfold IsPrimitive
      norm_num⟩

private def reducedRepNeg21Elems : List ReducedRepNeg21 :=
  [reducedRepNeg21Id, reducedRepNeg21A, reducedRepNeg21B, reducedRepNeg21C]

private def kleinFourId : KleinFour :=
  (Multiplicative.ofAdd (0 : ZMod 2), Multiplicative.ofAdd (0 : ZMod 2))

private def kleinFourA : KleinFour :=
  (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (0 : ZMod 2))

private def kleinFourB : KleinFour :=
  (Multiplicative.ofAdd (0 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2))

private def kleinFourC : KleinFour :=
  (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2))

private def reducedRepNeg21ToKlein (Q : ReducedRepNeg21) : KleinFour :=
  if Q = reducedRepNeg21Id then kleinFourId
  else if Q = reducedRepNeg21A then kleinFourA
  else if Q = reducedRepNeg21B then kleinFourB
  else kleinFourC

private def kleinFourToReducedRepNeg21 (x : KleinFour) : ReducedRepNeg21 :=
  if x = kleinFourId then reducedRepNeg21Id
  else if x = kleinFourA then reducedRepNeg21A
  else if x = kleinFourB then reducedRepNeg21B
  else reducedRepNeg21C

private def reducedRepNeg21MulForTable (Q R : ReducedRepNeg21) : ReducedRepNeg21 :=
  ⟨gaussMul (d := (-21 : ℤ)) (by norm_num) Q R,
    mem_enum_of_gaussMul (d := (-21 : ℤ)) (by norm_num) Q R⟩

example :
    tableMapIsStandardMulEquiv reducedRepNeg21Elems reducedRepNeg21MulForTable [2, 2]
      reducedRepNeg21ToKlein = true := by
  native_decide

private theorem enumPrimitiveReducedForms_neg84 :
    enumPrimitiveReducedForms (fieldDiscriminant (-21 : ℤ)) =
      ({BinaryQuadraticForm.mk 1 0 21, BinaryQuadraticForm.mk 2 2 11,
        BinaryQuadraticForm.mk 3 0 7, BinaryQuadraticForm.mk 5 4 5} :
        Finset BinaryQuadraticForm) := by
  native_decide

private theorem reducedFormNeg21_cases {Q : BinaryQuadraticForm}
    (hQ : Q ∈ enumPrimitiveReducedForms (fieldDiscriminant (-21 : ℤ))) :
    Q = BinaryQuadraticForm.mk 1 0 21 ∨
      Q = BinaryQuadraticForm.mk 2 2 11 ∨
      Q = BinaryQuadraticForm.mk 3 0 7 ∨
      Q = BinaryQuadraticForm.mk 5 4 5 := by
  rw [enumPrimitiveReducedForms_neg84] at hQ
  simpa using hQ

private theorem reducedRepNeg21_cases (Q : ReducedRepNeg21) :
    Q = reducedRepNeg21Id ∨ Q = reducedRepNeg21A ∨
      Q = reducedRepNeg21B ∨ Q = reducedRepNeg21C := by
  rcases reducedFormNeg21_cases Q.2 with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

private def reducedRepNeg21StandardCertificate :
    letI := reducedFormRepCommGroup (d := (-21 : ℤ)) (by norm_num)
    StandardZModProductMulEquivCertificate ReducedRepNeg21 [2, 2] := by
  letI := reducedFormRepCommGroup (d := (-21 : ℤ)) (by norm_num)
  refine
    { toFun := reducedRepNeg21ToKlein
      invFun := kleinFourToReducedRepNeg21
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro Q
    rcases reducedRepNeg21_cases Q with h | h | h | h <;> subst Q <;>
      decide +revert
  · intro x
    decide +revert
  · intro Q R
    rw [reducedFormRep_mul_eq_reducedFormRepMul (d := (-21 : ℤ)) (hdneg := by norm_num)]
    rw [← gaussMul_eq_reducedFormRepMul (d := (-21 : ℤ)) (hdneg := by norm_num) Q R]
    rcases reducedRepNeg21_cases Q with hQ | hQ | hQ | hQ <;> subst Q <;>
      rcases reducedRepNeg21_cases R with hR | hR | hR | hR <;> subst R <;>
        native_decide +revert

private noncomputable def reducedRepNeg21MulEquivKlein :
    letI := reducedFormRepCommGroup (d := (-21 : ℤ)) (by norm_num)
    ReducedRepNeg21 ≃* KleinFour := by
  letI := reducedFormRepCommGroup (d := (-21 : ℤ)) (by norm_num)
  exact reducedRepNeg21StandardCertificate.toMulEquiv

/-- **ℚ(√-21)**: the class group is the Klein four-group, i.e. ≅ ℤ/2ℤ × ℤ/2ℤ.
Class number 4 is already proved; the multiplication table (verified above)
shows all non-identity elements have order 2. -/
noncomputable def classGroup_qsqrtd_neg21_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-21 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := by
  letI := reducedFormRepCommGroup (d := (-21 : ℤ)) (by norm_num)
  exact (reducedFormRepMulEquivClassGroup (d := (-21 : ℤ)) (by norm_num)).symm.trans
    reducedRepNeg21MulEquivKlein

/-- **ℚ(√-21)**: the class group, targeted at the computed standard type. -/
noncomputable def classGroup_qsqrtd_neg21_standardMulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-21 : ℤ) : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter (-21)).target :=
  classGroupStandardMulEquivOfReducedFormRepCertificate (-21) (by norm_num)
    (by native_decide) reducedRepNeg21StandardCertificate

private abbrev ReducedRepNeg231 :=
  ReducedFormRep (fieldDiscriminant (-231 : ℤ))

private abbrev StandardNeg231 :=
  standardZModProduct [2, 6]

private def formsNeg231 : List BinaryQuadraticForm :=
  enumPrimitiveReducedFormsList (fieldDiscriminant (-231 : ℤ))

private def reducedRepNeg231 (i : Fin formsNeg231.length) : ReducedRepNeg231 :=
  ⟨formsNeg231[i], by
    have hmem : formsNeg231[i] ∈ formsNeg231 := List.getElem_mem i.2
    simpa [ReducedRepNeg231, formsNeg231, enumPrimitiveReducedForms] using hmem⟩

private def reducedRepNeg231Elems : List ReducedRepNeg231 :=
  (List.range formsNeg231.length).attach.map fun i =>
    reducedRepNeg231 ⟨i.1, List.mem_range.mp i.2⟩

private def reducedRepNeg231MulForTable (Q R : ReducedRepNeg231) : ReducedRepNeg231 :=
  ⟨gaussMul (d := (-231 : ℤ)) (by norm_num) Q R,
    mem_enum_of_gaussMul (d := (-231 : ℤ)) (by norm_num) Q R⟩

private def reducedRepNeg231StandardSearchResult :
    TableStandardIsoSearchResult ReducedRepNeg231 :=
  (tableCertifiedStandardIsoSearchResult? reducedRepNeg231Elems
    (reducedRepNeg231 ⟨0, by native_decide⟩) reducedRepNeg231MulForTable).get
      (by native_decide)

private theorem reducedRepNeg231StandardSearchResult_factors :
    reducedRepNeg231StandardSearchResult.factors = [2, 6] := by
  native_decide

private theorem reducedRepNeg231StandardSearchResult_search_eq :
    tableCertifiedStandardIsoSearchResult? reducedRepNeg231Elems
        (reducedRepNeg231 ⟨0, by native_decide⟩) reducedRepNeg231MulForTable =
      some reducedRepNeg231StandardSearchResult := by
  rw [reducedRepNeg231StandardSearchResult]
  exact (Option.some_get (by native_decide)).symm

private theorem reducedRepNeg231Elems_complete :
    ∀ Q : ReducedRepNeg231, Q ∈ reducedRepNeg231Elems := by
  native_decide +revert

private theorem reducedRepNeg231MulForTable_eq_mul :
    letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
    ∀ Q R : ReducedRepNeg231,
      reducedRepNeg231MulForTable Q R = Q * R := by
  letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
  intro Q R
  rw [reducedFormRep_mul_eq_reducedFormRepMul (d := (-231 : ℤ)) (hdneg := by norm_num)]
  rw [← gaussMul_eq_reducedFormRepMul (d := (-231 : ℤ)) (hdneg := by norm_num) Q R]
  rfl

private noncomputable def reducedRepNeg231CertifiedSearchResult :
    letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
    CertifiedTableStandardIsoSearchResult ReducedRepNeg231 := by
  letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
  exact CertifiedTableStandardIsoSearchResult.ofSearch reducedRepNeg231Elems
    reducedRepNeg231MulForTable (reducedRepNeg231 ⟨0, by native_decide⟩)
    reducedRepNeg231StandardSearchResult reducedRepNeg231StandardSearchResult_search_eq
    reducedRepNeg231Elems_complete reducedRepNeg231MulForTable_eq_mul

private noncomputable def reducedRepNeg231CertifiedStandardIsoType :
    letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
    CertifiedTableStandardIsoType ReducedRepNeg231 := by
  letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
  refine CertifiedTableStandardIsoType.ofCertifiedSearch reducedRepNeg231CertifiedSearchResult ?_
  change reducedRepNeg231Elems.length ≠ 0
  native_decide

private noncomputable def reducedRepNeg231StandardCertificate :
    letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
    StandardZModProductMulEquivCertificate ReducedRepNeg231 [2, 6] := by
  letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
  have hcert : StandardZModProductMulEquivCertificate ReducedRepNeg231
      reducedRepNeg231StandardSearchResult.factors :=
    reducedRepNeg231CertifiedSearchResult.toMulEquivCertificate
  simpa [reducedRepNeg231StandardSearchResult_factors] using hcert

private noncomputable def reducedRepNeg231MulEquivStandard :
    letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
    ReducedRepNeg231 ≃* StandardNeg231 := by
  letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
  exact reducedRepNeg231StandardCertificate.toMulEquiv

/-- **ℚ(√-231)**: the class group is `ℤ/2ℤ × ℤ/6ℤ`. -/
noncomputable def classGroup_qsqrtd_neg231_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-231 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 6) := by
  letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
  exact (reducedFormRepMulEquivClassGroup (d := (-231 : ℤ)) (by norm_num)).symm.trans
    reducedRepNeg231MulEquivStandard

/-- **ℚ(√-231)**: the class group, targeted at the computed standard type. -/
noncomputable def classGroup_qsqrtd_neg231_standardMulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-231 : ℤ) : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter (-231)).target := by
  letI := reducedFormRepCommGroup (d := (-231 : ℤ)) (by norm_num)
  refine classGroupStandardMulEquivOfCertifiedStandardIsoType (-231) (by norm_num)
    reducedRepNeg231CertifiedStandardIsoType ?_
  rw [show reducedRepNeg231CertifiedStandardIsoType.isoType =
    StandardGroupIsoType.product [2, 6] by
      change StandardGroupIsoType.product reducedRepNeg231StandardSearchResult.factors =
        StandardGroupIsoType.product [2, 6]
      rw [reducedRepNeg231StandardSearchResult_factors]]
  native_decide

end ConcreteIsomorphisms

/-! ## Regression: concrete multiplication tables

For each concrete discriminant, we verify the full multiplication table using
the `composeAndReduce` pipeline and `native_decide`. -/

section RegressionConcrete

/-- Forms for discriminant -20 (ℚ(√-5)): primitive reduced forms are `(1,0,5)` and `(2,2,3)`.
Class number 2, cyclic group ≅ ℤ/2ℤ. -/
def f5_id : BinaryQuadraticForm := BinaryQuadraticForm.mk 1 0 5
def f5_non : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 2 3

example : f5_id.disc = -20 := by native_decide
example : f5_non.disc = -20 := by native_decide
example : f5_id.IsPrimitive := by unfold IsPrimitive; native_decide
example : f5_non.IsPrimitive := by unfold IsPrimitive; native_decide

/-- Order-2 check for ℚ(√-5): the non-identity element squared is identity. -/
def composeAndReduce5 := @composeAndReduce
example : composeAndReduce5 f5_non f5_non = f5_id := by
  native_decide

/-- Forms for discriminant -23 (ℚ(√-23)): primitive reduced forms are
`(1,1,6)`, `(2,1,3)`, `(2,-1,3)`.  Class number 3, cyclic group ≅ ℤ/3ℤ. -/
def f23_id : BinaryQuadraticForm := BinaryQuadraticForm.mk 1 1 6
def f23_a : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 1 3
def f23_b : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 (-1) 3

example : f23_id.disc = -23 := by native_decide
example : f23_a.disc = -23 := by native_decide
example : f23_b.disc = -23 := by native_decide

/-- The non-identity elements have order 3: a³ = b³ = id, a² = b. -/
def composeAndReduce23 := @composeAndReduce
example : composeAndReduce23 f23_a (composeAndReduce23 f23_a f23_a) = f23_id := by
  native_decide
example : composeAndReduce23 f23_b (composeAndReduce23 f23_b f23_b) = f23_id := by
  native_decide
example : composeAndReduce23 f23_a f23_a = f23_b := by
  native_decide
example : composeAndReduce23 f23_a f23_b = f23_id := by
  native_decide

/-- The Klein four-group for ℚ(√-21) (discriminant -84) was fully verified in
`ComputableClassGroup.lean`.  We re-state the key relations here. -/
def f21_id : BinaryQuadraticForm := BinaryQuadraticForm.mk 1 0 21
def f21_A : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 2 11
def f21_B : BinaryQuadraticForm := BinaryQuadraticForm.mk 3 0 7
def f21_C : BinaryQuadraticForm := BinaryQuadraticForm.mk 5 4 5

-- Re-verify the full Klein four-group table (all 10 non-trivial entries)
def composeAndReduce21 := @composeAndReduce
example : composeAndReduce21 f21_A f21_A = f21_id := by native_decide
example : composeAndReduce21 f21_B f21_B = f21_id := by native_decide
example : composeAndReduce21 f21_C f21_C = f21_id := by native_decide
example : composeAndReduce21 f21_A f21_B = f21_C := by native_decide
example : composeAndReduce21 f21_A f21_C = f21_B := by native_decide
example : composeAndReduce21 f21_B f21_C = f21_A := by native_decide
example : composeAndReduce21 f21_id f21_A = f21_A := by native_decide
example : composeAndReduce21 f21_id f21_B = f21_B := by native_decide
example : composeAndReduce21 f21_id f21_C = f21_C := by native_decide
example : composeAndReduce21 f21_id f21_id = f21_id := by native_decide

end RegressionConcrete

/-! ## Regression: standard isomorphism type output -/

example :
    classGroupStandardIsoTypeOfImaginaryParameter (-5) =
      StandardGroupIsoType.product [2] := by
  native_decide

example :
    classGroupStandardIsoTypeOfImaginaryParameter (-23) =
      StandardGroupIsoType.product [3] := by
  native_decide

example :
    classGroupStandardIsoTypeOfImaginaryParameter (-21) =
      StandardGroupIsoType.product [2, 2] := by
  native_decide

example :
    (classGroupStandardIsoTypeOfImaginaryParameter (-21)).target =
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  rw [show classGroupStandardIsoTypeOfImaginaryParameter (-21) =
    StandardGroupIsoType.product [2, 2] by native_decide]
  rfl

noncomputable example :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-21 : ℤ) : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter (-21)).target := by
  exact classGroup_qsqrtd_neg21_standardMulEquiv

example :
    classGroupStandardIsoTypeOfImaginaryParameter (-231) =
      StandardGroupIsoType.product [2, 6] := by
  native_decide

example : (classGroupStandardIsoTypeOfImaginaryParameter (-231)).targetElems.length = 12 := by
  native_decide

example :
    (classGroupStandardIsoTypeOfImaginaryParameter (-231)).target =
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 6)) := by
  rw [show classGroupStandardIsoTypeOfImaginaryParameter (-231) =
    StandardGroupIsoType.product [2, 6] by native_decide]
  rfl

noncomputable example :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-231 : ℤ) : ℚ))) ≃*
      (classGroupStandardIsoTypeOfImaginaryParameter (-231)).target := by
  exact classGroup_qsqrtd_neg231_standardMulEquiv

end BinaryQuadraticForm
end QuadraticNumberFields
