/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Examples.ClassGroupStructure.ReducedFormTables
import QuadraticNumberFields.Examples.SqrtNeg5.Forms
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Class Group Structure Computations

This file is the final layer of the class-group structure examples.  The
preceding example files check the standard finite-abelian targets and the raw
reduced-form multiplication tables.  This file transports those certified
reduced-form classifications to readable ideal-class-group isomorphisms such as
`ClassGroup (𝓞 (ℚ(√-231))) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 6)`.
-/

set_option linter.style.nativeDecide false

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

open FiniteAbelianSmith

/-! ## Input facts for the concrete fields -/

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

/-! ## Direct cyclic outputs -/

/-- **ℚ(√-5)**: the class group is cyclic of order 2, i.e. `ℤ/2ℤ`.
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

/-- **ℚ(√-23)**: the class group is cyclic of order 3, i.e. `ℤ/3ℤ`.
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

/-! ## Certified Klein-four output for `ℚ(√-21)` -/

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

/-! ## Certified `ℤ/2ℤ × ℤ/6ℤ` output for `ℚ(√-231)` -/

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

/-! ## Public standard-output checks -/

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

end ConcreteIsomorphisms

end BinaryQuadraticForm
end QuadraticNumberFields
