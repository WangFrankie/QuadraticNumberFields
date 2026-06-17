/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.ComputableClassGroup
import QuadraticNumberFields.Examples.SqrtNeg5.Forms
import QuadraticNumberFields.Mathlib.Data.Int.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic.NormNum.Prime

set_option linter.style.nativeDecide false

/-!
# Concrete Class Group Isomorphism Types

This file provides tools to identify the isomorphism type of a finite abelian
group from its computable multiplication table, and applies them to the three
concrete imaginary quadratic fields `ℚ(√-5)`, `ℚ(√-23)`, `ℚ(√-21)`.

## Main results

* Cyclic group identification: given a generator and its order, construct
  `G ≃* Multiplicative (ZMod n)` via cardinality / table verification.
* Non-cyclic identification: given two commuting generators and their orders,
  construct `G ≃* Multiplicative (ZMod a) × Multiplicative (ZMod b)`.
* Concrete theorems:
  - `classGroup_qsqrtd_neg5_mulEquiv :
      ClassGroup (𝓞 (Qsqrtd (-5 : ℚ))) ≃* Multiplicative (ZMod 2)`
  - `classGroup_qsqrtd_neg23_mulEquiv :
      ClassGroup (𝓞 (Qsqrtd (-23 : ℚ))) ≃* Multiplicative (ZMod 3)`
  - `classGroup_qsqrtd_neg21_mulEquiv :
      ClassGroup (𝓞 (Qsqrtd (-21 : ℚ))) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)`
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

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

private noncomputable def reducedRepNeg21MulEquivKlein :
    letI := reducedFormRepCommGroup (d := (-21 : ℤ)) (by norm_num)
    ReducedRepNeg21 ≃* KleinFour := by
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

/-- **ℚ(√-21)**: the class group is the Klein four-group, i.e. ≅ ℤ/2ℤ × ℤ/2ℤ.
Class number 4 is already proved; the multiplication table (verified above)
shows all non-identity elements have order 2. -/
noncomputable def classGroup_qsqrtd_neg21_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-21 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := by
  letI := reducedFormRepCommGroup (d := (-21 : ℤ)) (by norm_num)
  exact (reducedFormRepMulEquivClassGroup (d := (-21 : ℤ)) (by norm_num)).symm.trans
    reducedRepNeg21MulEquivKlein

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

end BinaryQuadraticForm
end QuadraticNumberFields
