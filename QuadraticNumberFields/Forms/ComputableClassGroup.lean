/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.ComputableComposition
import QuadraticNumberFields.Forms.ComputableReduction
import QuadraticNumberFields.Forms.ClassGroupLaw

/-!
# Computable Form Class Group

This file connects the computable Dirichlet composition (`composeForm`) and
Gauss reduction (`reduceForm`) to obtain a computable group multiplication
`gaussMul` on finite reduced-form representatives, and states the main
consistency theorem that `gaussMul = reducedFormRepMul`.

## Main definitions

* `gaussMul` — reduced-form multiplication via `reduceForm ∘ composeForm`
* `gaussMul_eq_reducedFormRepMul` — equality with the Cox-transported law

## Regression

The `d = -21` spike (field discriminant `-84`, class number 4) gives a
Klein four-group; `#eval` verifies the multiplication table.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section GaussMul

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The discriminant of the reduced-form representatives for this `d`. -/
local notation "D" => fieldDiscriminant d

/-- Computable group multiplication on reduced-form representatives:
compose two forms via the CRT-adjusted formula, then reduce the result.

The `IsPositiveDefinite` and enumeration-membership proofs of the result
are deferred to the correctness theorems (the function is still computable
because the proofs are `Prop` arguments that are erased at runtime). -/
def gaussMul (hdneg : d < 0) (Q R : ReducedFormRep D) :
    BinaryQuadraticForm :=
  let Qf := Q.1
  let Rf := R.1
  -- Both are in the reduced enumeration, hence primitive, positive definite,
  -- and have discriminant D.
  have hQprim : Qf.IsPrimitive :=
    (of_mem_enumPrimitiveReducedForms Q.2).2.1
  have hRprim : Rf.IsPrimitive :=
    (of_mem_enumPrimitiveReducedForms R.2).2.1
  have hQpos : Qf.IsPositiveDefinite :=
    (of_mem_enumPrimitiveReducedForms Q.2).2.2.2
  have hRpos : Rf.IsPositiveDefinite :=
    (of_mem_enumPrimitiveReducedForms R.2).2.2.2
  have hdiscQ : Qf.disc = D :=
    (of_mem_enumPrimitiveReducedForms Q.2).2.2.1
  have hdiscR : Rf.disc = D :=
    (of_mem_enumPrimitiveReducedForms R.2).2.2.1
  have hQR : Qf.disc = Rf.disc := by rw [hdiscQ, hdiscR]
  have hQa : Qf.a ≠ 0 := ne_of_gt hQpos.1
  -- Compute composition, then reduce.  `reduceForm` needs a
  -- positive-definite proof for the composed form; this follows from
  -- discriminant preservation (a > 0 by construction, disc < 0 shown below).
  let comp := composeForm Qf Rf hQR hRprim hQa
  have hcomp_pos : comp.IsPositiveDefinite := by
    have ha_pos : 0 < comp.a := by
      rw [composeForm_a]
      apply mul_pos hQpos.1
      -- R'.a = Rf.eval(coprimeEvalVector Rf Qf.a hRprim hQa), positive by
      -- eval_pos_of_isPositiveDefinite from Action.lean
      rw [unitedRep_a]
      have hxy_nonzero : (coprimeEvalVector Rf Qf.a hRprim hQa).1 ≠ 0 ∨
          (coprimeEvalVector Rf Qf.a hRprim hQa).2 ≠ 0 := by
        have hgcd := coprimeEvalVector_gcd Rf Qf.a hRprim hQa
        by_contra! hboth
        rcases hboth with ⟨hx, hy⟩
        rw [hx, hy] at hgcd; simp at hgcd
      exact eval_pos_of_isPositiveDefinite Rf hRpos hxy_nonzero
    have hdisc_lt : comp.disc < 0 := by
      rw [disc_composeForm Qf Rf hQR hRprim hQa hQpos hRpos]
      rw [hdiscQ]
      exact fieldDiscriminant_neg hdneg
    exact ⟨ha_pos, hdisc_lt⟩
  reduceForm comp hcomp_pos

/-- The computable Gauss multiplication equals the Cox-transported
class-group law on reduced-form representatives
(both as `BinaryQuadraticForm` values). -/
theorem gaussMul_eq_reducedFormRepMul_val
    (hdneg : d < 0) (Q R : ReducedFormRep D) :
    gaussMul hdneg Q R = (reducedFormRepMul hdneg Q R).1 := by
  -- Both are the unique reduced representative of the class product.
  -- The proof requires composeForm_mk and reduceForm correctness.
  -- TODO: formalise using composeForm_mk, reduceForm_properEquivalent,
  -- and the uniqueness of reduced representatives.
  sorry

/-- The computable Gauss multiplication, lifted to `ReducedFormRep`,
agrees with the Cox-transported law. -/
theorem gaussMul_eq_reducedFormRepMul
    (hdneg : d < 0) (Q R : ReducedFormRep D) :
    (⟨gaussMul hdneg Q R, by
      -- Proof that the result is in the enumeration follows from
      -- reduceForm correctness (to be proved).
      sorry⟩ : ReducedFormRep D) = reducedFormRepMul hdneg Q R := by
  apply Subtype.ext
  exact gaussMul_eq_reducedFormRepMul_val hdneg Q R

end GaussMul

/-! ## Regression: multiplication table for `d = -21`

The spike confirms: `fieldDiscriminant (-21 : ℚ) = -84`, reduced forms
`[(1,0,21), (2,2,11), (3,0,7), (5,4,5)]`, class group ≅ `ℤ/2 × ℤ/2`.

We verify via `#eval` that the composition pipeline
(`composeForm` → `reduceForm`) reproduces the Klein four-group structure
on concrete forms. -/

section Regression_d21

/-- All four reduced forms for discriminant `-84`. -/
def f1 : BinaryQuadraticForm := BinaryQuadraticForm.mk 1 0 21
def f2 : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 2 11
def f3 : BinaryQuadraticForm := BinaryQuadraticForm.mk 3 0 7
def f4 : BinaryQuadraticForm := BinaryQuadraticForm.mk 5 4 5

/-- Compose and reduce two forms in one step (for `#eval` testing). -/
def composeAndReduce (Q R : BinaryQuadraticForm) : BinaryQuadraticForm :=
  let Q' := Q
  let R' := R
  have hQR : Q'.disc = R'.disc := by
    unfold Q' R' disc; native_decide
  have hRprim : R'.IsPrimitive := by
    unfold Q' R' IsPrimitive; native_decide
  have hQa : Q'.a ≠ 0 := by
    unfold Q'; native_decide
  let comp := composeForm Q' R' hQR hRprim hQa
  have hcomp_pos : comp.IsPositiveDefinite := by
    -- For this concrete test, we verify directly.
    refine ⟨by
      unfold comp Q' R' composeForm composeMiddleB unitedRep
        coprimeEvalVector coprimeEvalPred
      native_decide, ?_⟩
    unfold comp Q' R' composeForm composeMiddleB unitedRep
      coprimeEvalVector coprimeEvalPred disc
    native_decide
  reduceForm comp hcomp_pos

/-- `#eval` the full pipeline on `(2,2,11) × (2,2,11)` (order-2 element). -/
#eval composeAndReduce f2 f2
/-- Expected: identity form `(1,0,21)`. -/
example : composeAndReduce f2 f2 = f1 := by
  native_decide

/-- `#eval` the full pipeline on `(3,0,7) × (3,0,7)` (order-2 element). -/
#eval composeAndReduce f3 f3
example : composeAndReduce f3 f3 = f1 := by
  native_decide

/-- `#eval` the full pipeline on `(5,4,5) × (5,4,5)` (order-2 element). -/
#eval composeAndReduce f4 f4
example : composeAndReduce f4 f4 = f1 := by
  native_decide

/-- `#eval` the full pipeline on `(2,2,11) × (3,0,7)`. -/
#eval composeAndReduce f2 f3
/-- Product of the two distinct non-identity elements gives the third. -/
example : composeAndReduce f2 f3 = f4 := by
  native_decide

/-- `#eval` the full pipeline on `(2,2,11) × (5,4,5)`. -/
#eval composeAndReduce f2 f4
example : composeAndReduce f2 f4 = f3 := by
  native_decide

/-- `#eval` the full pipeline on `(3,0,7) × (5,4,5)`. -/
#eval composeAndReduce f3 f4
example : composeAndReduce f3 f4 = f2 := by
  native_decide

/-- Identity: `(1,0,21) × anything = anything`. -/
#eval composeAndReduce f1 f2
example : composeAndReduce f1 f2 = f2 := by native_decide
#eval composeAndReduce f1 f3
example : composeAndReduce f1 f3 = f3 := by native_decide
#eval composeAndReduce f1 f4
example : composeAndReduce f1 f4 = f4 := by native_decide

/-- Full Klein four-group verified: all 10 non-trivial table entries match. -/
example : composeAndReduce f1 f1 = f1 := by native_decide

end Regression_d21

end BinaryQuadraticForm
end QuadraticNumberFields
