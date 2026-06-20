/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Data.ZMod.Basic
import QuadraticNumberFields.ClassGroup.ClassNumber
import FormClassGroup.ClassGroup.Law
import FormClassGroup.ClassGroup.ClassNumber

/-!
# Computed Class Groups

This WIP module sketches the intended user-facing API for finite computed
models of ideal class groups of imaginary quadratic fields.

The backend is intentionally abstract here.  A future implementation can fill
the `sorry` boundaries using reduced binary quadratic forms, reduced ideals, or
another certified finite model without changing the facade exposed by this file.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace ClassGroup

/-- A finite model of the ideal class group of `ℚ(√d)`.

The type `Rep` is the finite representative type used by the backend.  The map
`toClassGroup` interprets representatives as elements of mathlib's ideal class
group, while `map_mul`, `map_inv`, `surjective`, and `injective` certify that the
finite model is exactly the class group. -/
structure ComputedClassGroup (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] where
  /-- The finite representative type used by this computed model. -/
  Rep : Type
  /-- Representatives are finite. -/
  instFintype : Fintype Rep
  /-- Representatives have decidable equality, so tables can be computed. -/
  instDecidableEq : DecidableEq Rep
  /-- The representative of the identity class. -/
  one : Rep
  /-- Multiplication in the finite representative model. -/
  mul : Rep → Rep → Rep
  /-- Inversion in the finite representative model. -/
  inv : Rep → Rep
  /-- Interpret a representative as an ideal class. -/
  toClassGroup : Rep → _root_.ClassGroup (𝓞 (Qsqrtd (d : ℚ)))
  /-- The representative identity maps to the ideal-class identity. -/
  map_one : toClassGroup one = 1
  /-- Representative multiplication agrees with ideal-class multiplication. -/
  map_mul : ∀ x y, toClassGroup (mul x y) = toClassGroup x * toClassGroup y
  /-- Representative inversion agrees with ideal-class inversion. -/
  map_inv : ∀ x, toClassGroup (inv x) = (toClassGroup x)⁻¹
  /-- Every ideal class is represented. -/
  surjective : Function.Surjective toClassGroup
  /-- Distinct representatives denote distinct ideal classes. -/
  injective : Function.Injective toClassGroup

namespace ComputedClassGroup

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The class number read off from a computed class-group model. -/
noncomputable def card (G : ComputedClassGroup d) : ℕ :=
  letI := G.instFintype
  Fintype.card G.Rep

/-- The multiplication table of a computed class-group model. -/
def mulTable (G : ComputedClassGroup d) : G.Rep → G.Rep → G.Rep :=
  G.mul

/-- Class-number-one shortcut for a computed class-group model: if the computed
representative type has cardinality one, every ideal class is trivial. -/
theorem eq_one_of_card_eq_one (G : ComputedClassGroup d) (hcard : G.card = 1)
    (C : _root_.ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) : C = 1 := by
  classical
  letI := G.instFintype
  have hcard' : Fintype.card G.Rep = 1 := by
    simpa [ComputedClassGroup.card] using hcard
  have hsub : Subsingleton G.Rep :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨x, hx⟩ := G.surjective C
  calc
    C = G.toClassGroup x := hx.symm
    _ = G.toClassGroup G.one := congrArg G.toClassGroup (Subsingleton.elim x G.one)
    _ = 1 := G.map_one

end ComputedClassGroup

end ClassGroup

/-! ## Facade API -/

/-- A future computed class-group model for `ℚ(√d)`.

The first backend is expected to use reduced positive definite forms and the
Cox equivalence; later backends may be ideal-native. -/
noncomputable def computedClassGroup (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    ClassGroup.ComputedClassGroup d := by
  sorry

/-- The class number obtained from the computed class-group facade. -/
noncomputable def computedClassNumber (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ℕ :=
  (computedClassGroup d).card

/-- The multiplication table obtained from the computed class-group facade. -/
noncomputable def classGroupMulTable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (computedClassGroup d).Rep → (computedClassGroup d).Rep → (computedClassGroup d).Rep :=
  (computedClassGroup d).mulTable

/-! ## Reduced-form backend target -/

/-- A certified finite computed class-group model for imaginary quadratic fields,
using reduced primitive positive definite binary quadratic forms. -/
noncomputable def reducedFormsComputedClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    ClassGroup.ComputedClassGroup d := by
  classical
  letI := BinaryQuadraticForm.reducedFormRepCommGroup (d := d) hdneg
  exact
    { Rep := BinaryQuadraticForm.ReducedFormRep (BinaryQuadraticForm.fieldDiscriminant d)
      instFintype := inferInstance
      instDecidableEq := inferInstance
      one := 1
      mul := fun x y => BinaryQuadraticForm.reducedFormRepMul hdneg x y
      inv := fun x => x⁻¹
      toClassGroup := BinaryQuadraticForm.reducedFormRepEquivClassGroup hdneg
      map_one := by
        simp [Equiv.one_def]
      map_mul := by
        intro x y
        exact BinaryQuadraticForm.reducedFormRepEquivClassGroup_mul hdneg x y
      map_inv := by
        intro x
        simp [Equiv.inv_def]
      surjective := (BinaryQuadraticForm.reducedFormRepEquivClassGroup hdneg).surjective
      injective := (BinaryQuadraticForm.reducedFormRepEquivClassGroup hdneg).injective }

/-- The reduced-form computed backend uses the finite reduced-form representative type. -/
theorem reducedFormsComputedClassGroup_rep
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    (reducedFormsComputedClassGroup d hdneg).Rep =
      BinaryQuadraticForm.ReducedFormRep (BinaryQuadraticForm.fieldDiscriminant d) :=
  rfl

/-- The reduced-form computed backend reads off the reduced-form enumeration
cardinality. -/
theorem reducedFormsComputedClassGroup_card
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    (reducedFormsComputedClassGroup d hdneg).card =
      (BinaryQuadraticForm.enumPrimitiveReducedForms
        (BinaryQuadraticForm.fieldDiscriminant d)).card := by
  simp [ClassGroup.ComputedClassGroup.card, reducedFormsComputedClassGroup]

/-- The reduced-form computed backend recovers the class number of `ℚ(√d)`. -/
theorem reducedFormsComputedClassGroup_card_eq_classNumberQsqrtd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    (reducedFormsComputedClassGroup d hdneg).card = classNumberQsqrtd d := by
  rw [reducedFormsComputedClassGroup_card, ← classNumberQsqrtd_eq_reducedForms_card d hdneg]

/-- The reduced-form computed backend uses the reduced-representative
multiplication table. -/
theorem reducedFormsComputedClassGroup_mul
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (Q R : BinaryQuadraticForm.ReducedFormRep (BinaryQuadraticForm.fieldDiscriminant d)) :
    (reducedFormsComputedClassGroup d hdneg).mul Q R =
      BinaryQuadraticForm.reducedFormRepMul hdneg Q R :=
  rfl

/-! ## Target examples -/

namespace Examples
namespace SqrtNeg14

/-- WIP backend certificate: the computed model for `ℚ(√-14)` identifies the
ideal class group with a cyclic group of order four. -/
theorem classGroup_cyclic_order_four_backend
    [Fact (Squarefree (-14 : ℤ))] [Fact ((-14 : ℤ) ≠ 1)] :
    Nonempty
      (_root_.ClassGroup (𝓞 (Qsqrtd ((-14 : ℤ) : ℚ))) ≃*
        Multiplicative (ZMod 4)) := by
  sorry

/-- Target interface: `ℚ(√-14)` has cyclic class group of order four. -/
theorem classGroup_cyclic_order_four
    [Fact (Squarefree (-14 : ℤ))] [Fact ((-14 : ℤ) ≠ 1)] :
    Nonempty
      (_root_.ClassGroup (𝓞 (Qsqrtd ((-14 : ℤ) : ℚ))) ≃*
        Multiplicative (ZMod 4)) := by
  exact classGroup_cyclic_order_four_backend

end SqrtNeg14

namespace SqrtNeg21

/-- WIP backend certificate: the computed model for `ℚ(√-21)` identifies the
ideal class group with the Klein four group. -/
theorem classGroup_klein_four_backend
    [Fact (Squarefree (-21 : ℤ))] [Fact ((-21 : ℤ) ≠ 1)] :
    Nonempty
      (_root_.ClassGroup (𝓞 (Qsqrtd ((-21 : ℤ) : ℚ))) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  sorry

/-- Target interface: `ℚ(√-21)` has Klein four class group. -/
theorem classGroup_klein_four
    [Fact (Squarefree (-21 : ℤ))] [Fact ((-21 : ℤ) ≠ 1)] :
    Nonempty
      (_root_.ClassGroup (𝓞 (Qsqrtd ((-21 : ℤ) : ℚ))) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  exact classGroup_klein_four_backend

end SqrtNeg21
end Examples

end QuadraticNumberFields
