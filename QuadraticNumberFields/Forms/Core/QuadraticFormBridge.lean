/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Core.Action
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Ring

/-!
# Bridge to mathlib Quadratic Forms

This file identifies the project-owned coordinate model of integral binary
quadratic forms with mathlib's structural `QuadraticForm` API on `ℤ²`.

The coordinate model remains the computable representation used by reduction,
enumeration, and Gauss composition.  The bridge in this file is the explicit
mathematical equivalence between a triple `(a, b, c)` and the quadratic form
`(x, y) ↦ a*x^2 + b*x*y + c*y^2`.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

open Matrix

local instance : Invertible (2 : ℚ) :=
  invertibleOfNonzero (by norm_num : (2 : ℚ) ≠ 0)

/-! ## Coordinates and coefficient accessors -/

/-- Coordinates in the standard basis of a two-dimensional coordinate module. -/
def coordVec {R : Type*} (x y : R) : Fin 2 → R :=
  ![x, y]

/-- The mathlib structural type corresponding to integral binary quadratic forms. -/
abbrev IntegralQuadraticForm : Type :=
  QuadraticForm ℤ (Fin 2 → ℤ)

/-- The mathlib structural type corresponding to rational binary quadratic forms. -/
abbrev RationalQuadraticForm : Type :=
  QuadraticForm ℚ (Fin 2 → ℚ)

/-- The `X²` coefficient of a mathlib binary quadratic form over `ℤ`. -/
def coeffA (Q : IntegralQuadraticForm) : ℤ :=
  Q (coordVec 1 0)

/-- The `XY` coefficient of a mathlib binary quadratic form over `ℤ`. -/
def coeffB (Q : IntegralQuadraticForm) : ℤ :=
  Q (coordVec 1 1) - Q (coordVec 1 0) - Q (coordVec 0 1)

/-- The `Y²` coefficient of a mathlib binary quadratic form over `ℤ`. -/
def coeffC (Q : IntegralQuadraticForm) : ℤ :=
  Q (coordVec 0 1)

/-- The classical binary-form discriminant `b² - 4ac`.

This is intentionally separate from mathlib's `QuadraticMap.discr`, whose matrix
determinant normalization requires an invertibility hypothesis for `2`.
-/
def classicalDisc (Q : IntegralQuadraticForm) : ℤ :=
  coeffB Q ^ 2 - 4 * coeffA Q * coeffC Q

/-! ## Converting between representations -/

/-- Interpret a coordinate binary quadratic form as a mathlib quadratic form. -/
def toQuadraticForm (Q : BinaryQuadraticForm) : IntegralQuadraticForm :=
  Q.a • QuadraticMap.proj (R := ℤ) (n := Fin 2) 0 0 +
    Q.b • QuadraticMap.proj (R := ℤ) (n := Fin 2) 0 1 +
    Q.c • QuadraticMap.proj (R := ℤ) (n := Fin 2) 1 1

/-- Recover the coordinate triple of a mathlib binary quadratic form over `ℤ`. -/
def ofQuadraticForm (Q : IntegralQuadraticForm) : BinaryQuadraticForm where
  a := coeffA Q
  b := coeffB Q
  c := coeffC Q

@[simp]
theorem toQuadraticForm_apply (Q : BinaryQuadraticForm) (v : Fin 2 → ℤ) :
    toQuadraticForm Q v = Q.eval (v 0) (v 1) := by
  simp [toQuadraticForm, eval]
  ring

@[simp]
theorem toQuadraticForm_coordVec (Q : BinaryQuadraticForm) (x y : ℤ) :
    toQuadraticForm Q (coordVec x y) = Q.eval x y := by
  simp [coordVec]

@[simp]
theorem coeffA_toQuadraticForm (Q : BinaryQuadraticForm) :
    coeffA (toQuadraticForm Q) = Q.a := by
  simp [coeffA, coordVec, eval]

@[simp]
theorem coeffB_toQuadraticForm (Q : BinaryQuadraticForm) :
    coeffB (toQuadraticForm Q) = Q.b := by
  simp [coeffB, coordVec, eval]
  ring_nf

@[simp]
theorem coeffC_toQuadraticForm (Q : BinaryQuadraticForm) :
    coeffC (toQuadraticForm Q) = Q.c := by
  simp [coeffC, coordVec, eval]

@[simp]
theorem ofQuadraticForm_toQuadraticForm (Q : BinaryQuadraticForm) :
    ofQuadraticForm (toQuadraticForm Q) = Q := by
  ext <;> simp [ofQuadraticForm]

/-- Every mathlib binary quadratic form over `ℤ` is determined by its three
standard coefficients. -/
theorem apply_eq_coeffs (Q : IntegralQuadraticForm) (v : Fin 2 → ℤ) :
    Q v = coeffA Q * (v 0) ^ 2 + coeffB Q * (v 0) * (v 1) + coeffC Q * (v 1) ^ 2 := by
  let e0 : Fin 2 → ℤ := coordVec 1 0
  let e1 : Fin 2 → ℤ := coordVec 0 1
  have hv : v = v 0 • e0 + v 1 • e1 := by
    ext i
    fin_cases i <;> simp [e0, e1, coordVec]
  rw [hv]
  rw [QuadraticMap.map_add (fun w => Q w) (v 0 • e0) (v 1 • e1)]
  rw [Q.map_smul, Q.map_smul]
  rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  simp [coeffA, coeffB, coeffC, e0, e1, coordVec, QuadraticMap.polar]
  ring

@[simp]
theorem ofQuadraticForm_eval (Q : IntegralQuadraticForm) (x y : ℤ) :
    (ofQuadraticForm Q).eval x y =
      coeffA Q * x ^ 2 + coeffB Q * x * y + coeffC Q * y ^ 2 :=
  rfl

@[simp]
theorem toQuadraticForm_ofQuadraticForm (Q : IntegralQuadraticForm) :
    toQuadraticForm (ofQuadraticForm Q) = Q := by
  apply QuadraticMap.ext
  intro v
  rw [toQuadraticForm_apply, ofQuadraticForm_eval, apply_eq_coeffs]

/-- The equivalence between the coordinate model and mathlib quadratic forms over `ℤ²`. -/
def equivQuadraticForm : BinaryQuadraticForm ≃ IntegralQuadraticForm where
  toFun := toQuadraticForm
  invFun := ofQuadraticForm
  left_inv := ofQuadraticForm_toQuadraticForm
  right_inv := toQuadraticForm_ofQuadraticForm

@[simp]
theorem classicalDisc_toQuadraticForm (Q : BinaryQuadraticForm) :
    classicalDisc (toQuadraticForm Q) = Q.disc := by
  simp [classicalDisc, disc]

@[simp]
theorem disc_ofQuadraticForm (Q : IntegralQuadraticForm) :
    (ofQuadraticForm Q).disc = classicalDisc Q := by
  simp [ofQuadraticForm, classicalDisc, disc]

/-! ## Rational discriminant normalization -/

/-- Matrix representing `Q` as a mathlib quadratic form over `ℚ`. -/
def toRationalQuadraticFormMatrix (Q : BinaryQuadraticForm) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(Q.a : ℚ), (Q.b : ℚ); 0, (Q.c : ℚ)]

/-- Interpret a coordinate binary quadratic form as a rational mathlib quadratic form. -/
def toRationalQuadraticForm (Q : BinaryQuadraticForm) : RationalQuadraticForm :=
  (toRationalQuadraticFormMatrix Q).toQuadraticMap'

/-- The rational bridge evaluates to the same polynomial with rational coefficients. -/
theorem toRationalQuadraticForm_apply (Q : BinaryQuadraticForm) (x y : ℚ) :
    Q.toRationalQuadraticForm (coordVec x y) =
      (Q.a : ℚ) * x ^ 2 + (Q.b : ℚ) * x * y + (Q.c : ℚ) * y ^ 2 := by
  rcases Q with ⟨a, b, c⟩
  simp [toRationalQuadraticForm, toRationalQuadraticFormMatrix, coordVec,
    Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec]
  ring_nf

/-- The associated rational matrix has the classical half-cross-term shape. -/
theorem toMatrix'_toRationalQuadraticForm (Q : BinaryQuadraticForm) :
    Q.toRationalQuadraticForm.toMatrix' =
      !![(Q.a : ℚ), (Q.b : ℚ) / 2; (Q.b : ℚ) / 2, (Q.c : ℚ)] := by
  rcases Q with ⟨a, b, c⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toRationalQuadraticForm, toRationalQuadraticFormMatrix, QuadraticMap.toMatrix',
      QuadraticMap.associated, QuadraticMap.associatedHom, LinearMap.toMatrix₂'_apply,
      Matrix.toQuadraticMap', LinearMap.BilinMap.polar_toQuadraticMap,
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', dotProduct,
      Matrix.mulVec] <;> ring_nf

/-- Mathlib's rational matrix discriminant is `-1/4` times the classical discriminant. -/
theorem discr_toRationalQuadraticForm (Q : BinaryQuadraticForm) :
    -4 * QuadraticMap.discr Q.toRationalQuadraticForm = (Q.disc : ℚ) := by
  rw [QuadraticMap.discr, toMatrix'_toRationalQuadraticForm]
  rcases Q with ⟨a, b, c⟩
  simp [Matrix.det_fin_two_of, disc]
  ring_nf

/-! ## Compatibility with the `SL₂(ℤ)` action -/

/-- The linear map on `ℤ²` induced by an `SL₂(ℤ)` matrix. -/
def linearMapOfSL2Z (g : SL2Z) : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v :=
    coordVec
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * v 0 +
        (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * v 1)
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * v 0 +
        (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * v 1)
  map_add' v w := by
    ext i
    fin_cases i <;> simp [coordVec] <;> ring
  map_smul' n v := by
    ext i
    fin_cases i <;> simp [coordVec] <;> ring

@[simp]
theorem linearMapOfSL2Z_apply (g : SL2Z) (v : Fin 2 → ℤ) :
    linearMapOfSL2Z g v =
      coordVec
        ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * v 0 +
          (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * v 1)
        ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * v 0 +
          (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * v 1) :=
  rfl

/-- The coordinate `SL₂(ℤ)` action is mathlib quadratic-form composition by the
induced linear map on `ℤ²`. -/
theorem toQuadraticForm_transform (Q : BinaryQuadraticForm) (g : SL2Z) :
    toQuadraticForm (transform Q g) = (toQuadraticForm Q).comp (linearMapOfSL2Z g) := by
  apply QuadraticMap.ext
  intro v
  simp [transform, eval, coordVec]
  ring

/-- Proper equivalence of coordinate forms gives equality after composing the
associated mathlib quadratic form with the corresponding linear map. -/
theorem exists_toQuadraticForm_eq_comp_of_properEquivalent {Q R : BinaryQuadraticForm}
    (hQR : ProperEquivalent Q R) :
    ∃ g : SL2Z, toQuadraticForm R = (toQuadraticForm Q).comp (linearMapOfSL2Z g) := by
  rcases hQR with ⟨g, rfl⟩
  exact ⟨g, toQuadraticForm_transform Q g⟩

/-! ## Positive definiteness -/

/-- Positive definite coordinate forms are positive definite as mathlib
quadratic forms over `ℤ²`. -/
theorem toQuadraticForm_posDef (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) : (toQuadraticForm Q).PosDef := by
  intro v hv
  rw [toQuadraticForm_apply]
  apply eval_pos_of_isPositiveDefinite Q hQ
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · exfalso
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    · exact Or.inr h1
  · exact Or.inl h0

/-- If the attached mathlib quadratic form is positive definite, then the
coordinate form is positive definite. -/
theorem isPositiveDefinite_of_toQuadraticForm_posDef (Q : BinaryQuadraticForm)
    (hQ : (toQuadraticForm Q).PosDef) : Q.IsPositiveDefinite := by
  have h10_ne : (coordVec 1 0 : Fin 2 → ℤ) ≠ 0 := by
    intro h
    have := congr_fun h 0
    norm_num [coordVec] at this
  have ha : 0 < Q.a := by
    have h := hQ (coordVec 1 0) h10_ne
    simpa [toQuadraticForm_coordVec, eval, coordVec] using h
  have hvec_ne : coordVec Q.b (-2 * Q.a) ≠ 0 := by
    intro h
    have h1 := congr_fun h 1
    have : -2 * Q.a = 0 := by simpa [coordVec] using h1
    nlinarith
  have hval := hQ (coordVec Q.b (-2 * Q.a)) hvec_ne
  have hcalc : Q.eval Q.b (-2 * Q.a) = -Q.a * Q.disc := by
    simp [eval, disc]
    ring_nf
  rw [toQuadraticForm_coordVec, hcalc] at hval
  exact ⟨ha, by nlinarith⟩

/-- The project positivity predicate agrees with mathlib positive-definiteness. -/
theorem toQuadraticForm_posDef_iff (Q : BinaryQuadraticForm) :
    (toQuadraticForm Q).PosDef ↔ Q.IsPositiveDefinite :=
  ⟨isPositiveDefinite_of_toQuadraticForm_posDef Q, toQuadraticForm_posDef Q⟩

end BinaryQuadraticForm
end QuadraticNumberFields
