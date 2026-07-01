/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Zsqrtd.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Bridge between the project `Zsqrtd` and mathlib's `ℤ√d`

This module is the **only** place that connects the project-owned `Zsqrtd d`
(`QuadraticAlgebra ℤ d 0`) with mathlib's `_root_.Zsqrtd d` (`ℤ√d`). It is kept
separate from `QuadraticNumberFields.Zsqrtd.Basic` so that the project model
never transitively depends on mathlib's `Zsqrtd`, and so that the rest of the
library can use the project model without pulling in mathlib's API.

Import this file only when an interface with mathlib's `ℤ√d` is genuinely
required (see the `Zsqrtd` policy in `AGENTS.md`).

## Main Definitions

* `Zsqrtd.toMathlib`, `Zsqrtd.ofMathlib`: coordinate ring homs between the two
  models.
* `Zsqrtd.equivMathlib`: ring isomorphism with mathlib's `ℤ√d`.
-/

namespace QuadraticNumberFields

namespace Zsqrtd

/-- Coordinate map from QA `Zsqrtd` to mathlib's `ℤ√d`. -/
def toMathlib (d : ℤ) : Zsqrtd d →+* ℤ√d where
  toFun := fun z => ⟨z.re, z.im⟩
  map_one' := by ext <;> rfl
  map_mul' := by
    intro x y
    ext <;> simp
  map_zero' := by ext <;> rfl
  map_add' := by
    intro x y
    ext <;> rfl

/-- Coordinate map from mathlib's `ℤ√d` to QA `Zsqrtd`. -/
def ofMathlib (d : ℤ) : ℤ√d →+* Zsqrtd d where
  toFun := fun z => ⟨z.re, z.im⟩
  map_one' := by ext <;> rfl
  map_mul' := by
    intro x y
    ext <;> simp
  map_zero' := by ext <;> rfl
  map_add' := by
    intro x y
    ext <;> rfl

@[simp] theorem toMathlib_ofMathlib (d : ℤ) (z : ℤ√d) :
    toMathlib d (ofMathlib d z) = z := by
  rfl

@[simp] theorem ofMathlib_toMathlib (d : ℤ) (z : Zsqrtd d) :
    ofMathlib d (toMathlib d z) = z := by
  rfl

/-- Ring isomorphism between QA `Zsqrtd` and mathlib's `ℤ√d`. -/
def equivMathlib (d : ℤ) : Zsqrtd d ≃+* ℤ√d where
  toFun := toMathlib d
  invFun := ofMathlib d
  left_inv := ofMathlib_toMathlib d
  right_inv := toMathlib_ofMathlib d
  map_mul' := by
    intro x y
    ext <;> simp [mul_comm, mul_left_comm]
  map_add' := by
    intro x y
    rfl

end Zsqrtd

end QuadraticNumberFields
