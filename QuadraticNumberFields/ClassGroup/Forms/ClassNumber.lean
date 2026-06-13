/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassNumber
import QuadraticNumberFields.Heegner.ClassNumberOne

/-!
# The Class Number of `ℚ(√d)` as a Function of `d`

This file defines `classNumberQsqrtd d`, the class number of the standard
quadratic field `Qsqrtd d` as a function of the integer parameter `d`, and
bridges the nine Heegner class-number-one theorems to this interface.

For now `classNumberQsqrtd` is a noncomputable thin alias of
`NumberField.classNumber`; after the planned binary-quadratic-form
enumeration it will acquire a computable equation on imaginary `d` with the
same signature.

## Main definitions

* `classNumberQsqrtd`: the class number of `ℚ(√d)` as a function of `d : ℤ`.

## Main statements

* `classNumberQsqrtd_neg1` … `classNumberQsqrtd_neg163`: the nine Heegner
  fields have class number one.
* `classNumberQsqrtd_eq_one_of_mem_heegnerSet`: packaged form over
  `Heegner.heegnerSet`.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields

/-- The class number of the quadratic field `ℚ(√d)`, as a function of the
squarefree integer parameter `d`. Thin alias of `NumberField.classNumber`. -/
noncomputable def classNumberQsqrtd (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ℕ :=
  NumberField.classNumber (Qsqrtd (d : ℚ))

/-! ## The nine Heegner fields have class number one -/

/-- `classNumberQsqrtd (-1) = 1`, bridged from `Heegner.classNumber_eq_one_neg1`. -/
theorem classNumberQsqrtd_neg1 : classNumberQsqrtd (-1) = 1 :=
  Heegner.classNumber_eq_one_neg1

/-- `classNumberQsqrtd (-2) = 1`, bridged from `Heegner.classNumber_eq_one_neg2`. -/
theorem classNumberQsqrtd_neg2 : classNumberQsqrtd (-2) = 1 :=
  Heegner.classNumber_eq_one_neg2

/-- `classNumberQsqrtd (-3) = 1`, bridged from `Heegner.classNumber_eq_one_neg3`. -/
theorem classNumberQsqrtd_neg3 : classNumberQsqrtd (-3) = 1 :=
  Heegner.classNumber_eq_one_neg3

/-- `classNumberQsqrtd (-7) = 1`, bridged from `Heegner.classNumber_eq_one_neg7`. -/
theorem classNumberQsqrtd_neg7 : classNumberQsqrtd (-7) = 1 :=
  Heegner.classNumber_eq_one_neg7

/-- `classNumberQsqrtd (-11) = 1`, bridged from `Heegner.classNumber_eq_one_neg11`. -/
theorem classNumberQsqrtd_neg11 : classNumberQsqrtd (-11) = 1 :=
  Heegner.classNumber_eq_one_neg11

/-- `classNumberQsqrtd (-19) = 1`, bridged from `Heegner.classNumber_eq_one_neg19`. -/
theorem classNumberQsqrtd_neg19 : classNumberQsqrtd (-19) = 1 :=
  Heegner.classNumber_eq_one_neg19

/-- `classNumberQsqrtd (-43) = 1`, bridged from `Heegner.classNumber_eq_one_neg43`. -/
theorem classNumberQsqrtd_neg43 : classNumberQsqrtd (-43) = 1 :=
  Heegner.classNumber_eq_one_neg43

/-- `classNumberQsqrtd (-67) = 1`, bridged from `Heegner.classNumber_eq_one_neg67`. -/
theorem classNumberQsqrtd_neg67 : classNumberQsqrtd (-67) = 1 :=
  Heegner.classNumber_eq_one_neg67

/-- `classNumberQsqrtd (-163) = 1`, bridged from `Heegner.classNumber_eq_one_neg163`. -/
theorem classNumberQsqrtd_neg163 : classNumberQsqrtd (-163) = 1 :=
  Heegner.classNumber_eq_one_neg163

/-- Packaged form: every Heegner number has `classNumberQsqrtd d = 1`. -/
theorem classNumberQsqrtd_eq_one_of_mem_heegnerSet
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d ∈ Heegner.heegnerSet) :
    classNumberQsqrtd d = 1 :=
  Heegner.classNumber_eq_one_of_mem_heegnerSet hd

end QuadraticNumberFields
