/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.ClassGroup.ClassNumber
import QuadraticNumberFields.Heegner.ClassNumberOne

/-!
# Heegner Class Number One via Reduced Forms

This file records the reduced-form computation proof of the Heegner
class-number-one direction, parallel to the Minkowski/splitting proof in
`QuadraticNumberFields.Heegner.ClassNumberOne`.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- Every Heegner number has class number one, proved by finite case analysis
and the reduced-form enumeration backend. -/
theorem classNumber_eq_one_of_mem_heegnerSet_by_reducedForms
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d ∈ heegnerSet) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  fin_cases hd <;> compute_class_number_qsqrtd

end Heegner
end QuadraticNumberFields
