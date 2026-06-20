/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Core.Basic
import BinaryQuadraticForms.Core.Enumeration
import BinaryQuadraticForms.Core.Reduction
import BinaryQuadraticForms.Gauss.Composition

/-!
# Binary Quadratic Form Smoke Examples

Small examples for the project-owned binary-quadratic-form API.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

example : (BinaryQuadraticForm.mk 1 0 1).disc = -4 := by
  norm_num [disc]

example : (BinaryQuadraticForm.mk 1 1 1).eval 2 3 = 19 := by
  norm_num [eval]

example : (BinaryQuadraticForm.mk 1 0 1).IsPositiveDefinite := by
  constructor <;> norm_num [IsPositiveDefinite, disc]

example : (BinaryQuadraticForm.mk 1 0 1).IsReduced := by
  norm_num [IsReduced]

example : (BinaryQuadraticForm.mk 1 1 1).IsReduced := by
  norm_num [IsReduced]

example : ¬ (BinaryQuadraticForm.mk 1 (-1) 1).IsReduced := by
  norm_num [IsReduced]

example : bCandidates 1 = [-1, 0, 1] := by
  decide

example :
    (BinaryQuadraticForm.mk 1 0 1).IsUnited (BinaryQuadraticForm.mk 1 0 1) := by
  norm_num [IsUnited, sigma, coeffGCD3]

example :
    composeConcordant (BinaryQuadraticForm.mk 1 0 1) (BinaryQuadraticForm.mk 1 0 1) =
      BinaryQuadraticForm.mk 1 0 1 := by
  norm_num [composeConcordant, disc]

example :
    (composeConcordant (BinaryQuadraticForm.mk 1 0 1)
      (BinaryQuadraticForm.mk 1 0 1)).disc = -4 := by
  exact disc_composeConcordant_of_eq_mul
    (BinaryQuadraticForm.mk 1 0 1) (BinaryQuadraticForm.mk 1 0 1) (c := 1)
    (by norm_num) (by norm_num [disc])

example :
    (composeConcordant (BinaryQuadraticForm.mk 1 0 1)
      (BinaryQuadraticForm.mk 1 0 1)).disc = -4 := by
  exact disc_composeConcordant_of_isConcordant
    (Q := BinaryQuadraticForm.mk 1 0 1) (R := BinaryQuadraticForm.mk 1 0 1)
    (by norm_num [IsConcordant, disc]) (by norm_num) (by norm_num)

example :
    (composeConcordant (BinaryQuadraticForm.mk 1 0 1)
      (BinaryQuadraticForm.mk 1 0 1)).IsPositiveDefinite := by
  exact isPositiveDefinite_composeConcordant_of_isConcordant
    (Q := BinaryQuadraticForm.mk 1 0 1) (R := BinaryQuadraticForm.mk 1 0 1)
    (by norm_num [IsConcordant, disc])
    (by norm_num [IsPositiveDefinite, disc])
    (by norm_num [IsPositiveDefinite, disc])

end BinaryQuadraticForm
end QuadraticNumberFields
