import QuadraticNumberFields.Forms.ClassNumber
import QuadraticNumberFields.Mathlib.Data.Int.Squarefree

attribute [-instance] DivisionRing.toRatAlgebra

instance : Fact (Squarefree (-21 : ℤ)) :=
    ⟨Int.squarefree_natAbs.mp (by
      change Squarefree (21 : ℕ)
      rw [show (21 : ℕ) = 3 * 7 by norm_num]
      rw [Nat.squarefree_mul (by norm_num : Nat.Coprime 3 7)]
      exact ⟨Nat.prime_three.squarefree, Nat.prime_seven.squarefree⟩)⟩

instance :Fact ((-21 : ℤ) ≠ 1) := by decide


theorem classNumber_eq_four : NumberField.classNumber (Qsqrtd (-21 : ℤ)) = 4 := by
          compute_class_number_qsqrtd

instance : Fact (Prime (47 : ℤ)) := by decide

example : NumberField.classNumber (Qsqrtd (-47 : ℤ)) = 5 := by
          compute_class_number_qsqrtd


set_option maxRecDepth 10000
instance : Fact (Prime (2347 : ℤ)) := by decide


example : NumberField.classNumber (Qsqrtd (-2347 : ℤ)) = 5 := by
          compute_class_number_qsqrtd
