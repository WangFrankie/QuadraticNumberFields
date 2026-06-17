import QuadraticNumberFields.Forms.ClassGroup.ClassNumber
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


-- set_option maxRecDepth 10000
-- instance : Fact (Prime (2347 : ℤ)) := by decide


-- example : NumberField.classNumber (Qsqrtd (-2347 : ℤ)) = 5 := by
--           compute_class_number_qsqrtd


-- theorem prime_61 : Prime 61 := by decide
-- theorem prime_131 : Prime 131 := by decide

-- instance :Fact ((-7991 : ℤ) ≠ 1) := by decide
-- instance : Fact (Squarefree (-7991 : ℤ)) :=
--     ⟨Int.squarefree_natAbs.mp (by
--       change Squarefree (7991 : ℕ)
--       rw [show (7991 : ℕ) = 61 * 131 by norm_num]
--       rw [Nat.squarefree_mul (by norm_num : Nat.Coprime 61 131)]
--       exact ⟨prime_61.squarefree, prime_131.squarefree⟩)⟩

-- example : NumberField.classNumber (Qsqrtd (-7991 : ℤ)) = 100 := by
--           compute_class_number_qsqrtd
-- #eval 61*131

-- theorem prime_151 : Prime 151 := by decide
-- theorem prime_2731 : Prime 2729 := by decide

-- instance :Fact ((-412079 : ℤ) ≠ 1) := by decide
-- instance : Fact (Squarefree (-412079 : ℤ)) :=
--     ⟨Int.squarefree_natAbs.mp (by
--       change Squarefree (412079 : ℕ)
--       rw [show (412079 : ℕ) = 151 * 2729 by norm_num]
--       rw [Nat.squarefree_mul (by norm_num : Nat.Coprime 151 2729)]
--       exact ⟨prime_151.squarefree, prime_2731.squarefree⟩)⟩

-- set_option maxHeartbeats 5000000 in
-- example : NumberField.classNumber (Qsqrtd (-412079 : ℤ)) = 1000 := by
--           compute_class_number_qsqrtd
-- #eval 151*2729
