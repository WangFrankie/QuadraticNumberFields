/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.ClassGroup

/-!
# Torsion in Class Groups

This file organizes ideal-theoretic torsion criteria for mathlib's ideal class
group.
-/

namespace ClassGroup

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- If a power of a nonzero integral ideal is principal, then the same power of its
ideal class is trivial. -/
theorem mk0_pow_eq_one_of_pow_isPrincipal
    (I : nonZeroDivisors (Ideal R)) {n : ℕ} (hI : ((I : Ideal R) ^ n).IsPrincipal) :
    (mk0 I : ClassGroup R) ^ n = 1 := by
  rw [← map_pow]
  rw [mk0_eq_one_iff]
  exact hI

/-- If a positive power of a nonzero integral ideal is principal, its ideal class is
torsion. -/
theorem mk0_mem_torsion_of_pow_isPrincipal
    (I : nonZeroDivisors (Ideal R)) {n : ℕ} (hn : 0 < n)
    (hI : ((I : Ideal R) ^ n).IsPrincipal) :
    mk0 I ∈ CommGroup.torsion (ClassGroup R) := by
  rw [CommGroup.mem_torsion]
  rw [isOfFinOrder_iff_pow_eq_one]
  exact ⟨n, hn, mk0_pow_eq_one_of_pow_isPrincipal I hI⟩

/-- If the square of a nonzero integral ideal is principal, then the square of its
ideal class is trivial. -/
theorem mk0_sq_eq_one_of_sq_isPrincipal
    (I : nonZeroDivisors (Ideal R)) (hI : ((I : Ideal R) ^ 2).IsPrincipal) :
    (mk0 I : ClassGroup R) ^ 2 = 1 :=
  mk0_pow_eq_one_of_pow_isPrincipal I hI

end ClassGroup
