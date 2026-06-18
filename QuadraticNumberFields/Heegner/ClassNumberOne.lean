/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassNumber
import QuadraticNumberFields.RingOfIntegers.CommonInstances
import QuadraticNumberFields.Splitting.Qsqrtd.Classification

/-!
# Class Number One for the Nine Heegner Numbers

This file proves that the nine imaginary quadratic fields `ℚ(√d)` with
`d ∈ {-1, -2, -3, -7, -11, -19, -43, -67, -163}` (the **Heegner numbers**)
all have class number one. This is the elementary direction of the
Baker–Heegner–Stark theorem (see `QuadraticNumberFields.Heegner.StarkHeegner`
for the full statement).

## Proof strategy

For each Heegner number the Minkowski bound `(2/π)·√|D|` is estimated by
`Qsqrtd.minkowskiBound_lt_of_neg` (using only `π > 3`), and every rational
prime below the bound is checked to be **inert** via the splitting
classification: `d ≡ 5 (mod 8)` for `p = 2`, and `legendreSym p d = -1` for
odd `p`. The criterion
`Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn` then yields
triviality of the class group.

The largest case `d = -163` has Minkowski bound `≈ 8.13 < 9`, so the primes
`2, 3, 5, 7` must all be inert — the classical computation.

## Main results

* `classNumber_eq_one_neg1` … `classNumber_eq_one_neg163`: the nine cases.
* `heegnerSet`: the nine Heegner numbers as a `Finset ℤ`.
* `classNumber_eq_one_of_mem_heegnerSet`: packaged forward direction.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

open Splitting

instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `ℚ(√-1)` has class number one: the Minkowski bound is `4/π < 2`. -/
theorem classNumber_eq_one_neg1 :
    NumberField.classNumber (Qsqrtd ((-1 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-1)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-1 : ℤ) < (2 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_ne_one _ (by decide)]; norm_num)
  have hplt : p < 2 := by exact_mod_cast hple.trans_lt hb
  interval_cases p <;> exact absurd hp (by decide)

/-- `ℚ(√-2)` has class number one: the Minkowski bound is `(2/π)·√8 < 2`. -/
theorem classNumber_eq_one_neg2 :
    NumberField.classNumber (Qsqrtd ((-2 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-2)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-2 : ℤ) < (2 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_ne_one _ (by decide)]; norm_num)
  have hplt : p < 2 := by exact_mod_cast hple.trans_lt hb
  interval_cases p <;> exact absurd hp (by decide)

/-- `ℚ(√-3)` has class number one: the Minkowski bound is `(2/π)·√3 < 2`. -/
theorem classNumber_eq_one_neg3 :
    NumberField.classNumber (Qsqrtd ((-3 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-3)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-3 : ℤ) < (2 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]; norm_num)
  have hplt : p < 2 := by exact_mod_cast hple.trans_lt hb
  interval_cases p <;> exact absurd hp (by decide)

/-- `ℚ(√-7)` has class number one: the Minkowski bound is `(2/π)·√7 < 2`. -/
theorem classNumber_eq_one_neg7 :
    NumberField.classNumber (Qsqrtd ((-7 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-7)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-7 : ℤ) < (2 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]; norm_num)
  have hplt : p < 2 := by exact_mod_cast hple.trans_lt hb
  interval_cases p <;> exact absurd hp (by decide)

/-- `ℚ(√-11)` has class number one: the Minkowski bound is `(2/π)·√11 < 3`,
and `2` is inert since `-11 ≡ 5 (mod 8)`. -/
theorem classNumber_eq_one_neg11 :
    NumberField.classNumber (Qsqrtd ((-11 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-11)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-11 : ℤ) < (3 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]; norm_num)
  have hplt : p < 3 := by exact_mod_cast hple.trans_lt hb
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact isInert_two_of_mod_eight_eq_five (-11) (by decide)

/-- `ℚ(√-19)` has class number one: the Minkowski bound is `(2/π)·√19 < 3`,
and `2` is inert since `-19 ≡ 5 (mod 8)`. -/
theorem classNumber_eq_one_neg19 :
    NumberField.classNumber (Qsqrtd ((-19 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-19)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-19 : ℤ) < (3 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]; norm_num)
  have hplt : p < 3 := by exact_mod_cast hple.trans_lt hb
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact isInert_two_of_mod_eight_eq_five (-19) (by decide)

/-- `ℚ(√-43)` has class number one: the Minkowski bound is `(2/π)·√43 < 5`,
and `2, 3` are inert. -/
theorem classNumber_eq_one_neg43 :
    NumberField.classNumber (Qsqrtd ((-43 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-43)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-43 : ℤ) < (5 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]; norm_num)
  have hplt : p < 5 := by exact_mod_cast hple.trans_lt hb
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact isInert_two_of_mod_eight_eq_five (-43) (by decide)
  · exact (isInert_iff_legendreSym_eq_neg_one (-43) 3 (by decide) (by decide)).mpr (by decide)
  · exact absurd hp (by decide)

/-- `ℚ(√-67)` has class number one: the Minkowski bound is `(2/π)·√67 < 6`,
and `2, 3, 5` are inert. -/
theorem classNumber_eq_one_neg67 :
    NumberField.classNumber (Qsqrtd ((-67 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-67)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-67 : ℤ) < (6 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]; norm_num)
  have hplt : p < 6 := by exact_mod_cast hple.trans_lt hb
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact isInert_two_of_mod_eight_eq_five (-67) (by decide)
  · exact (isInert_iff_legendreSym_eq_neg_one (-67) 3 (by decide) (by decide)).mpr (by decide)
  · exact absurd hp (by decide)
  · exact (isInert_iff_legendreSym_eq_neg_one (-67) 5 (by decide) (by decide)).mpr (by decide)

/-- `ℚ(√-163)` has class number one: the Minkowski bound is `(2/π)·√163 < 9`,
and `2, 3, 5, 7` are all inert — the classical Heegner computation. -/
theorem classNumber_eq_one_neg163 :
    NumberField.classNumber (Qsqrtd ((-163 : ℤ) : ℚ)) = 1 := by
  refine Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn (-163)
    fun p hp hple => ?_
  have hb : Qsqrtd.minkowskiBound (-163 : ℤ) < (9 : ℕ) :=
    Qsqrtd.minkowskiBound_lt_of_neg _ (by norm_num)
      (by rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]; norm_num)
  have hplt : p < 9 := by exact_mod_cast hple.trans_lt hb
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact isInert_two_of_mod_eight_eq_five (-163) (by decide)
  · exact (isInert_iff_legendreSym_eq_neg_one (-163) 3 (by decide) (by decide)).mpr (by decide)
  · exact absurd hp (by decide)
  · exact (isInert_iff_legendreSym_eq_neg_one (-163) 5 (by decide) (by decide)).mpr (by decide)
  · exact absurd hp (by decide)
  · exact (isInert_iff_legendreSym_eq_neg_one (-163) 7 (by decide) (by decide)).mpr (by decide)
  · exact absurd hp (by decide)

/-! ## The Heegner numbers, packaged -/

/-- The nine **Heegner numbers**: the negative squarefree integers `d` for
which `ℚ(√d)` has class number one. -/
def heegnerSet : Finset ℤ := {-1, -2, -3, -7, -11, -19, -43, -67, -163}

/-- **Forward direction of the Baker–Heegner–Stark theorem**: every Heegner
number gives an imaginary quadratic field of class number one. -/
theorem classNumber_eq_one_of_mem_heegnerSet
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d ∈ heegnerSet) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  fin_cases hd
  · exact classNumber_eq_one_neg1
  · exact classNumber_eq_one_neg2
  · exact classNumber_eq_one_neg3
  · exact classNumber_eq_one_neg7
  · exact classNumber_eq_one_neg11
  · exact classNumber_eq_one_neg19
  · exact classNumber_eq_one_neg43
  · exact classNumber_eq_one_neg67
  · exact classNumber_eq_one_neg163

-- theorem classNumber_eq_one_of_mem_heegnerSet'
--     {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d ∈ heegnerSet) :
--     NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
--   fin_cases hd <;> compute_class_number_qsqrtd

end Heegner
end QuadraticNumberFields
