/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Examples.SqrtNeg5.Forms
import Examples.SqrtNeg21.ClassGroup
import FormClassGroup.ClassGroup.ClassNumber
import QuadraticNumberFields.ClassGroup.GenusTheory.Imaginary
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Simproc.Factors

/-!
# Class Group Structure Computations

This file is the final layer of the class-group structure examples.  The
preceding example file checks the raw reduced-form multiplication tables.  This
file keeps the formal `MulEquiv` outputs.  The cyclic groups for `d = -5` and
`d = -23` follow from their prime class numbers.  The class groups for
`d = -14` and `d = -21` both have order four, and the genus-theory count of
their two-torsion tells them apart.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## Groups of order four -/

/-- A commutative group of order four whose two-torsion subgroup has order two
is cyclic. -/
private theorem isCyclic_of_card_eq_four_of_card_twoTorsion_eq_two
    {G : Type*} [CommGroup G] (hG : Nat.card G = 4)
    (h2 : Nat.card (Subgroup.twoTorsion G) = 2) : IsCyclic G := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ Subgroup.twoTorsion G := by
    by_contra! h
    have htop : Subgroup.twoTorsion G = ⊤ := eq_top_iff.mpr fun g _ => h g
    have := (Subgroup.card_eq_iff_eq_top _).mpr htop
    omega
  rw [Subgroup.mem_twoTorsion_iff, ← orderOf_dvd_iff_pow_eq_one] at hg
  refine isCyclic_of_orderOf_eq_card g ?_
  have hdvd : orderOf g ∣ 4 := hG ▸ orderOf_dvd_natCard g
  have hle : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  rw [hG]
  interval_cases orderOf g <;> simp_all

/-- A group of order four in which every element squares to one is a Klein
four-group. -/
private theorem isKleinFour_of_card_eq_four_of_forall_sq_eq_one
    {G : Type*} [Group G] (hG : Nat.card G = 4) (h : ∀ g : G, g ^ 2 = 1) :
    IsKleinFour G where
  card_four := hG
  exponent_two := by
    have : Finite G := Nat.finite_of_card_ne_zero (by omega)
    have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    exact fun g hg => orderOf_eq_prime (h g) hg

/-! ## Input facts for the concrete fields -/

section ConcreteIsomorphisms

open scoped _root_.NumberField

attribute [-instance] DivisionRing.toRatAlgebra

/-- `-23` is squarefree. -/
instance : Fact (Squarefree (-23 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

/-- `-23` is not `1`. -/
instance : Fact ((-23 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `-14` is squarefree. -/
instance : Fact (Squarefree (-14 : ℤ)) :=
  ⟨Int.squarefree_natAbs.mp (by
    change Squarefree (14 : ℕ)
    rw [show (14 : ℕ) = 2 * 7 by norm_num]
    rw [Nat.squarefree_mul (by norm_num : Nat.Coprime 2 7)]
    exact ⟨Nat.prime_two.squarefree, Nat.prime_seven.squarefree⟩)⟩

/-- `-14` is not `1`. -/
instance : Fact ((-14 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `ℚ(√-23)` has class number three, computed by reduced forms. -/
theorem classNumber_qsqrtd_neg23 :
    NumberField.classNumber (Qsqrtd ((-23 : ℤ) : ℚ)) = 3 := by
  compute_class_number_qsqrtd

/-- `ℚ(√-14)` has class number four, computed by reduced forms. -/
theorem classNumber_qsqrtd_neg14 :
    NumberField.classNumber (Qsqrtd ((-14 : ℤ) : ℚ)) = 4 := by
  compute_class_number_qsqrtd

/-- Exactly two rational primes, `2` and `7`, ramify in `ℚ(√-14)`. -/
theorem ramifiedPrimeCount_neg14 : ClassGroup.ramifiedPrimeCount (-14) = 2 := by
  rw [ClassGroup.ramifiedPrimeCount, ClassGroup.ramifiedPrimes_eq_discrFormula_primeFactors,
    RingOfIntegers.discrFormula_of_mod_four_ne_one (by decide)]
  simp [Nat.primeFactors]

/-- Exactly three rational primes, `2`, `3`, and `7`, ramify in `ℚ(√-21)`. -/
theorem ramifiedPrimeCount_neg21 : ClassGroup.ramifiedPrimeCount (-21) = 3 := by
  rw [ClassGroup.ramifiedPrimeCount, ClassGroup.ramifiedPrimes_eq_discrFormula_primeFactors,
    RingOfIntegers.discrFormula_of_mod_four_ne_one (by decide)]
  simp [Nat.primeFactors]

/-! ## Direct cyclic outputs -/

/-- `ℚ(√-5)`: the class group is cyclic of order 2, i.e. `ℤ/2ℤ`.
This follows from class number 2 (already proved in `Computed.lean`) and the
fact that any non-principal ideal generates the group. -/
noncomputable def classGroup_qsqrtd_neg5_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-5 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 2) :=
  Examples.SqrtNeg5.classGroupMulEquivZMod2

/-- `ℚ(√-23)`: the class group is cyclic of order 3, i.e. `ℤ/3ℤ`.
Class number 3 is already proved; any non-principal ideal has order 3. -/
noncomputable def classGroup_qsqrtd_neg23_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq (p := 3)
    (G := ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))))
    (G' := Multiplicative (ZMod 3))
    (by
      simpa only [NumberField.classNumber, Nat.card_eq_fintype_card]
        using classNumber_qsqrtd_neg23)
    (by simp)

/-! ## Order-four outputs from genus theory -/

/-- `ℚ(√-14)`: the class group is cyclic of order 4, i.e. `ℤ/4ℤ`.
Class number 4 is computed by reduced forms; genus theory gives a two-torsion
subgroup of order `2 ^ (2 - 1) = 2`, so the group is not of exponent two. -/
noncomputable def classGroup_qsqrtd_neg14_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-14 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 4) :=
  have hcard :
      Nat.card (ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-14 : ℤ) : ℚ)))) = 4 := by
    simpa only [NumberField.classNumber, Nat.card_eq_fintype_card]
      using classNumber_qsqrtd_neg14
  have h2 : Nat.card (ClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd ((-14 : ℤ) : ℚ)))) = 2 := by
    rw [ClassGroup.GenusTheory.card_classGroupTwoTorsion_eq_two_pow_sub_one_of_neg (-14)
      (by decide), ramifiedPrimeCount_neg14]
    norm_num
  have := isCyclic_of_card_eq_four_of_card_twoTorsion_eq_two hcard h2
  mulEquivOfCyclicCardEq (hcard.trans (by simp))

/-- `ℚ(√-21)`: the class group is the Klein four-group `(ℤ/2ℤ)²`.
Class number 4 is computed by reduced forms; genus theory gives a two-torsion
subgroup of order `2 ^ (3 - 1) = 4`, so every class squares to one. -/
noncomputable def classGroup_qsqrtd_neg21_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-21 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  have hcard :
      Nat.card (ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-21 : ℤ) : ℚ)))) = 4 := by
    simpa only [NumberField.classNumber, Nat.card_eq_fintype_card]
      using classNumber_eq_four
  have h2 : Nat.card (ClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd ((-21 : ℤ) : ℚ)))) = 4 := by
    rw [ClassGroup.GenusTheory.card_classGroupTwoTorsion_eq_two_pow_sub_one_of_neg (-21)
      (by decide), ramifiedPrimeCount_neg21]
    norm_num
  have htop : Subgroup.twoTorsion (ClassGroup
      (NumberField.RingOfIntegers (Qsqrtd ((-21 : ℤ) : ℚ)))) = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).mp (h2.trans hcard.symm)
  have := isKleinFour_of_card_eq_four_of_forall_sq_eq_one hcard fun g =>
    (Subgroup.mem_twoTorsion_iff g).mp (htop ▸ Subgroup.mem_top g)
  have : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    isKleinFour_of_card_eq_four_of_forall_sq_eq_one (by simp) (by decide)
  Classical.choice IsKleinFour.nonempty_mulEquiv

attribute [nolint defsWithUnderscore]
  classGroup_qsqrtd_neg5_mulEquiv classGroup_qsqrtd_neg23_mulEquiv
  classGroup_qsqrtd_neg14_mulEquiv classGroup_qsqrtd_neg21_mulEquiv

end ConcreteIsomorphisms

end BinaryQuadraticForm
end QuadraticNumberFields
