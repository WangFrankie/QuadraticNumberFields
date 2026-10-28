/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import ImaginaryClassNumberOne.ClassNumberOne
import ImaginaryClassNumberOne.InertPrimes
import ImaginaryClassNumberOne.IdealReductions
import QuadraticNumberFields.ClassGroup.GenusTheory.Sieve

/-!
# The Baker–Heegner–Stark Theorem (Statement)

This file states the full **Baker–Heegner–Stark theorem** (also known as the
Stark–Heegner theorem): an imaginary quadratic field `ℚ(√d)` (with `d < 0`
squarefree) has class number one if and only if `d` is one of the nine
Heegner numbers `-1, -2, -3, -7, -11, -19, -43, -67, -163`.

The easy direction — each Heegner number gives class number one — is proved in
`QuadraticNumberFields.Heegner.ClassNumberOne` via Minkowski bounds and
inertness of small primes. The forward direction is assembled from the
genus-theory parameter-shape sieve, the split-at-`2` reduction, and the
Cox-Weber inert prime case in `ImaginaryClassNumberOne.InertPrimes`. The
remaining mathematical assumption is `InertPrimeWeberHypothesis`.
The Diophantine theorem `heegner_xy_solutions`
for `Y ^ 2 = 2 * X * (X ^ 3 + 1)` is proved in
`QuadraticNumberFields.Heegner.Diophantine`.

## Reference

D. A. Cox, *Primes of the form x² + ny²*, 2nd ed., Theorem 12.34 (Heegner's
proof). H. M. Stark, *A complete determination of the complex quadratic fields
of class-number one*, Michigan Math. J. 14 (1967).
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-
TODO roadmap for the remaining forward direction:

* Prove `InertPrimeWeberHypothesis` from Weber functions and complex multiplication.
* The conductor-`2` reduced-form relation `h(-4p) = 3` is proved in
  `ImaginaryClassNumberOne.Weber.ConductorTwo`; its identification with the
  quadratic-order class number still needs to be established.
* A quadratic-order/Picard-group proof of Cox 7.24 or Corollary 7.28 is an
  alternative approach to the conductor class-number relation.
* Stark's argument or Baker's logarithmic estimates give other approaches to
  the remaining inert prime case.
-/

/-- **Elementary non-half-integral branch of Baker-Heegner-Stark.** If
`d % 4 ≠ 1`, then the ideal-theoretic ramification-at-`2` argument already
forces `d = -1` or `d = -2`, hence `d` is a Heegner number. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd4 : d % 4 ≠ 1)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  rcases eq_neg_one_or_eq_neg_two_of_classNumber_eq_one_of_mod_four_ne_one
      d hd hd4 h with rfl | rfl <;>
    simp [heegnerSet]

/-- **Elementary split half-integral branch of Baker-Heegner-Stark.** If
`d % 8 = 1`, then the ideal-theoretic split-at-`2` argument already forces
`d = -7`, hence `d` is a Heegner number. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd8 : d % 8 = 1)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  have hd_eq : d = -7 :=
    eq_neg_seven_of_classNumber_eq_one_of_mod_eight_eq_one d hd hd8 h
  rw [hd_eq]
  simp [heegnerSet]

/-- **Baker-Heegner-Stark prime-family step.** After the genus-theory
parameter-shape sieve has reduced the class-number-one problem to `d = -1`,
`d = -2`, or `d = -p` with `p ≡ 3 (mod 4)` prime, the remaining case is
the inert prime case `p ≡ 3 (mod 8)`. The complementary case `p ≡ 7 (mod 8)` is
the elementary split-at-`2` branch, which has already been handled
ideal-theoretically. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_parameter_prime_shape
    (hweber : InertPrimeWeberHypothesis)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hshape :
      d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  rcases hshape with rfl | rfl | ⟨p, hp, hp4, hdp⟩
  · simp [heegnerSet]
  · simp [heegnerSet]
  · have hp8_cases : p % 8 = 3 ∨ p % 8 = 7 := by omega
    rcases hp8_cases with hp8 | hp8
    · exact mem_heegnerSet_of_classNumber_eq_one_of_inert_prime hweber d hd p hp hp8 hdp h
    · have hd8 : d % 8 = 1 := by
        subst hdp
        omega
      exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one d hd hd8 h

/-- Deprecated name for
`classNumber_eq_one_imp_mem_heegnerSet_of_parameter_prime_shape`. -/
@[deprecated classNumber_eq_one_imp_mem_heegnerSet_of_parameter_prime_shape
  (since := "2026-07-12")]
theorem classNumber_eq_one_imp_mem_heegnerSet_of_discr_prime_shape
    (hweber : InertPrimeWeberHypothesis)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hshape :
      d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet :=
  classNumber_eq_one_imp_mem_heegnerSet_of_parameter_prime_shape
    hweber d hd hshape h

/-- **Inert half-integral branch of Baker-Heegner-Stark.** In the `d % 8 = 5`
branch, the ideal-theoretic odd prime-shape sieve reduces class number one to
`d = -p` with `p ≡ 3 (mod 8)`, to which we apply
`mem_heegnerSet_of_classNumber_eq_one_of_inert_prime`. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_five
    (hweber : InertPrimeWeberHypothesis)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd8 : d % 8 = 5)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  have hd4 : d % 4 = 1 := by omega
  rcases classNumber_eq_one_imp_exists_prime_of_mod_four_eq_one d hd hd4 h with
    ⟨p, hp, _hp4, hdp⟩
  have hp8 : p % 8 = 3 := by
    subst hdp
    omega
  exact mem_heegnerSet_of_classNumber_eq_one_of_inert_prime hweber d hd p hp hp8 hdp h

/-- **Baker-Heegner-Stark forward direction.** The genus-theory sieve supplies
the parameter shape; the split-at-`2` reduction closes the `p ≡ 7 (mod 8)`
branch, and the remaining `p ≡ 3 (mod 8)` branch uses the inert prime core. -/
theorem classNumber_eq_one_imp_mem_heegnerSet
    (hweber : InertPrimeWeberHypothesis)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet :=
  classNumber_eq_one_imp_mem_heegnerSet_of_parameter_prime_shape
    hweber d hd
    (ClassGroup.GenusTheory.classNumber_eq_one_imp_parameter_prime_shape d hd h) h

/-- **Baker–Heegner–Stark theorem.** A negative squarefree integer `d` gives an
imaginary quadratic field `ℚ(√d)` of class number one if and only if `d` is one
of the nine Heegner numbers `-1, -2, -3, -7, -11, -19, -43, -67, -163`.

The reverse implication is `classNumber_eq_one_of_mem_heegnerSet`. The forward
implication uses the genus-theory parameter-shape sieve and the explicit
Weber hypothesis `hweber`. This is a conditional theorem. -/
theorem classNumber_eq_one_iff_mem_heegnerSet
    (hweber : InertPrimeWeberHypothesis)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet := by
  constructor
  · exact classNumber_eq_one_imp_mem_heegnerSet hweber d hd
  · exact fun h => classNumber_eq_one_of_mem_heegnerSet h

end Heegner
end QuadraticNumberFields
