/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassGroup.GenusTheory.Formula
import QuadraticNumberFields.ClassGroup.GenusTheory.Sieve
import ImaginaryClassNumberOne.ClassNumberOne
import ImaginaryClassNumberOne.Framework
import ImaginaryClassNumberOne.IdealReductions

/-!
# The Baker–Heegner–Stark Theorem (Statement)

This file states the full **Baker–Heegner–Stark theorem** (also known as the
Stark–Heegner theorem): an imaginary quadratic field `ℚ(√d)` (with `d < 0`
squarefree) has class number one if and only if `d` is one of the nine
Heegner numbers `-1, -2, -3, -7, -11, -19, -43, -67, -163`.

The easy direction — each Heegner number gives class number one — is proved in
`QuadraticNumberFields.Heegner.ClassNumberOne` via Minkowski bounds and
inertness of small primes. The forward direction is assembled from elementary
ideal-theoretic reductions and the Cox-Weber inert-prime core in
`QuadraticNumberFields.Heegner.Framework`. The inert-prime core still depends on
two named inputs: the Weber/CM certificate input and the Diophantine endgame
`heegner_xy_solutions` for `Y ^ 2 = 2 * X * (X ^ 3 + 1)`.

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

* Genus route: keep the full `Cl / Cl²` formula in `ClassGroup.GenusTheory`.
  The Baker-Heegner-Stark assembly no longer depends on that formula for the
  odd fundamental-discriminant prime-shape sieve.
* Weber/CM route: keep the inert-prime core routed through
  `Heegner.WeberCM.Core`; this file should not import reduced forms directly.
* Diophantine route: close `Heegner.Diophantine.heegner_xy_solutions`, the
  remaining integer-equation endgame used after the Weber/CM route supplies
  `StarkHeegnerAlgebraicCertificate`.
* Conductor-`2` assembly route: use
  `Heegner.WeberCM.ConductorTwo.Assembly` only as an optional conditional proof
  of the conductor-`2` class-number input `h(-4 * p) = 3`.  The current route
  needs the explicit fiber-residue injection theorem; injectivity gives the
  upper bound, and the lower bound comes from the reduced-form construction.
* Order/Picard route: a later quadratic-order/Picard-group proof of the
  fiber-residue injection, or of Cox 7.24 / Corollary 7.28, can replace the
  conditional conductor-`2` assembly route without changing this file.
* Alternative deep route: Stark's no-Weber variant or Baker's logarithmic route
  should be added as separate proofs of the same named inert-core input.
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

/-- **Baker-Heegner-Stark prime-family step.** After a prime-shape sieve has
reduced the class-number-one problem to `d = -1`, `d = -2`, or `d = -p` with
`p ≡ 3 (mod 4)` prime, the only deep input needed is the inert prime core
`p ≡ 3 (mod 8)`.  The complementary case `p ≡ 7 (mod 8)` is the elementary
split-at-`2` branch, which has already been handled ideal-theoretically. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_discriminant_prime_shape
    (hweber : HasInertPrimeWeberCM)
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
    · exact baker_heegner_stark_inert_prime_core hweber d hd p hp hp8 hdp h
    · have hd8 : d % 8 = 1 := by
        subst hdp
        omega
      exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one d hd hd8 h

/-- **Odd genus-formula-data branch of Baker-Heegner-Stark.** For odd fundamental
discriminants, complete odd genus-formula data feeds the prime-shape sieve and leaves
only the existing inert-prime Weber/CM input. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_oddGenusFormulaData_of_mod_four_eq_one
    (hweber : HasInertPrimeWeberCM)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : ClassGroup.OddGenusFormulaData d hd)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  have hprime :=
    ClassGroup.classNumber_eq_one_imp_exists_prime_of_oddGenusFormulaData_of_mod_four_eq_one
      d hd hd4 hdata h
  exact classNumber_eq_one_imp_mem_heegnerSet_of_discriminant_prime_shape hweber d hd
    (Or.inr (Or.inr hprime)) h

/-- **Odd genus-character branch of Baker-Heegner-Stark.** For odd fundamental
discriminants, the existing odd genus-character interface with bijective product
character feeds the prime-shape sieve and leaves only the inert-prime Weber/CM input. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_oddGenusCharacterData_of_mod_four_eq_one
    (hweber : HasInertPrimeWeberCM)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : ClassGroup.OddGenusCharacterData d)
    (hrel : ClassGroup.oddGenusProductRelation d hd hdata)
    (hbij :
      Function.Bijective
        (ClassGroup.oddGenusCharacterProductToRelationSubgroup d hd hdata hrel))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  have hprime :=
    ClassGroup.classNumber_eq_one_imp_exists_prime_of_oddGenusCharacterData_of_mod_four_eq_one
      d hd hd4 hdata hrel hbij h
  exact classNumber_eq_one_imp_mem_heegnerSet_of_discriminant_prime_shape hweber d hd
    (Or.inr (Or.inr hprime)) h

/-- **Inert half-integral branch of Baker-Heegner-Stark.** In the `d % 8 = 5`
branch, the ideal-theoretic odd prime-shape sieve reduces class number one to
`d = -p` with `p ≡ 3 (mod 8)`, so the only remaining input is
`baker_heegner_stark_inert_prime_core`. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_five
    (hweber : HasInertPrimeWeberCM)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd8 : d % 8 = 5)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  have hd4 : d % 4 = 1 := by omega
  rcases classNumber_eq_one_imp_exists_prime_of_mod_four_eq_one d hd hd4 h with
    ⟨p, hp, _hp4, hdp⟩
  have hp8 : p % 8 = 3 := by
    subst hdp
    omega
  exact baker_heegner_stark_inert_prime_core hweber d hd p hp hp8 hdp h

/-- **Baker-Heegner-Stark forward direction.** The elementary ideal-theoretic
branches are closed directly, and the inert half-integral branch is routed
through the odd prime-shape sieve and the inert prime core. -/
theorem classNumber_eq_one_imp_mem_heegnerSet
    (hweber : HasInertPrimeWeberCM)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  by_cases hd4 : d % 4 = 1
  · have hd8_cases : d % 8 = 1 ∨ d % 8 = 5 := by omega
    rcases hd8_cases with hd8 | hd8
    · exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one d hd hd8 h
    · exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_five
        hweber d hd hd8 h
  · exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_four_ne_one d hd hd4 h

/-- **Baker–Heegner–Stark theorem.** A negative squarefree integer `d` gives an
imaginary quadratic field `ℚ(√d)` of class number one if and only if `d` is one
of the nine Heegner numbers `-1, -2, -3, -7, -11, -19, -43, -67, -163`.

The reverse implication is `classNumber_eq_one_of_mem_heegnerSet`. The forward
implication now factors through the ideal-theoretic prime-shape sieve; the
remaining WIP inputs are the inert-prime Weber/CM certificate input and the Diophantine
endgame `heegner_xy_solutions`. -/
theorem classNumber_eq_one_iff_mem_heegnerSet
    (hweber : HasInertPrimeWeberCM)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet := by
  constructor
  · exact classNumber_eq_one_imp_mem_heegnerSet hweber d hd
  · exact fun h => classNumber_eq_one_of_mem_heegnerSet h

end Heegner
end QuadraticNumberFields
