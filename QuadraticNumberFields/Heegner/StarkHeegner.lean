/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassGroup.GenusTheory
import QuadraticNumberFields.Heegner.ClassNumberOne
import QuadraticNumberFields.Heegner.Framework
import QuadraticNumberFields.Heegner.IdealReductions

/-!
# The Baker–Heegner–Stark Theorem (Statement)

This file states the full **Baker–Heegner–Stark theorem** (also known as the
Stark–Heegner theorem): an imaginary quadratic field `ℚ(√d)` (with `d < 0`
squarefree) has class number one if and only if `d` is one of the nine
Heegner numbers `-1, -2, -3, -7, -11, -19, -43, -67, -163`.

The easy direction — each Heegner number gives class number one — is proved in
`QuadraticNumberFields.Heegner.ClassNumberOne` via Minkowski bounds and
inertness of small primes. The forward direction is assembled from named
interfaces: elementary ideal-theoretic reductions, a genus-theory formula, and
the Cox-Weber inert-prime core in `QuadraticNumberFields.Heegner.Framework`.

## Reference

D. A. Cox, *Primes of the form x² + ny²*, 2nd ed., Theorem 12.34 (Heegner's
proof). H. M. Stark, *A complete determination of the complex quadratic fields
of class-number one*, Michigan Math. J. 14 (1967).
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

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

/-- **Baker-Heegner-Stark prime-family step.** After the genus-theory sieve has
reduced the class-number-one problem to `d = -1`, `d = -2`, or `d = -p` with
`p ≡ 3 (mod 4)` prime, the only deep input needed is the inert prime core
`p ≡ 3 (mod 8)`.  The complementary case `p ≡ 7 (mod 8)` is the elementary
split-at-`2` branch, which has already been handled ideal-theoretically. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_discriminant_prime_shape
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
    · exact baker_heegner_stark_inert_prime_core d hd p hp hp8 hdp h
    · have hd8 : d % 8 = 1 := by
        subst hdp
        omega
      exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one d hd hd8 h

/-- **Genus-sieved inert half-integral branch of Baker-Heegner-Stark.** In the
`d % 8 = 5` branch, the genus-theory sieve reduces class number one to
`d = -p` with `p ≡ 3 (mod 8)`, so the only remaining input is
`baker_heegner_stark_inert_prime_core`. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_five
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd8 : d % 8 = 5)
    (hgenus : ClassGroup.genusFormula d)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  rcases ClassGroup.classNumber_eq_one_imp_discriminant_prime_shape d hd hgenus h with
    hneg1 | hneg2 | ⟨p, hp, _hp4, hdp⟩
  · subst hneg1
    norm_num at hd8
  · subst hneg2
    norm_num at hd8
  · have hp8 : p % 8 = 3 := by
      subst hdp
      omega
    exact baker_heegner_stark_inert_prime_core d hd p hp hp8 hdp h

/-- **Baker-Heegner-Stark forward direction with genus theory as an explicit
input.** The elementary ideal-theoretic branches are closed directly, and the
inert half-integral branch is routed through the genus sieve and the inert
prime core. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_genusFormula
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hgenus : ClassGroup.genusFormula d)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  by_cases hd4 : d % 4 = 1
  · have hd8_cases : d % 8 = 1 ∨ d % 8 = 5 := by omega
    rcases hd8_cases with hd8 | hd8
    · exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one d hd hd8 h
    · exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_five d hd hd8 hgenus h
  · exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_four_ne_one d hd hd4 h

/-- **Baker–Heegner–Stark theorem with genus theory as an explicit input.** This
version isolates the remaining analytic/deep input to
`baker_heegner_stark_inert_prime_core`; the algebraic genus-theory formula is
assumed through `hgenus`. -/
theorem classNumber_eq_one_iff_mem_heegnerSet_of_genusFormula
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hgenus : ClassGroup.genusFormula d) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet := by
  constructor
  · exact classNumber_eq_one_imp_mem_heegnerSet_of_genusFormula d hd hgenus
  · exact fun h => classNumber_eq_one_of_mem_heegnerSet h

/-- **Odd-discriminant genus formula from the existing genus-character
interface.** In the odd field-discriminant branch, the genus formula follows
from the current `ClassGroup.GenusTheory` data interface: construction of the
odd genus characters, their single product relation, and bijectivity onto the
relation subgroup. -/
theorem genusFormula_of_oddGenusCharacterData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : ClassGroup.OddGenusCharacterData d)
    (hrel : ClassGroup.oddGenusProductRelation d hd hdata)
    (hbij :
      Function.Bijective
        (ClassGroup.oddGenusCharacterProductToRelationSubgroup d hd hdata hrel)) :
    ClassGroup.genusFormula d :=
  ClassGroup.genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective_of_discr_odd
    d hd hodd hdata hrel hbij

/-- **Genus-theory input for Baker-Heegner-Stark.** The full genus formula for
negative squarefree quadratic fields is kept as the named algebraic-number-theory
input not supplied by the final assembly theorem. The odd-discriminant branch can
instead use `genusFormula_of_oddGenusCharacterData` once the genus-character data
and bijectivity are available. -/
theorem genusFormula_of_negative_squarefree
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    ClassGroup.genusFormula d := by
  sorry

/-- **Baker–Heegner–Stark theorem.** A negative squarefree integer `d` gives an
imaginary quadratic field `ℚ(√d)` of class number one if and only if `d` is one
of the nine Heegner numbers `-1, -2, -3, -7, -11, -19, -43, -67, -163`.

The reverse implication is `classNumber_eq_one_of_mem_heegnerSet`. The forward
implication now factors through the explicit-genus wrapper
`classNumber_eq_one_iff_mem_heegnerSet_of_genusFormula`; the remaining WIP
inputs are the genus formula and the inert-prime Baker-Heegner-Stark core. -/
theorem classNumber_eq_one_iff_mem_heegnerSet
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet := by
  exact classNumber_eq_one_iff_mem_heegnerSet_of_genusFormula d hd
    (genusFormula_of_negative_squarefree d hd)

end Heegner
end QuadraticNumberFields
