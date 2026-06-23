/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.GenusTheory.OddProduct

/-!
# Genus Formula Interface

This file contains the conditional interfaces that turn the odd genus-character
product and principal-kernel statements into the standard genus formula.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

open RingOfIntegers
open Splitting

local notation "𝓞" => _root_.NumberField.RingOfIntegers

/-- Surjectivity of the relation-subgroup-valued odd genus-character product gives
the genus-theory divisibility needed by the class-number-one sieve. -/
theorem genus_divisibility_of_oddGenusCharacterProduct_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hrel : oddGenusProductRelation d hd_neg)
    (hsurj : Function.Surjective
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel))
    (hcard : Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  let φ : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* oddGenusSignRelationSubgroup d :=
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel).comp
      (QuotientGroup.mk' (squareClassSubgroup d))
  refine genus_divisibility_of_surjective_quotient d (oddGenusSignRelationSubgroup d)
    hcard φ ?_
  exact hsurj.comp (QuotientGroup.mk'_surjective (squareClassSubgroup d))

/-- In the odd field-discriminant branch, surjectivity of the odd genus-character product
already gives the genus-theory divisibility needed by the class-number-one sieve. -/
theorem genus_divisibility_of_oddGenusCharacterProduct_surjective_of_discr_odd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hrel : oddGenusProductRelation d hd_neg)
    (hsurj :
      Function.Surjective
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) :=
  genus_divisibility_of_oddGenusCharacterProduct_surjective d hd_neg hrel hsurj
    (card_oddGenusSignRelationSubgroup_of_discr_odd d hodd)

/-- The standard genus formula for the principal-genus quotient
`Cl(𝓞(ℚ(√d))) / Cl(𝓞(ℚ(√d)))²`: its cardinality is `2 ^ (t - 1)`, where `t` is the
number of prime-discriminant factors. In the literature this is the statement that
`Cl / Cl²` is the genus group whose order — the *number of genera* — is `2 ^ (t - 1)`,
equivalently `#Cl[2] = 2 ^ (t - 1)`.

This is stated for all parameters `d`, but is only established in the imaginary
(`d < 0`) branch downstream; every theorem proving it carries an explicit `d < 0`
hypothesis. -/
def genusFormula (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : Prop :=
  Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
    2 ^ (primeDiscriminantFactorCount d - 1)

/-- The genus formula is equivalent to the corresponding cardinality statement for
the kernel of the square map on the ideal class group. -/
theorem genusFormula_iff_card_powMonoidHom_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    genusFormula d ↔
      Nat.card (powMonoidHom (α := ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) 2).ker =
        2 ^ (primeDiscriminantFactorCount d - 1) := by
  rw [genusFormula, card_squareClassSubgroup_quotient_eq_card_powMonoidHom_ker d]

/-- **Odd fundamental-discriminant genus formula.** For an imaginary quadratic field
with odd fundamental discriminant (`d % 4 = 1`), the principal-genus quotient
`Cl / Cl²` has the standard genus-theory cardinality.

This is the public proof boundary for the odd genus-theory route. Downstream
class-number-one and Baker--Heegner--Stark statements should call this theorem
directly rather than threading the product-relation, surjectivity, or
principal-kernel inputs as hypotheses.

This remains the full principal-genus cardinality boundary. The weaker
class-number-one route should use `genus_divisibility_of_mod_four_eq_one` from
`QuadraticNumberFields.ClassGroup.GenusTheory.Surjectivity` instead. -/
theorem genusFormula_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1) :
    genusFormula d := by
  sorry

/-- If the principal-genus quotient has the standard genus-theory cardinality,
then the standard genus-theory divisibility follows from Lagrange's theorem. -/
theorem genus_divisibility_of_squareClassSubgroup_quotient_card
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcard : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  rw [← hcard]
  simpa [NumberField.classNumber, Subgroup.index_eq_card] using
    (squareClassSubgroup d).index_dvd_card

end ClassGroup
end QuadraticNumberFields
