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

/-- Complete odd-discriminant genus-theory data for the current class-group interface.

This bundles the individual odd-prime genus characters, the single product relation,
surjectivity onto the relation subgroup, and the principal-kernel theorem saying that a
class in `Cl / Cl²` with all odd-prime genus characters trivial is itself trivial. -/
structure OddGenusFormulaData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0) where
  /-- Individual odd-prime genus characters. -/
  character : OddGenusCharacterData d
  /-- The single product relation among the odd-prime genus characters. -/
  relation : oddGenusProductRelation d hd_neg character
  /-- Every sign vector satisfying the product relation occurs as an odd genus character. -/
  surjective :
    Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg character relation)
  /-- The principal-kernel theorem for the odd-prime genus characters. -/
  principalKernel :
    ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
      (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        oddGenusCharacterProductOnSquareClassQuotient d hd_neg character C P = 1) → C = 1

/-- Surjectivity of the odd genus-character product together with trivial product
kernel packages the complete odd genus-formula data. -/
theorem OddGenusFormulaData.of_surjective_of_ker_eq_bot
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hker : (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥) :
    OddGenusFormulaData d hd_neg where
  character := hdata
  relation := hrel
  surjective := hsurj
  principalKernel :=
    (oddGenusCharacterProductToRelationSubgroup_ker_eq_bot_iff d hd_neg hdata hrel).mp hker

/-- Bijectivity of the relation-subgroup-valued odd genus-character product packages
the complete odd genus-formula data. -/
theorem OddGenusFormulaData.of_bijective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij :
      Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    OddGenusFormulaData d hd_neg where
  character := hdata
  relation := hrel
  surjective := hbij.2
  principalKernel := by
    have hker :
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)).mpr hbij.1
    exact
      (oddGenusCharacterProductToRelationSubgroup_ker_eq_bot_iff d hd_neg hdata hrel).mp hker

/-- Surjectivity of the relation-subgroup-valued odd genus-character product gives
the genus-theory divisibility needed by the class-number-one sieve. -/
theorem genus_divisibility_of_oddGenusCharacterProduct_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj : Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hcard : Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  let φ : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* oddGenusSignRelationSubgroup d :=
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).comp
      (QuotientGroup.mk' (squareClassSubgroup d))
  refine genus_divisibility_of_surjective_quotient d (oddGenusSignRelationSubgroup d)
    hcard φ ?_
  exact hsurj.comp (QuotientGroup.mk'_surjective (squareClassSubgroup d))

/-- In the odd field-discriminant branch, surjectivity of the odd genus-character product
already gives the genus-theory divisibility needed by the class-number-one sieve. -/
theorem genus_divisibility_of_oddGenusCharacterProduct_surjective_of_discr_odd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) :=
  genus_divisibility_of_oddGenusCharacterProduct_surjective d hd_neg hdata hrel hsurj
    (card_oddGenusSignRelationSubgroup_of_discr_odd d hodd)

/-- The standard genus formula for the principal-genus quotient
`Cl(𝓞(ℚ(√d))) / Cl(𝓞(ℚ(√d)))²`: its cardinality is `2 ^ (t - 1)`, where `t` is the
number of prime-discriminant factors. In the literature this is the statement that
`Cl / Cl²` is the genus group and each genus contains exactly `2 ^ (t - 1)` classes,
or equivalently `#Cl[2] = 2 ^ (t - 1)`. -/
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

/-- If the relation-subgroup-valued odd genus-character product is bijective and
the relation subgroup has the expected cardinality, then the standard genus
formula follows. -/
theorem genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij :
      Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hcard : Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1)) :
    genusFormula d := by
  dsimp [genusFormula]
  rw [← hcard]
  exact Nat.card_congr (Equiv.ofBijective _ hbij)

/-- In the odd field-discriminant branch, bijectivity of the relation-subgroup-valued
odd genus-character product implies the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective_of_discr_odd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij :
      Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d :=
  genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective d hd_neg hdata hrel hbij
    (card_oddGenusSignRelationSubgroup_of_discr_odd d hodd)

/-- In the odd field-discriminant branch, surjectivity of the relation-subgroup-valued
odd genus-character product proves the standard genus formula once the reverse
cardinality inequality for the principal-genus quotient is known. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_card_le
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hle : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) ≤
      Nat.card (oddGenusSignRelationSubgroup d)) :
    genusFormula d := by
  letI := _root_.NumberField.RingOfIntegers.instFintypeClassGroup (Qsqrtd (d : ℚ))
  have htarget_le : Nat.card (oddGenusSignRelationSubgroup d) ≤
      Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) :=
    Nat.card_le_card_of_surjective _ hsurj
  have hcard : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
      Nat.card (oddGenusSignRelationSubgroup d) :=
    le_antisymm hle htarget_le
  dsimp [genusFormula]
  rw [hcard, card_oddGenusSignRelationSubgroup_of_discr_odd d hodd]

/-- In the odd field-discriminant branch, surjectivity and injectivity of the
relation-subgroup-valued odd genus-character product prove the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_injective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hinj :
      Function.Injective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d := by
  have hcard := (MonoidHom.injective_iff_nat_card_eq_of_surjective
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel) hsurj).mp hinj
  dsimp [genusFormula]
  rw [hcard, card_oddGenusSignRelationSubgroup_of_discr_odd d hodd]

/-- In the odd field-discriminant branch, the standard genus formula follows once the
odd genus-character product is surjective and has trivial kernel on `Cl / Cl²`. This
is the kernel form of the principal-genus theorem for the odd-prime characters. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_ker_eq_bot
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hker : (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥) :
    genusFormula d := by
  have hcard := (MonoidHom.ker_eq_bot_iff_nat_card_eq_of_surjective
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel) hsurj).mp hker
  dsimp [genusFormula]
  rw [hcard, card_oddGenusSignRelationSubgroup_of_discr_odd d hodd]

/-- In the odd field-discriminant branch, once the relation-subgroup-valued odd
genus-character product is surjective, the standard genus formula is equivalent to
triviality of its kernel on `Cl / Cl²`. -/
theorem genusFormula_iff_oddGenusCharacterProduct_ker_eq_bot_of_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d ↔
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥ := by
  constructor
  · intro hgenus
    have hcard :
        Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
          Nat.card (oddGenusSignRelationSubgroup d) := by
      dsimp [genusFormula] at hgenus
      rw [hgenus, card_oddGenusSignRelationSubgroup_of_discr_odd d hodd]
    exact (MonoidHom.ker_eq_bot_iff_nat_card_eq_of_surjective
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel) hsurj).mpr hcard
  · intro hker
    have hcard := (MonoidHom.ker_eq_bot_iff_nat_card_eq_of_surjective
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel) hsurj).mp hker
    dsimp [genusFormula]
    rw [hcard, card_oddGenusSignRelationSubgroup_of_discr_odd d hodd]

/-- In the odd field-discriminant branch, once the relation-subgroup-valued odd
genus-character product is surjective, the standard genus formula is equivalent to
the principal-kernel statement: a class in `Cl / Cl²` whose odd-prime genus characters
are all trivial is itself trivial. -/
theorem genusFormula_iff_oddGenusPrincipalKernel_of_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1) → C = 1 := by
  rw [genusFormula_iff_oddGenusCharacterProduct_ker_eq_bot_of_surjective
    d hd_neg hodd hdata hrel hsurj]
  rw [oddGenusCharacterProductToRelationSubgroup_ker_eq_bot_iff]

/-- In the odd field-discriminant branch, surjectivity of the odd genus-character
product and the principal-kernel theorem prove the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_principalKernel
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hprincipal :
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1) → C = 1) :
    genusFormula d :=
  (genusFormula_iff_oddGenusPrincipalKernel_of_surjective d hd_neg hodd hdata hrel hsurj).2
    hprincipal

/-- In the odd field-discriminant branch, complete odd genus-formula data proves
the standard genus formula. -/
theorem genusFormula_of_oddGenusFormulaData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusFormulaData d hd_neg) :
    genusFormula d :=
  (genusFormula_iff_oddGenusPrincipalKernel_of_surjective d hd_neg hodd
    hdata.character hdata.relation hdata.surjective).2 hdata.principalKernel

/-- For odd fundamental discriminants (`d % 4 = 1`), surjectivity of the
relation-subgroup-valued odd genus-character product proves the standard genus formula
once the reverse cardinality inequality for the principal-genus quotient is known. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hle : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) ≤
      Nat.card (oddGenusSignRelationSubgroup d)) :
    genusFormula d := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_of_oddGenusCharacterProduct_surjective_of_card_le
    d hd_neg hodd hdata hrel hsurj hle

/-- For odd fundamental discriminants (`d % 4 = 1`), the standard genus formula follows
once the odd genus-character product is surjective and has trivial kernel on `Cl / Cl²`. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_ker_eq_bot_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hker : (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥) :
    genusFormula d := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_of_oddGenusCharacterProduct_surjective_of_ker_eq_bot
    d hd_neg hodd hdata hrel hsurj hker

/-- For odd fundamental discriminants (`d % 4 = 1`), once the odd genus-character
product is surjective, the standard genus formula is equivalent to triviality of
its kernel on `Cl / Cl²`. -/
theorem genusFormula_iff_oddGenusCharacterProduct_ker_eq_bot_of_surjective_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d ↔
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥ := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_iff_oddGenusCharacterProduct_ker_eq_bot_of_surjective
    d hd_neg hodd hdata hrel hsurj

/-- For odd fundamental discriminants (`d % 4 = 1`), once the odd genus-character
product is surjective, the standard genus formula is equivalent to the principal-kernel
statement for the odd-prime genus characters. -/
theorem genusFormula_iff_oddGenusPrincipalKernel_of_surjective_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1) → C = 1 := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_iff_oddGenusPrincipalKernel_of_surjective
    d hd_neg hodd hdata hrel hsurj

/-- For odd fundamental discriminants (`d % 4 = 1`), surjectivity of the odd
genus-character product and the principal-kernel theorem prove the standard
genus formula. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_principalKernel_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hprincipal :
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1) → C = 1) :
    genusFormula d :=
  (genusFormula_iff_oddGenusPrincipalKernel_of_surjective_of_mod_four_eq_one
    d hd_neg hd4 hdata hrel hsurj).2 hprincipal

/-- For odd fundamental discriminants (`d % 4 = 1`), complete odd genus-formula data
proves the standard genus formula. -/
theorem genusFormula_of_oddGenusFormulaData_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusFormulaData d hd_neg) :
    genusFormula d := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_of_oddGenusFormulaData d hd_neg hodd hdata

/-- In the odd field-discriminant branch, the existing odd-prime genus-character
interface implies the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij : Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d :=
  genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective_of_discr_odd
    d hd_neg hodd hdata hrel hbij

/-- For odd fundamental discriminants (`d % 4 = 1`), the existing odd-prime
genus-character interface implies the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterData_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij : Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_of_oddGenusCharacterData d hd_neg hodd hdata hrel hbij

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
