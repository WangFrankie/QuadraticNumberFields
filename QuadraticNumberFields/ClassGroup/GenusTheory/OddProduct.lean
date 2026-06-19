/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.SquareClass

/-!
# Odd Genus Character Product

This file packages the odd-prime genus characters into a product character and
records the product-one sign relation used in the odd-discriminant genus formula.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

open RingOfIntegers
open Splitting

local notation "𝓞" => _root_.NumberField.RingOfIntegers

/-- Ideal-avoidance data needed to construct all odd-prime genus characters.

The two fields are the remaining local inputs not supplied by the raw Legendre-symbol
calculation: every class must have a representative whose norm is prime to `p`, and
equal such representatives must have principal multipliers still prime to `p`. -/
structure OddGenusCharacterData (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] where
  /-- Every ideal class has a representative whose norm is prime to `p`. -/
  surjective : ∀ (p : ℕ) [Fact p.Prime], p ∈ oddPrimeDiscriminantDivisors d →
    Function.Surjective (mk0OnPrimeToNormIdeals d p)
  /-- Equal prime-to-`p` representatives have a compatible principal multiplier
  whose norm stays prime to `p`. -/
  principalMultiplier :
    ∀ (p : ℕ) [Fact p.Prime], p ∈ oddPrimeDiscriminantDivisors d →
      HasPrimeToNormPrincipalMultiplierData d p

/-- The product of all odd-prime genus characters on the principal-genus quotient.

The remaining genus-theory relation and independence statements identify the image of
this map with the sign vectors satisfying the single product relation. -/
noncomputable def oddGenusCharacterProductOnSquareClassQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d →*
      ((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) :=
  Pi.monoidHom fun P => by
    haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
    exact genusCharacterOnSquareClassQuotient d P.1 hd_neg P.2
      (hdata.surjective P.1 P.2) (hdata.principalMultiplier P.1 P.2)

/-- The product character evaluates componentwise to the corresponding odd-prime
genus character. -/
theorem oddGenusCharacterProductOnSquareClassQuotient_apply
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d)
    (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) :
    oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = by
      haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
      exact genusCharacterOnSquareClassQuotient d P.1 hd_neg P.2
        (hdata.surjective P.1 P.2) (hdata.principalMultiplier P.1 P.2) C := by
  rfl

/-- Product of all coordinates of an odd-prime sign vector. -/
noncomputable def oddGenusSignProductHom (d : ℤ) :
    (((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) →* ℤˣ) where
  toFun v := Finset.univ.prod fun P => v P
  map_one' := by simp
  map_mul' v w := by
    change Finset.univ.prod (fun P => v P * w P) =
      Finset.univ.prod (fun P => v P) * Finset.univ.prod (fun P => w P)
    rw [Finset.prod_mul_distrib]

/-- The subgroup of sign vectors whose component product is `1`. In the odd
fundamental-discriminant branch this is the expected target of the genus-character map:
all odd-prime genus characters satisfy one product relation. -/
noncomputable def oddGenusSignRelationSubgroup (d : ℤ) :
    Subgroup ((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) :=
  (oddGenusSignProductHom d).ker

/-- Membership in the odd-genus sign relation subgroup is the product-one relation. -/
theorem mem_oddGenusSignRelationSubgroup_iff (d : ℤ)
    (v : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) :
    v ∈ oddGenusSignRelationSubgroup d ↔ Finset.univ.prod (fun P => v P) = 1 :=
  Iff.rfl

/-- If there is at least one odd discriminant divisor, the coordinate-product map
from sign vectors to `ℤˣ` is surjective. -/
theorem oddGenusSignProductHom_surjective_of_nonempty
    (d : ℤ) (hS : (oddPrimeDiscriminantDivisors d).Nonempty) :
    Function.Surjective (oddGenusSignProductHom d) := by
  classical
  obtain ⟨p, hp⟩ := hS
  let P : {p // p ∈ oddPrimeDiscriminantDivisors d} := ⟨p, hp⟩
  intro u
  refine ⟨fun Q => if Q = P then u else 1, ?_⟩
  dsimp [oddGenusSignProductHom]
  rw [Finset.prod_ite_eq']
  simp

/-- The full odd-prime sign-vector space has cardinality `2 ^ #S`, where `S` is
the set of odd discriminant divisors. -/
theorem card_oddGenusSignVectors (d : ℤ) :
    Nat.card ((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) =
      2 ^ (oddPrimeDiscriminantDivisors d).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  rw [Fintype.card_units_int, Fintype.card_coe]

/-- If the odd discriminant-divisor set is nonempty, the product-one sign
relation subgroup has cardinality `2 ^ (#S - 1)`. -/
theorem card_oddGenusSignRelationSubgroup_of_nonempty
    (d : ℤ) (hS : (oddPrimeDiscriminantDivisors d).Nonempty) :
    Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ ((oddPrimeDiscriminantDivisors d).card - 1) := by
  classical
  have hsurj := oddGenusSignProductHom_surjective_of_nonempty d hS
  have hindex : (oddGenusSignRelationSubgroup d).index = 2 := by
    calc
      (oddGenusSignRelationSubgroup d).index = Nat.card (oddGenusSignProductHom d).range := by
        rw [oddGenusSignRelationSubgroup, Subgroup.index_ker]
      _ = Nat.card (⊤ : Subgroup ℤˣ) := by
        rw [MonoidHom.range_eq_top.mpr hsurj]
      _ = 2 := by
        rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hmul := (oddGenusSignRelationSubgroup d).card_mul_index
  rw [hindex, card_oddGenusSignVectors d] at hmul
  have hcard_pos : 0 < (oddPrimeDiscriminantDivisors d).card := Finset.card_pos.mpr hS
  have hpow : 2 ^ (oddPrimeDiscriminantDivisors d).card =
      2 ^ ((oddPrimeDiscriminantDivisors d).card - 1) * 2 := by
    have hsucc : (oddPrimeDiscriminantDivisors d).card =
        ((oddPrimeDiscriminantDivisors d).card - 1) + 1 := by omega
    calc
      2 ^ (oddPrimeDiscriminantDivisors d).card =
          2 ^ (((oddPrimeDiscriminantDivisors d).card - 1) + 1) := by rw [← hsucc]
      _ = 2 ^ ((oddPrimeDiscriminantDivisors d).card - 1) * 2 := by rw [pow_succ]
  rw [hpow] at hmul
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) hmul

/-- The product-one sign relation subgroup has cardinality `2 ^ (#S - 1)`, also
covering the empty-index case by natural-number subtraction. -/
theorem card_oddGenusSignRelationSubgroup (d : ℤ) :
    Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ ((oddPrimeDiscriminantDivisors d).card - 1) := by
  classical
  by_cases hS : (oddPrimeDiscriminantDivisors d).Nonempty
  · exact card_oddGenusSignRelationSubgroup_of_nonempty d hS
  · have hempty : oddPrimeDiscriminantDivisors d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hrel_top : oddGenusSignRelationSubgroup d = ⊤ := by
      haveI : IsEmpty {p // p ∈ oddPrimeDiscriminantDivisors d} := by
        refine ⟨?_⟩
        intro P
        have hp_empty : P.1 ∈ (∅ : Finset ℕ) := by
          simpa [hempty] using P.property
        simp at hp_empty
      ext v
      simp [oddGenusSignRelationSubgroup, oddGenusSignProductHom]
    rw [hrel_top, Subgroup.card_top, card_oddGenusSignVectors d, hempty]
    norm_num

/-- In the odd field-discriminant branch, the product-one sign relation subgroup
has the genus-theory cardinality `2 ^ (t - 1)`. -/
theorem card_oddGenusSignRelationSubgroup_of_discr_odd
    (d : ℤ) (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0) :
    Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1) := by
  rw [card_oddGenusSignRelationSubgroup,
    card_oddPrimeDiscriminantDivisors_eq_primeDiscriminantFactorCount_of_discr_odd d hodd]

/-- The product-relation assertion for the odd-prime genus characters. This is one
of the remaining genus-theory inputs after constructing the individual characters. -/
def oddGenusProductRelation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d) : Prop :=
  ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
    oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C ∈
      oddGenusSignRelationSubgroup d

/-- The product of the odd-prime genus characters, with codomain restricted to the
single-relation sign subgroup. -/
noncomputable def oddGenusCharacterProductToRelationSubgroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d →*
      oddGenusSignRelationSubgroup d where
  toFun C := ⟨oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C, hrel C⟩
  map_one' := by
    ext P
    simp
  map_mul' C D := by
    ext P
    simp

/-- The relation-subgroup-valued product character forgets to the raw product
character. -/
theorem oddGenusCharacterProductToRelationSubgroup_apply
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) :
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel C :
      (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) =
      oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C := by
  rfl

/-- Membership in the kernel of the relation-subgroup-valued product character is
equivalent to every odd-prime genus character being trivial. -/
theorem mem_oddGenusCharacterProductToRelationSubgroup_ker_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) :
    C ∈ (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker ↔
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1 := by
  constructor
  · intro hC P
    have hmap : oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel C = 1 := by
      simpa [MonoidHom.mem_ker] using hC
    have hval := congr_arg Subtype.val hmap
    exact congr_fun hval P
  · intro hC
    rw [MonoidHom.mem_ker]
    ext P
    simpa [oddGenusCharacterProductToRelationSubgroup_apply] using hC P

/-- The product character has trivial kernel exactly when the only class whose
odd-prime genus characters are all trivial is the trivial class of `Cl / Cl²`. -/
theorem oddGenusCharacterProductToRelationSubgroup_ker_eq_bot_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata) :
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥ ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1) → C = 1 := by
  constructor
  · intro hker C hC
    have hinj :
        Function.Injective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel) :=
      (MonoidHom.ker_eq_bot_iff
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)).mp hker
    rw [injective_iff_map_eq_one] at hinj
    apply hinj
    ext P
    simpa [oddGenusCharacterProductToRelationSubgroup_apply] using hC P
  · intro h
    apply (MonoidHom.ker_eq_bot_iff
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)).mpr
    rw [injective_iff_map_eq_one]
    intro C hC
    apply h C
    intro P
    have hval := congr_arg Subtype.val hC
    exact congr_fun hval P

end ClassGroup
end QuadraticNumberFields
