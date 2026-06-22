/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.CoprimeRepresentatives
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

/-- The product of all odd-prime genus characters on the principal-genus quotient.

The remaining genus-theory relation and independence statements identify the image of
this map with the sign vectors satisfying the single product relation. -/
noncomputable def oddGenusCharacterProductOnSquareClassQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d →*
      ((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) :=
  Pi.monoidHom fun P => by
    haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
    exact genusCharacterOnSquareClassQuotient d P.1 hd_neg P.2

/-- The product character evaluates componentwise to the corresponding odd-prime
genus character. -/
theorem oddGenusCharacterProductOnSquareClassQuotient_apply
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d)
    (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) :
    oddGenusCharacterProductOnSquareClassQuotient d hd_neg C P = by
      haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
      exact genusCharacterOnSquareClassQuotient d P.1 hd_neg P.2 C := by
  rfl

/-- On a representative class, each coordinate of the odd genus-character product
is the corresponding descended odd-prime genus character. -/
theorem oddGenusCharacterProductOnSquareClassQuotient_apply_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))))
    (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) :
    oddGenusCharacterProductOnSquareClassQuotient d hd_neg
        ((QuotientGroup.mk' (squareClassSubgroup d)) C) P = by
      haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
      exact genusCharacterOfAbsNormCoprimeIdeals d P.1 hd_neg P.2 C := by
  haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
  rw [oddGenusCharacterProductOnSquareClassQuotient_apply]
  exact genusCharacterOnSquareClassQuotient_apply d P.1 hd_neg P.2 C

/-- On a representative class, the coordinate product of the odd genus-character
product is the product of the corresponding descended odd-prime genus characters. -/
theorem oddGenusCharacterProductOnSquareClassQuotient_prod_apply_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    Finset.univ.prod
        (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} =>
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg
            ((QuotientGroup.mk' (squareClassSubgroup d)) C) P) =
      Finset.univ.prod
        (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} => by
          haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
          exact genusCharacterOfAbsNormCoprimeIdeals d P.1 hd_neg P.2 C) := by
  apply Finset.prod_congr rfl
  intro P _
  exact oddGenusCharacterProductOnSquareClassQuotient_apply_mk'
    d hd_neg C P

/-- If a class has a single ideal representative whose norm is prime to every odd
discriminant prime, then the product of the descended odd genus characters on
that class is the corresponding product of Legendre symbols of the representative's
absolute norm. -/
theorem oddGenusCharacterProduct_prod_apply_eq_prod_legendreSym_of_mk0
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))))
    (I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰)
    (hC : ClassGroup.mk0 I = C)
    (hI : ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
      ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ)) :
    ((Finset.univ.prod
      (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} => by
        haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
        exact genusCharacterOfAbsNormCoprimeIdeals d P.1 hd_neg P.2 C) : ℤˣ) : ℤ) =
      (oddPrimeDiscriminantDivisors d).prod
        (fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩
          (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ) else 1) := by
  rw [← Finset.attach_eq_univ (s := oddPrimeDiscriminantDivisors d)]
  conv_rhs =>
    rw [← Finset.prod_attach (s := oddPrimeDiscriminantDivisors d)
      (f := fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩
        (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ) else 1)]
  rw [Units.coe_prod]
  apply Finset.prod_congr rfl
  intro P _hP
  haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
  let IP : absNormCoprimeIdealSubmonoid d P.1 :=
    ⟨(I : Ideal (𝓞 (Qsqrtd (d : ℚ)))), hI P⟩
  have hmk : mk0OnAbsNormCoprimeIdeals d P.1 IP = C := by
    simpa [IP, mk0OnAbsNormCoprimeIdeals, absNormCoprimeIdealNonzeroMonoidHom] using hC
  have happly := genusCharacterOfAbsNormCoprimeIdeals_apply_mk0OnAbsNormCoprimeIdeals
    d P.1 hd_neg P.2 IP
  rw [hmk] at happly
  rw [happly]
  simp [IP, genusCharacterRawUnit, genusCharacterRaw,
    prime_of_mem_oddPrimeDiscriminantDivisors P.2]

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
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0) : Prop :=
  ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
    oddGenusCharacterProductOnSquareClassQuotient d hd_neg C ∈
      oddGenusSignRelationSubgroup d

/-- The product-relation assertion is equivalently the statement that, for every
class in `Cl / Cl²`, the product of all odd-prime genus-character coordinates is
`1`. -/
theorem oddGenusProductRelation_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0) :
    oddGenusProductRelation d hd_neg ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        Finset.univ.prod
          (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} =>
            oddGenusCharacterProductOnSquareClassQuotient
              d hd_neg C P) = 1 := by
  constructor
  · intro hrel C
    exact (mem_oddGenusSignRelationSubgroup_iff d _).mp (hrel C)
  · intro hrel C
    exact (mem_oddGenusSignRelationSubgroup_iff d _).mpr (hrel C)

/-- The product-relation assertion can be checked on representatives in the
class group instead of arbitrary quotient classes in `Cl / Cl²`. -/
theorem oddGenusProductRelation_iff_forall_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0) :
    oddGenusProductRelation d hd_neg ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))),
        (Finset.univ.prod
          (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} => by
            haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
            exact genusCharacterOfAbsNormCoprimeIdeals d P.1 hd_neg P.2 C) : ℤˣ) = 1 := by
  rw [oddGenusProductRelation_iff]
  constructor
  · intro hrel C
    rw [← oddGenusCharacterProductOnSquareClassQuotient_prod_apply_mk'
      d hd_neg C]
    exact hrel ((QuotientGroup.mk' (squareClassSubgroup d)) C)
  · intro hrel C
    rcases QuotientGroup.mk'_surjective (squareClassSubgroup d) C with ⟨C, rfl⟩
    rw [oddGenusCharacterProductOnSquareClassQuotient_prod_apply_mk']
    exact hrel C

/-- In the odd fundamental-discriminant branch, the product relation follows if
each class has a single ideal representative whose norm is prime to every odd
discriminant prime and whose absolute norm has Jacobi symbol `1` modulo `|d|`.

This isolates the remaining ideal-theoretic content needed to prove the product
relation from the already formalized Legendre/Jacobi product computation. -/
theorem oddGenusProductRelation_of_jacobiSym_absNorm_eq_one_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hrep : ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))),
      ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
        ClassGroup.mk0 I = C ∧
          ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
            ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ))
    (hjac : ∀ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
      (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ)) →
        jacobiSym (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ) d.natAbs = 1) :
    oddGenusProductRelation d hd_neg := by
  rw [oddGenusProductRelation_iff_forall_mk']
  intro C
  rcases hrep C with ⟨I, hC, hI⟩
  apply Units.ext
  change ((Finset.univ.prod
    (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} => by
      haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
      exact genusCharacterOfAbsNormCoprimeIdeals d P.1 hd_neg P.2 C) : ℤˣ) : ℤ) = 1
  rw [oddGenusCharacterProduct_prod_apply_eq_prod_legendreSym_of_mk0
    d hd_neg C I hC hI]
  rw [← jacobiSym_natAbs_eq_prod_oddPrimeDiscriminantDivisors_of_mod_four_eq_one
    d ((Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ))))) : ℤ)
    (Fact.out : Squarefree d) hd4]
  exact hjac I hI

/-- In the odd fundamental-discriminant branch, the product relation follows from
a Kronecker-symbol norm-one statement for a simultaneous prime-to-discriminant
representative of each ideal class.

This is the product-relation interface most directly compatible with the
splitting classification, where prime ideal factors of an ideal norm are read
through the Kronecker symbol of the field discriminant. -/
theorem oddGenusProductRelation_of_kroneckerSymNat_absNorm_eq_one_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hrep : ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))),
      ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
        ClassGroup.mk0 I = C ∧
          ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
            ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ))
    (hkron : ∀ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
      (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ)) →
        kroneckerSymNat (RingOfIntegers.discrFormula d)
          (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ))))) = 1) :
    oddGenusProductRelation d hd_neg :=
  oddGenusProductRelation_of_jacobiSym_absNorm_eq_one_of_mod_four_eq_one
    d hd_neg hd4 hrep fun I hI => by
      rw [jacobiSym_natAbs_eq_kroneckerSymNat_discrFormula_of_mod_four_eq_one
        d (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ))))) hd4]
      exact hkron I hI

/-- In the odd fundamental-discriminant branch, if a nonzero ideal has norm
prime to every odd discriminant divisor, then the Kronecker symbol of the field
discriminant evaluates to `1` at its absolute norm. -/
theorem kroneckerSymNat_discrFormula_absNorm_eq_one_of_not_dvd_oddPrimeDiscriminantDivisors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd4 : d % 4 = 1)
    (I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰)
    (hI : ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
      ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ)) :
    kroneckerSymNat (RingOfIntegers.discrFormula d)
      (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ))))) = 1 := by
  rw [← RingOfIntegers.discr_formula d]
  apply Splitting.kroneckerSymNat_discr_absNorm_eq_one_of_forall_prime_dvd_not_isRamifiedIn d
  · exact nonZeroDivisors.coe_ne_zero I
  · intro p hp hpabs hram
    haveI : Fact p.Prime := ⟨hp⟩
    have hp_disc : (p : ℤ) ∣ disc(d) :=
      (Splitting.isRamified_iff_dvd_disc d p).mp hram
    rw [RingOfIntegers.discr_formula d, RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
      at hp_disc
    have hp_mem_disc : p ∈ (RingOfIntegers.discrFormula d).natAbs.primeFactors := by
      rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, ?_⟩
      · exact Int.natCast_dvd.mp hp_disc
      · exact Int.natAbs_ne_zero.mpr (Fact.out : Squarefree d).ne_zero
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      subst p
      omega
    have hp_odd : p ∈ oddPrimeDiscriminantDivisors d := by
      rw [mem_oddPrimeDiscriminantDivisors_iff]
      exact ⟨hp_mem_disc, hp_ne_two⟩
    exact hI ⟨p, hp_odd⟩ (by exact_mod_cast hpabs)

/-- In the odd fundamental-discriminant branch, the product relation follows
from a simultaneous representative theorem avoiding all odd discriminant
divisors. -/
theorem oddGenusProductRelation_of_coprime_representatives_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hrep : ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))),
      ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
        ClassGroup.mk0 I = C ∧
          ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
            ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ)) :
    oddGenusProductRelation d hd_neg :=
  oddGenusProductRelation_of_kroneckerSymNat_absNorm_eq_one_of_mod_four_eq_one
    d hd_neg hd4 hrep fun I hI =>
      kroneckerSymNat_discrFormula_absNorm_eq_one_of_not_dvd_oddPrimeDiscriminantDivisors
        d hd4 I hI

/-- In the odd fundamental-discriminant branch, coprime representatives supply the
representatives needed for the product relation. -/
theorem oddGenusProductRelation_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1) :
    oddGenusProductRelation d hd_neg :=
  oddGenusProductRelation_of_coprime_representatives_of_mod_four_eq_one
    d hd_neg hd4
    (exists_absNorm_coprime_representative_oddPrimeDiscriminantDivisors d)

/-- The product of the odd-prime genus characters, with codomain restricted to the
single-relation sign subgroup. -/
noncomputable def oddGenusCharacterProductToRelationSubgroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hrel : oddGenusProductRelation d hd_neg) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d →*
      oddGenusSignRelationSubgroup d where
  toFun C :=
    ⟨oddGenusCharacterProductOnSquareClassQuotient
      d hd_neg C, hrel C⟩
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
    (hrel : oddGenusProductRelation d hd_neg)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) :
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel C :
      (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) =
      oddGenusCharacterProductOnSquareClassQuotient d hd_neg C := by
  rfl

/-- Membership in the kernel of the relation-subgroup-valued product character is
equivalent to every odd-prime genus character being trivial. -/
theorem mem_oddGenusCharacterProductToRelationSubgroup_ker_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hrel : oddGenusProductRelation d hd_neg)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) :
    C ∈ (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel).ker ↔
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        oddGenusCharacterProductOnSquareClassQuotient d hd_neg C P = 1 := by
  constructor
  · intro hC P
    have hmap :
        oddGenusCharacterProductToRelationSubgroup d hd_neg hrel C =
          1 := by
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
    (hrel : oddGenusProductRelation d hd_neg) :
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel).ker = ⊥ ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient
            d hd_neg C P = 1) → C = 1 := by
  constructor
  · intro hker C hC
    have hinj :
        Function.Injective
          (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel) :=
      (MonoidHom.ker_eq_bot_iff
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel)).mp hker
    rw [injective_iff_map_eq_one] at hinj
    apply hinj
    ext P
    simpa [oddGenusCharacterProductToRelationSubgroup_apply] using hC P
  · intro h
    apply (MonoidHom.ker_eq_bot_iff
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel)).mpr
    rw [injective_iff_map_eq_one]
    intro C hC
    apply h C
    intro P
    have hval := congr_arg Subtype.val hC
    exact congr_fun hval P

end ClassGroup
end QuadraticNumberFields
