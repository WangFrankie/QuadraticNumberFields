/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import QuadraticNumberFields.ClassGroup.GenusTheory.GenusTheorem
import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.ClassGroup.Narrow.Principal

/-!
# Ordinary Genus Theory for Real Quadratic Fields

This file compares the square-class quotients of the narrow and ordinary class
groups of `ℚ(√d)`.  The ordinary genus formula differs from the uniform narrow
formula only by the kernel of the induced map

`Cl⁺(d) / Cl⁺(d)² → Cl(d) / Cl(d)²`.

For a real quadratic field, Emerton's items 8, 9, and 12 give three cases. A
fundamental unit of norm `-1` forces the narrow and ordinary class groups to
coincide. If its norm is `1`, the comparison kernel has order two; this kernel
survives in the narrow square quotient exactly when the field discriminant has
a prime divisor congruent to `3` modulo `4`.

Writing `t` for the number of ramified rational primes, the cases are:

* norm `-1`: no such discriminant prime, `Cl⁺(d) ≃ Cl(d)`, and ordinary
  `2`-rank `t - 1`;
* norm `1` with such a prime: correction dimension `1` and ordinary `2`-rank
  `t - 2`;
* norm `1` without such a prime: correction dimension `0` and ordinary
  `2`-rank `t - 1`.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup
open CommGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" =>
  NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- The natural map `Cl⁺(d) → Cl(d)` descends to square quotients. -/
noncomputable def narrowSquareQuotientToClassGroup :
    squareQuotient (Cl⁺(d)) →* squareQuotient (Cl(d)) :=
  squareQuotientMap (Qsqrtd.narrowToClassGroup d)

@[simp]
theorem narrowSquareQuotientToClassGroup_mk' (C : Cl⁺(d)) :
    narrowSquareQuotientToClassGroup d
        (C : squareQuotient (Cl⁺(d))) =
      QuotientGroup.mk' (Subgroup.square (Cl(d))) (Qsqrtd.narrowToClassGroup d C) :=
  squareQuotientMap_mk (Qsqrtd.narrowToClassGroup d) C

/-- The map from narrow to ordinary square classes is surjective. -/
theorem narrowSquareQuotientToClassGroup_surjective :
    Function.Surjective (narrowSquareQuotientToClassGroup d) :=
  squareQuotientMap_surjective (Qsqrtd.narrowToClassGroup d)
    (NarrowClassGroup.toClassGroup_surjective OK)

/-- The map from narrow to ordinary square classes as a linear map over `ZMod 2`. -/
noncomputable def narrowSquareQuotientLinearMap :
    Additive (squareQuotient (Cl⁺(d))) →ₗ[ZMod 2]
      Additive (squareQuotient (Cl(d))) :=
  squareQuotientLinearMap (Qsqrtd.narrowToClassGroup d)

/-- The linear map from narrow to ordinary square classes is surjective. -/
theorem narrowSquareQuotientLinearMap_surjective :
    Function.Surjective (narrowSquareQuotientLinearMap d) :=
  squareQuotientLinearMap_surjective (Qsqrtd.narrowToClassGroup d)
    (NarrowClassGroup.toClassGroup_surjective OK)

/-- The correction kernel is the image of `ker(Cl⁺(d) → Cl(d))` in the narrow
square-class quotient. -/
theorem narrowSquareQuotientToClassGroup_ker_eq_map_narrowToClassGroup_ker :
    (narrowSquareQuotientToClassGroup d).ker =
      Subgroup.map (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))))
        (Qsqrtd.narrowToClassGroup d).ker :=
  squareQuotientMap_ker_eq_map_ker_of_surjective (Qsqrtd.narrowToClassGroup d)
    (NarrowClassGroup.toClassGroup_surjective OK)

/-- If the discriminant has no prime divisor congruent to `3` modulo `4`, an
ordinary-principal narrow class has trivial genus characters. -/
theorem genusCharacterMap_eq_one_of_narrowToClassGroup_eq_one_of_no_prime_mod_four_three
    (hdisc : ¬ DiscriminantHasPrimeModFourThree d) {C : Cl⁺(d)}
    (hC : Qsqrtd.narrowToClassGroup d C = 1) :
    genusCharacterMap d C = 1 := by
  apply Subtype.ext
  funext p
  change genusCharacter d p C = 1
  by_cases hp2 : p.1 = 2
  · have hrest :
        ∏ q ∈ (Finset.univ.erase p), genusCharacter d q C = 1 := by
      apply Finset.prod_eq_one
      intro q hq
      have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
      have hq2 : q.1 ≠ 2 := by
        intro hq2
        exact hqp (Subtype.ext (hq2.trans hp2.symm))
      exact
        genusCharacter_eq_one_of_narrowToClassGroup_eq_one_of_mod_four_one
          d q ((not_discriminantHasPrimeModFourThree_iff d).1 hdisc q hq2) C hC
    have hprod := genusCharacter_product_eq_one d C
    have herase :=
      Finset.prod_erase_mul Finset.univ (fun q : RamifiedPrimeIndex d ↦
        genusCharacter d q C) (Finset.mem_univ p)
    calc
      genusCharacter d p C =
          (∏ q ∈ (Finset.univ.erase p), genusCharacter d q C) *
            genusCharacter d p C := by rw [hrest, one_mul]
      _ = ∏ q : RamifiedPrimeIndex d, genusCharacter d q C := herase
      _ = 1 := hprod
  · exact
      genusCharacter_eq_one_of_narrowToClassGroup_eq_one_of_mod_four_one
        d p ((not_discriminantHasPrimeModFourThree_iff d).1 hdisc p hp2) C hC

/-- With no discriminant prime congruent to `3` modulo `4`, the narrow-to-wide
map is injective on square classes. -/
theorem narrowSquareQuotientToClassGroup_ker_eq_bot_of_no_prime_mod_four_three
    (hdisc : ¬ DiscriminantHasPrimeModFourThree d) :
    (narrowSquareQuotientToClassGroup d).ker = ⊥ := by
  rw [narrowSquareQuotientToClassGroup_ker_eq_map_narrowToClassGroup_ker d]
  refine le_antisymm ?_ bot_le
  rintro _ ⟨C, hC, rfl⟩
  rw [Subgroup.mem_bot]
  apply (QuotientGroup.eq_one_iff C).2
  rw [← genusCharacterMap_ker_eq_square d, MonoidHom.mem_ker]
  exact genusCharacterMap_eq_one_of_narrowToClassGroup_eq_one_of_no_prime_mod_four_three
    d hdisc (MonoidHom.mem_ker.mp hC)

/-- A unit of norm `-1` rules out discriminant prime divisors congruent to `3`
modulo `4`. -/
theorem not_discriminantHasPrimeModFourThree_of_unit_algebraNorm_eq_neg_one
    (ε : OKˣ) (hε : Algebra.norm ℤ (ε : OK) = -1) :
    ¬ DiscriminantHasPrimeModFourThree d := by
  rintro ⟨p, hp4⟩
  have hspan : Ideal.span ({(ε : OK)} : Set OK) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr ε.isUnit
  have hlocal :=
    kroneckerSymNat_primeDiscriminantFactor_absNorm_span_eq_neg_one_of_mod_four_three
      d p hp4 (by omega : Algebra.norm ℤ (ε : OK) < 0) (by
        rw [hspan]
        simp)
  rw [hspan] at hlocal
  simp [kroneckerSymNat] at hlocal

/-- With no discriminant prime congruent to `3` modulo `4`, the induced linear
map on square classes is injective. -/
theorem narrowSquareQuotientLinearMap_ker_eq_bot_of_no_prime_mod_four_three
    (hdisc : ¬ DiscriminantHasPrimeModFourThree d) :
    (narrowSquareQuotientLinearMap d).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  apply Additive.toMul.injective
  apply (MonoidHom.ker_eq_bot_iff (narrowSquareQuotientToClassGroup d)).1
    (narrowSquareQuotientToClassGroup_ker_eq_bot_of_no_prime_mod_four_three
      d hdisc)
  simpa using congrArg Additive.toMul hxy

private theorem squareClassMap_injective_on_narrowToClassGroup_ker_of_mod_four_three
    (hd : 0 < d) (p : RamifiedPrimeIndex d) (hp4 : p.1 % 4 = 3) :
    Function.Injective
      ((QuotientGroup.mk' (Subgroup.square (Cl⁺(d)))).comp
        (Qsqrtd.narrowToClassGroup d).ker.subtype) := by
  let K := (Qsqrtd.narrowToClassGroup d).ker
  let q : K →* squareQuotient (Cl⁺(d)) :=
    (QuotientGroup.mk' (Subgroup.square (Cl⁺(d)))).comp K.subtype
  intro C D hCD
  let E : K := C / D
  have hqE : q E = 1 := by
    have hCD' :
        (QuotientGroup.mk' (Subgroup.square (Cl⁺(d)))) (C : Cl⁺(d)) =
          (QuotientGroup.mk' (Subgroup.square (Cl⁺(d)))) (D : Cl⁺(d)) := by
      simpa [q, K] using hCD
    change (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))))
      ((C : Cl⁺(d)) / (D : Cl⁺(d))) = 1
    rw [map_div, hCD']
    simp
  have hE_square : (E : Cl⁺(d)) ∈ Subgroup.square (Cl⁺(d)) :=
    (QuotientGroup.eq_one_iff (E : Cl⁺(d))).1 hqE
  have hE : E = 1 := by
    by_contra hE1
    have hE1' : (E : Cl⁺(d)) ≠ 1 := by
      intro h
      exact hE1 (Subtype.ext h)
    have hchar_neg :=
      genusCharacter_eq_neg_one_of_narrowToClassGroup_eq_one_of_mod_four_three
        d hd p hp4 (E : Cl⁺(d)) (MonoidHom.mem_ker.mp E.2) hE1'
    have hgenus : genusCharacterMap d (E : Cl⁺(d)) = 1 :=
      (genusCharacterMap_eq_one_iff d (E : Cl⁺(d))).2 (by rwa [← Subgroup.mem_square])
    have hchar_one : genusCharacter d p (E : Cl⁺(d)) = 1 := by
      have hcoord := congrArg
        (fun v : AdmissibleGenusSignVector d ↦ (v : GenusSignVector d) p) hgenus
      simpa using hcoord
    rw [hchar_neg] at hchar_one
    norm_num at hchar_one
  apply Subtype.ext
  have hEval : (C : Cl⁺(d)) / (D : Cl⁺(d)) = 1 := by
    simpa [E] using congrArg Subtype.val hE
  exact div_eq_one.mp hEval

/-- If the comparison kernel has order two and the discriminant has a prime
divisor congruent to `3` modulo `4`, its full order-two image survives in the
narrow square quotient. -/
theorem card_narrowSquareQuotientToClassGroup_ker_eq_two_of_mod_four_three
    (hd : 0 < d) (p : RamifiedPrimeIndex d) (hp4 : p.1 % 4 = 3)
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker = 2) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker = 2 := by
  let K := (Qsqrtd.narrowToClassGroup d).ker
  let q : K →* squareQuotient (Cl⁺(d)) :=
    (QuotientGroup.mk' (Subgroup.square (Cl⁺(d)))).comp K.subtype
  have hqinj : Function.Injective q := by
    simpa [q, K] using
      squareClassMap_injective_on_narrowToClassGroup_ker_of_mod_four_three
        d hd p hp4
  have hcard_range : Nat.card q.range = 2 := by
    change Nat.card (Set.range q) = 2
    exact (Nat.card_range_of_injective hqinj).trans hker
  have hrange :
      q.range =
        Subgroup.map (QuotientGroup.mk' (Subgroup.square (Cl⁺(d)))) K := by
    ext x
    simp [q]
  rw [narrowSquareQuotientToClassGroup_ker_eq_map_narrowToClassGroup_ker d,
    ← hrange]
  exact hcard_range

/-- In the order-two correction case, the linear correction has dimension
one over `ZMod 2`. -/
theorem finrank_narrowSquareQuotientLinearMap_ker_eq_one_of_mod_four_three
    (hd : 0 < d) (p : RamifiedPrimeIndex d) (hp4 : p.1 % 4 = 3)
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker = 2) :
    Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker = 1 := by
  have hcard_group :=
    card_narrowSquareQuotientToClassGroup_ker_eq_two_of_mod_four_three
      d hd p hp4 hker
  have hcard_linear : Nat.card (narrowSquareQuotientLinearMap d).ker = 2 := by
    simpa [narrowSquareQuotientLinearMap, narrowSquareQuotientToClassGroup,
      squareQuotientLinearMap] using hcard_group
  apply Nat.pow_right_injective (a := 2) (by norm_num)
  calc
    2 ^ Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker =
        Nat.card (narrowSquareQuotientLinearMap d).ker := by
      simpa using (Module.natCard_eq_pow_finrank
        (K := ZMod 2) (V := (narrowSquareQuotientLinearMap d).ker)).symm
    _ = 2 := hcard_linear
    _ = 2 ^ 1 := by norm_num

/-- The ordinary 2-rank plus the dimension of the correction kernel is `t - 1`. -/
theorem twoRank_classGroup_add_correction_eq_ramifiedPrimeCount_sub_one :
    ClassGroup.twoRank OK +
        Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker =
      ramifiedPrimeCount d - 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank := (narrowSquareQuotientLinearMap d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (narrowSquareQuotientLinearMap_surjective d),
    finrank_top] at hrank
  calc
    ClassGroup.twoRank OK +
          Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker =
        NarrowClassGroup.twoRank OK := by
      simpa [ClassGroup.twoRank, NarrowClassGroup.twoRank, CommGroup.twoRank] using hrank
    _ = ramifiedPrimeCount d - 1 :=
      twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one d

/-- Emerton item 12, unchanged-rank case: if the discriminant has no prime
divisor congruent to `3` modulo `4`, the ordinary and narrow 2-ranks agree. -/
theorem twoRank_classGroup_eq_ramifiedPrimeCount_sub_one_of_no_prime_mod_four_three
    (hdisc : ¬ DiscriminantHasPrimeModFourThree d) :
    ClassGroup.twoRank OK = ramifiedPrimeCount d - 1 := by
  have hmain := twoRank_classGroup_add_correction_eq_ramifiedPrimeCount_sub_one d
  rw [narrowSquareQuotientLinearMap_ker_eq_bot_of_no_prime_mod_four_three d hdisc,
    finrank_bot, add_zero] at hmain
  exact hmain

/-- Emerton items 8(e), 9, and 12: a norm-`-1` unit makes the narrow and
ordinary class groups coincide and leaves the ordinary 2-rank equal to
`t - 1`. -/
theorem twoRank_classGroup_eq_ramifiedPrimeCount_sub_one_of_unit_algebraNorm_eq_neg_one
    (ε : OKˣ) (hε : Algebra.norm ℤ (ε : OK) = -1) :
    ClassGroup.twoRank OK = ramifiedPrimeCount d - 1 :=
  twoRank_classGroup_eq_ramifiedPrimeCount_sub_one_of_no_prime_mod_four_three d
    (not_discriminantHasPrimeModFourThree_of_unit_algebraNorm_eq_neg_one d ε hε)

/-- Emerton items 8(d) and 12, rank-drop case: a norm-`1` fundamental unit and
a discriminant prime congruent to `3` modulo `4` make the ordinary 2-rank
equal to `t - 2`. -/
theorem twoRank_classGroup_eq_ramifiedPrimeCount_sub_two_of_fundamentalUnit_norm_one
    (hd : 0 < d) (ε : OKˣ) (hεfund : Units.IsFundamentalUnit ε)
    (hεnorm : Algebra.norm ℤ (ε : OK) = 1)
    (hdisc : DiscriminantHasPrimeModFourThree d) :
    ClassGroup.twoRank OK = ramifiedPrimeCount d - 2 := by
  obtain ⟨p, hp4⟩ := hdisc
  have hker :=
    Qsqrtd.Real.card_narrowToClassGroup_ker_eq_two_of_fundamentalUnit_algebraNorm_eq_one
      d hd ε hεfund hεnorm
  have hcor :=
    finrank_narrowSquareQuotientLinearMap_ker_eq_one_of_mod_four_three
      d hd p hp4 hker
  have hmain := twoRank_classGroup_add_correction_eq_ramifiedPrimeCount_sub_one d
  rw [hcor] at hmain
  omega

/-- Emerton item 12 in its direct comparison form: the ordinary and narrow
2-ranks agree exactly when the discriminant has no prime divisor congruent to
`3` modulo `4`. -/
theorem twoRank_classGroup_eq_twoRank_narrowClassGroup_iff_not_discriminantHasPrimeModFourThree
    (hd : 0 < d) (ε : OKˣ) (hεfund : Units.IsFundamentalUnit ε) :
    ClassGroup.twoRank OK = NarrowClassGroup.twoRank OK ↔
      ¬ DiscriminantHasPrimeModFourThree d := by
  constructor
  · intro hrank hdisc
    have hεnorm : Algebra.norm ℤ (ε : OK) = 1 := by
      rcases Qsqrtd.Real.unit_algebraNorm_eq_one_or_neg_one d ε with hεnorm | hεnorm
      · exact hεnorm
      · exact False.elim
          ((not_discriminantHasPrimeModFourThree_of_unit_algebraNorm_eq_neg_one
            d ε hεnorm) hdisc)
    obtain ⟨p, hp4⟩ := hdisc
    have hker :=
      Qsqrtd.Real.card_narrowToClassGroup_ker_eq_two_of_fundamentalUnit_algebraNorm_eq_one
        d hd ε hεfund hεnorm
    have hcor :=
      finrank_narrowSquareQuotientLinearMap_ker_eq_one_of_mod_four_three
        d hd p hp4 hker
    have hwide := twoRank_classGroup_add_correction_eq_ramifiedPrimeCount_sub_one d
    have hnarrow := twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one d
    rw [hcor] at hwide
    omega
  · intro hdisc
    rw [twoRank_classGroup_eq_ramifiedPrimeCount_sub_one_of_no_prime_mod_four_three
        d hdisc,
      twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one d]

/-- Emerton items 8, 9, and 12 as the three exhaustive real-quadratic cases.

The fourth apparent combination, norm `-1` together with a discriminant prime
congruent to `3` modulo `4`, is impossible. -/
theorem fundamentalUnit_norm_and_discriminant_cases
    (hd : 0 < d) (ε : OKˣ) (hεfund : Units.IsFundamentalUnit ε) :
    (Algebra.norm ℤ (ε : OK) = -1 ∧
        ¬ DiscriminantHasPrimeModFourThree d ∧
        Function.Bijective (Qsqrtd.narrowToClassGroup d) ∧
        ClassGroup.twoRank OK = ramifiedPrimeCount d - 1) ∨
      (Algebra.norm ℤ (ε : OK) = 1 ∧
        DiscriminantHasPrimeModFourThree d ∧
        Nat.card (Qsqrtd.narrowToClassGroup d).ker = 2 ∧
        Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker = 1 ∧
        ClassGroup.twoRank OK = ramifiedPrimeCount d - 2) ∨
      (Algebra.norm ℤ (ε : OK) = 1 ∧
        ¬ DiscriminantHasPrimeModFourThree d ∧
        Nat.card (Qsqrtd.narrowToClassGroup d).ker = 2 ∧
        Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker = 0 ∧
        ClassGroup.twoRank OK = ramifiedPrimeCount d - 1) := by
  rcases Qsqrtd.Real.unit_algebraNorm_eq_one_or_neg_one d ε with hεnorm | hεnorm
  · by_cases hdisc : DiscriminantHasPrimeModFourThree d
    · right
      left
      obtain ⟨p, hp4⟩ := hdisc
      have hker :=
        Qsqrtd.Real.card_narrowToClassGroup_ker_eq_two_of_fundamentalUnit_algebraNorm_eq_one
          d hd ε hεfund hεnorm
      exact ⟨hεnorm, ⟨p, hp4⟩, hker,
        finrank_narrowSquareQuotientLinearMap_ker_eq_one_of_mod_four_three
          d hd p hp4 hker,
        twoRank_classGroup_eq_ramifiedPrimeCount_sub_two_of_fundamentalUnit_norm_one
          d hd ε hεfund hεnorm ⟨p, hp4⟩⟩
    · right
      right
      have hker :=
        Qsqrtd.Real.card_narrowToClassGroup_ker_eq_two_of_fundamentalUnit_algebraNorm_eq_one
          d hd ε hεfund hεnorm
      have hcor :
          Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker = 0 := by
        rw [narrowSquareQuotientLinearMap_ker_eq_bot_of_no_prime_mod_four_three
          d hdisc, finrank_bot]
      exact ⟨hεnorm, hdisc, hker, hcor,
        twoRank_classGroup_eq_ramifiedPrimeCount_sub_one_of_no_prime_mod_four_three
          d hdisc⟩
  · left
    have hdisc :=
      not_discriminantHasPrimeModFourThree_of_unit_algebraNorm_eq_neg_one d ε hεnorm
    exact ⟨hεnorm, hdisc,
      Qsqrtd.Real.narrowToClassGroup_bijective_of_unit_algebraNorm_eq_neg_one
        d hd ε hεnorm,
      twoRank_classGroup_eq_ramifiedPrimeCount_sub_one_of_unit_algebraNorm_eq_neg_one
        d ε hεnorm⟩

/-- The cardinalities of the ordinary square-class group and the correction
kernel multiply to `2 ^ (t - 1)`. -/
theorem card_squareClassGroup_mul_correction_eq_two_pow_sub_one :
    Nat.card (narrowSquareQuotientToClassGroup d).ker *
        Nat.card (squareQuotient (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  have hcard :=
    MonoidHom.nat_card_eq_card_ker_mul_card_of_surjective
      (narrowSquareQuotientToClassGroup d)
      (narrowSquareQuotientToClassGroup_surjective d)
  rw [card_narrowSquareClassGroup_eq_two_pow_sub_one d] at hcard
  exact hcard.symm

end GenusTheory
end ClassGroup
end QuadraticNumberFields
