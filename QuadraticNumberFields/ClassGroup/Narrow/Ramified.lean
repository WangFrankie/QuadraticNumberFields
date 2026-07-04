/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.ClassGroup.Narrow
import QuadraticNumberFields.ClassGroup.GenusTheory.Discriminant
import QuadraticNumberFields.ClassGroup.Narrow.Ambiguous
import QuadraticNumberFields.Splitting.Qsqrtd.Discriminant
import QuadraticNumberFields.Splitting.Qsqrtd.Factorization

/-!
# Ramified-Prime Boundary for Strict Two-Torsion

This file keeps the narrow item-11 layer independent of the ordinary genus
formula. It states the strict two-torsion cardinality target and the
ramified-prime generation API for the ideal-arithmetic proof.

p ramified
⇒ (p) O K = P²
⇒ [P]⁺² = [(p)]⁺ = 1
⇒ [P]⁺ ∈ Cl⁺(K)[2]

-/

open scoped NumberField nonZeroDivisors
open scoped QuadraticNumberFields.Splitting

open Ideal FractionalIdeal

namespace QuadraticNumberFields
namespace ClassGroup
namespace Narrow

section Qsqrtd

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞 (Qsqrtd (d : ℚ))

/-- A chosen prime ideal over a ramified rational prime. -/
noncomputable def ramifiedPrimeIdealOfIsRamified
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) : Ideal OK :=
  (Splitting.exists_primeOver_map_eq_sq_of_isRamifiedIn d p hr).choose

/-- The chosen ramified prime lies over `(p)`. -/
theorem ramifiedPrimeIdealOfIsRamified_mem_primesOver
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) :
    ramifiedPrimeIdealOfIsRamified d p hr ∈ Ideal.primesOver (𝔭(p)) OK :=
  (Splitting.exists_primeOver_map_eq_sq_of_isRamifiedIn d p hr).choose_spec.1

/-- The factorization `(p) = P²` for the chosen ramified prime. -/
theorem map_eq_sq_ramifiedPrimeIdealOfIsRamified
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) :
    Ideal.map (algebraMap ℤ OK) (𝔭(p)) =
      ramifiedPrimeIdealOfIsRamified d p hr ^ 2 :=
  (Splitting.exists_primeOver_map_eq_sq_of_isRamifiedIn d p hr).choose_spec.2

/-- The chosen ramified prime ideal is nonzero. -/
theorem ramifiedPrimeIdealOfIsRamified_ne_bot
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) :
    ramifiedPrimeIdealOfIsRamified d p hr ≠ ⊥ := by
  have hpbot : 𝔭(p) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  exact Ideal.ne_bot_of_mem_primesOver hpbot
    (ramifiedPrimeIdealOfIsRamified_mem_primesOver d p hr)

/-- The strict/narrow class of a chosen ramified prime ideal. -/
noncomputable def ramifiedPrimeNarrowClassOfIsRamified
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) :
    NarrowClassGroup OK :=
  NarrowClassGroup.mk0
    ⟨ramifiedPrimeIdealOfIsRamified d p hr,
      mem_nonZeroDivisors_iff_ne_zero.mpr (ramifiedPrimeIdealOfIsRamified_ne_bot d p hr)⟩

/-- The strict/narrow class of a ramified prime ideal is two-torsion. -/
theorem ramifiedPrimeNarrowClassOfIsRamified_mem_twoTorsion
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) :
    ramifiedPrimeNarrowClassOfIsRamified d p hr ∈
      NarrowClassGroup.twoTorsion OK := by
  rw [NarrowClassGroup.mem_twoTorsion_iff]
  let P0 : (Ideal OK)⁰ :=
    ⟨ramifiedPrimeIdealOfIsRamified d p hr,
      mem_nonZeroDivisors_iff_ne_zero.mpr (ramifiedPrimeIdealOfIsRamified_ne_bot d p hr)⟩
  have hpR_ne : (p : OK) ≠ 0 := by
    change algebraMap ℤ OK (p : ℤ) ≠ 0
    exact (FaithfulSMul.algebraMap_injective ℤ OK).ne (by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have hspan : Ideal.map (algebraMap ℤ OK) (𝔭(p)) =
      Ideal.span ({(p : OK)} : Set OK) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hP0_sq : (P0 ^ 2 : (Ideal OK)⁰) =
      ⟨Ideal.span ({(p : OK)} : Set OK), by
        rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
          Ideal.span_singleton_eq_bot]
        exact hpR_ne⟩ := by
    apply Subtype.ext
    exact (map_eq_sq_ramifiedPrimeIdealOfIsRamified d p hr).symm.trans hspan
  change (NarrowClassGroup.mk0 P0) ^ 2 = 1
  rw [← map_pow, hP0_sq]
  exact NarrowClassGroup.mk0_span_singleton_eq_one_of_isTotallyPositive hpR_ne
    (NarrowClassGroup.isTotallyPositive_natCast_fractionRing p
      (Fact.out : Nat.Prime p).pos)

/-- The index type for all rational primes dividing the field discriminant.

This is the ramified-prime index relevant to the item-11 cardinality
`primeDiscriminantFactorCount d`; it includes the prime `2` when it ramifies. -/
abbrev PrimeDiscriminantIndex :=
  {p : ℕ // p ∈ (RingOfIntegers.discrFormula d).natAbs.primeFactors}

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
/-- Members of `PrimeDiscriminantIndex` are rational primes. -/
theorem prime_of_mem_PrimeDiscriminantIndex (p : PrimeDiscriminantIndex d) :
    p.1.Prime :=
  Nat.prime_of_mem_primeFactors p.2

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
/-- Members of `PrimeDiscriminantIndex` divide the closed field discriminant. -/
theorem dvd_discr_of_mem_PrimeDiscriminantIndex (p : PrimeDiscriminantIndex d) :
    (p.1 : ℤ) ∣ RingOfIntegers.discrFormula d := by
  have hmem := Nat.mem_primeFactors.mp p.2
  rw [← Int.dvd_natAbs]
  exact_mod_cast hmem.2.1

/-- Members of `PrimeDiscriminantIndex` are ramified in `𝓞(ℚ(√d))`. -/
theorem isRamified_of_mem_PrimeDiscriminantIndex (p : PrimeDiscriminantIndex d) :
    Ideal.IsRamifiedIn (𝔭(p.1)) OK := by
  letI : Fact p.1.Prime := ⟨prime_of_mem_PrimeDiscriminantIndex d p⟩
  refine (QuadraticNumberFields.Splitting.isRamified_iff_dvd_disc d p.1).mpr ?_
  rw [QuadraticNumberFields.RingOfIntegers.discr_formula d]
  exact dvd_discr_of_mem_PrimeDiscriminantIndex d p

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
/-- The number of `PrimeDiscriminantIndex` terms is the genus-theory parameter `t`. -/
theorem fintype_card_PrimeDiscriminantIndex :
    Fintype.card (PrimeDiscriminantIndex d) = primeDiscriminantFactorCount d := by
  simp [PrimeDiscriminantIndex, primeDiscriminantFactorCount]

/-- The current discriminant-prime index is the prime-factor index of the field
discriminant. -/
theorem mem_PrimeDiscriminantIndex_iff_fieldDiscriminantPrimeFactor (p : ℕ) :
    p ∈ (RingOfIntegers.discrFormula d).natAbs.primeFactors ↔
      p ∈ (NumberField.discr (Qsqrtd (d : ℚ))).natAbs.primeFactors := by
  rw [QuadraticNumberFields.RingOfIntegers.discr_formula d]

/-- The concrete strict/narrow class of the ramified prime indexed by a
discriminant prime divisor. -/
noncomputable def primeDiscriminantStrictClass (p : PrimeDiscriminantIndex d) :
    NarrowClassGroup OK := by
  classical
  letI : Fact p.1.Prime := ⟨prime_of_mem_PrimeDiscriminantIndex d p⟩
  exact ramifiedPrimeNarrowClassOfIsRamified d p.1
    (isRamified_of_mem_PrimeDiscriminantIndex d p)

/-- Each discriminant-prime strict class is two-torsion. -/
theorem primeDiscriminantStrictClass_mem_twoTorsion (p : PrimeDiscriminantIndex d) :
    primeDiscriminantStrictClass d p ∈ NarrowClassGroup.twoTorsion OK := by
  classical
  letI : Fact p.1.Prime := ⟨prime_of_mem_PrimeDiscriminantIndex d p⟩
  simpa [primeDiscriminantStrictClass] using
    ramifiedPrimeNarrowClassOfIsRamified_mem_twoTorsion d p.1
      (isRamified_of_mem_PrimeDiscriminantIndex d p)

end Qsqrtd

end Narrow
end ClassGroup
end QuadraticNumberFields
