/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.Recovery

/-!
# Ambiguous-Ideal Upper Bound

This file uses the ramified-parity recovery layer to inject inversion-fixed
narrow classes into erased ramified parity vectors.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

/-- A nonzero kernel vector in the full ramified-parity map lets one coordinate be
erased in the count of inversion-fixed narrow classes. -/
theorem card_narrowInversionFixedClass_le_two_pow_sub_one_of_mem_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker) :
    Nat.card (NarrowInversionFixedClass
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let encode : NarrowInversionFixedClass R →
      ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) :=
    narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrker
  have hencode_injective : Function.Injective encode :=
    narrowInversionFixedClassRamifiedParityVector_injective d hp0 r hrp0 hrker
  haveI : Finite (NarrowInversionFixedClass R) :=
    Finite.of_injective encode hencode_injective
  calc
    Nat.card (NarrowInversionFixedClass R) ≤
        Nat.card ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) :=
      Nat.card_le_card_of_injective encode hencode_injective
    _ = 2 ^ (ramifiedPrimeCount d - 1) :=
      card_erasedRamifiedParityVectorDomain d hp0

/-- Inversion-fixed narrow classes are bounded by the genus-formula value
`2 ^ (t - 1)`. -/
theorem card_narrowInversionFixedClass_le_two_pow_sub_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowInversionFixedClass
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  obtain ⟨r, hnonzero, hrker⟩ :=
    exists_nonzero_fullRamifiedParityNarrowClassHom_ker d
  obtain ⟨p0, hrp0⟩ := hnonzero
  exact card_narrowInversionFixedClass_le_two_pow_sub_one_of_mem_ker
    d p0.2 r hrp0 hrker

/-- Ambiguous-ideal upper bound: the two-torsion in the narrow class group has
size at most `2 ^ (t - 1)`, where `t` is the number of ramified rational primes. -/
theorem card_narrowClassGroupTwoTorsion_le_two_pow_sub_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_narrowClassGroupTwoTorsion_eq_card_narrowInversionFixedClass]
  exact card_narrowInversionFixedClass_le_two_pow_sub_one d

/-- Equivalent upper bound for the narrow square-class quotient. -/
theorem card_narrowClassGroupSquareQuotient_le_two_pow_sub_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_narrowClassGroupSquareQuotient_eq_card_narrowClassGroupTwoTorsion]
  exact card_narrowClassGroupTwoTorsion_le_two_pow_sub_one d

end Internal

/-- Ambiguous-ideal upper bound: the two-torsion in the narrow class group has
size at most `2 ^ (t - 1)`, where `t` is the number of ramified rational primes. -/
theorem card_narrowClassGroupTwoTorsion_le_two_pow_sub_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  rw [Internal.card_narrowClassGroupTwoTorsion_eq_card_narrowInversionFixedClass]
  exact Internal.card_narrowInversionFixedClass_le_two_pow_sub_one d

/-- Equivalent upper bound for the narrow square-class quotient. -/
theorem card_narrowClassGroupSquareQuotient_le_two_pow_sub_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_narrowClassGroupSquareQuotient_eq_card_narrowClassGroupTwoTorsion]
  exact card_narrowClassGroupTwoTorsion_le_two_pow_sub_one d

end GenusTheory
end ClassGroup
end QuadraticNumberFields
