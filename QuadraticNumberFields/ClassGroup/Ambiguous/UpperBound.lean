/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.Ambiguous.Relation.Kernel
import QuadraticNumberFields.ClassGroup.Ambiguous.Representatives.IntegralClearing

/-!
# Upper Bound for Strict Two-Torsion

This file proves the upper bound for the strict two-torsion subgroup of the
narrow class group. The arithmetic input is isolated as nontriviality of the
kernel of the full ramified-parity homomorphism. The representative-level
inclusion into the ramified-parity range is imported from
`Representatives.IntegralClearing`.

This is an upper-bound consequence, not the full exact genus formula.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped NumberField

section Qsqrtd

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

private theorem card_narrowClassGroupTwoTorsion_le_two_pow_sub_one_of_ker_ne_bot
    (hker : (fullRamifiedParityNarrowClassHom d).ker ≠ ⊥) :
    Nat.card (NarrowClassGroup.twoTorsion OK) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  let φ := fullRamifiedParityNarrowClassHom d
  have hcover :
      Nat.card (NarrowClassGroup.twoTorsion OK) ≤ Nat.card φ.range :=
    Nat.card_le_card_of_injective
      (fun C : NarrowClassGroup.twoTorsion OK =>
        ⟨(C : NarrowClassGroup OK),
          twoTorsion_le_fullRamifiedParityNarrowClassHom_range d C.2⟩)
      (fun _ _ hCD =>
        Subtype.ext (congrArg (fun x : φ.range => (x : NarrowClassGroup OK)) hCD))
  have hdomain :
      Nat.card (Multiplicative (RamifiedParityVector d)) =
        2 ^ ramifiedPrimeCount d := by
    rw [Nat.card_eq_fintype_card]
    simp [RamifiedParityVector, RamifiedPrimeIndex, ramifiedPrimeCount]
  have hhalf : 2 * Nat.card φ.range ≤ 2 ^ ramifiedPrimeCount d := by
    simpa [hdomain] using MonoidHom.two_mul_card_range_le φ hker
  have htpos : 0 < ramifiedPrimeCount d := by
    have h2le : 2 ≤ 2 ^ ramifiedPrimeCount d :=
      (Nat.mul_le_mul_left 2
        (Nat.succ_le_of_lt Nat.card_pos : 1 ≤ Nat.card φ.range)).trans hhalf
    by_contra ht
    have ht0 : ramifiedPrimeCount d = 0 := by omega
    rw [ht0, pow_zero] at h2le
    omega
  have hpow :
      2 ^ ramifiedPrimeCount d =
        2 * 2 ^ (ramifiedPrimeCount d - 1) := by
    conv_lhs =>
      rw [(by omega : ramifiedPrimeCount d = (ramifiedPrimeCount d - 1) + 1), pow_succ']
  have hrange_le : Nat.card φ.range ≤ 2 ^ (ramifiedPrimeCount d - 1) := by
    rw [hpow] at hhalf
    exact Nat.le_of_mul_le_mul_left hhalf (by decide)
  exact hcover.trans hrange_le

/-- Weak upper bound for the strict two-torsion subgroup of the narrow class
group of `ℚ(√d)`: its cardinality is at most
`2 ^ (ramifiedPrimeCount d - 1)`. -/
theorem card_narrowClassGroupTwoTorsion_le_two_pow_sub_one :
    Nat.card (NarrowClassGroup.twoTorsion OK) ≤
      2 ^ (ramifiedPrimeCount d - 1) :=
  card_narrowClassGroupTwoTorsion_le_two_pow_sub_one_of_ker_ne_bot d
    (fullRamifiedParityNarrowClassHom_ker_ne_bot d)

end Qsqrtd

end Ambiguous
end ClassGroup
end QuadraticNumberFields
