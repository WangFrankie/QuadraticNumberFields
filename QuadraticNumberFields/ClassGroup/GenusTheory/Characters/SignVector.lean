/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.RamifiedPrimes

/-!
# Admissible Genus Sign Vectors

This file defines sign vectors indexed by ramified rational primes and the
product-one subgroup that is the target of the genus-character map.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- Vectors of nonzero signs `±1`, represented by `ℤˣ` and indexed by the
ramified rational primes of `ℚ(√d)`. -/
abbrev GenusSignVector :=
  RamifiedPrimeIndex d → ℤˣ

/-- The product of the coordinates of a genus sign vector. -/
noncomputable def genusSignProduct : GenusSignVector d →* ℤˣ where
  toFun ε := ∏ p, ε p
  map_one' := by simp
  map_mul' ε η := by simp [Finset.prod_mul_distrib]

/-- The subgroup of genus sign vectors whose coordinate product is one. -/
noncomputable def admissibleGenusSignVectors :
    Subgroup (GenusSignVector d) :=
  MonoidHom.ker (genusSignProduct d)

/-- The type of genus sign vectors whose coordinate product is one. -/
abbrev AdmissibleGenusSignVector : Type :=
  admissibleGenusSignVectors d

/-- Membership in the admissible subgroup is the product-one condition. -/
theorem mem_admissibleGenusSignVectors_iff (ε : GenusSignVector d) :
    ε ∈ admissibleGenusSignVectors d ↔ ∏ p, ε p = 1 :=
  Iff.rfl

private theorem genusSignProduct_surjective :
    Function.Surjective (genusSignProduct d) := by
  classical
  have hcard : 0 < Fintype.card (RamifiedPrimeIndex d) := by
    rw [fintype_card_ramifiedPrimeIndex]
    exact one_le_ramifiedPrimeCount d
  let p : RamifiedPrimeIndex d := Classical.choice (Fintype.card_pos_iff.mp hcard)
  intro u
  refine ⟨fun q ↦ if q = p then u else 1, ?_⟩
  simp [genusSignProduct, p]

private theorem card_genusSignVector :
    Nat.card (GenusSignVector d) = 2 ^ ramifiedPrimeCount d := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [GenusSignVector, Fintype.card_units_int, ramifiedPrimeCount_eq_card]

/-- There are `2 ^ (t - 1)` admissible sign vectors, where `t` is the number
of ramified rational primes. -/
theorem card_admissibleGenusSignVector :
    Nat.card (AdmissibleGenusSignVector d) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  have hcard := MonoidHom.nat_card_eq_card_ker_mul_card_of_surjective
    (genusSignProduct d) (genusSignProduct_surjective d)
  have hfull := card_genusSignVector d
  have hunits : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  change Nat.card (GenusSignVector d) =
    Nat.card (AdmissibleGenusSignVector d) * Nat.card ℤˣ at hcard
  rw [hfull, hunits] at hcard
  have hpow :
      2 ^ ramifiedPrimeCount d = 2 ^ (ramifiedPrimeCount d - 1) * 2 :=
    (Nat.two_pow_pred_mul_two (one_le_ramifiedPrimeCount d)).symm
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) (hcard.symm.trans hpow)

end GenusTheory
end ClassGroup
end QuadraticNumberFields
