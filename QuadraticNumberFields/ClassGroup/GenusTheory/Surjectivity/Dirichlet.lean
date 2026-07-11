/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Map
import QuadraticNumberFields.ClassGroup.GenusTheory.Surjectivity.Residues

/-!
# Surjectivity Of The Genus Character Map

This file lifts prescribed local genus signs from a CRT residue to a rational
prime. For an admissible sign vector, the product-one relation makes that prime
split in the quadratic field, producing a narrow ideal class with the prescribed
genus characters.
-/

open scoped NumberField nonZeroDivisors QuadraticNumberFields.ClassGroup

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- Every genus sign vector is realized by a rational prime. Admissibility is
not needed until the splitting step. -/
theorem exists_prime_for_genusSignVector (ε : GenusSignVector d) :
    ∃ q : ℕ, q.Prime ∧
      ∀ p : RamifiedPrimeIndex d,
        kroneckerSymNat (primeDiscriminantFactor d p) q = (ε p : ℤ) := by
  rcases exists_residue_for_genusSignVector d ε with ⟨a, ha_coprime, ha_symbols⟩
  rcases Nat.forall_exists_prime_gt_and_modEq 0
      (primeDiscriminantModulus_ne_zero d) ha_coprime with
    ⟨q, _, hq_prime, hq_mod⟩
  refine ⟨q, hq_prime, ?_⟩
  intro p
  exact (kroneckerSymNat_eq_of_modEq
    (primeDiscriminantFactor_emod_four_eq_zero_or_one d p)
    (natAbs_primeDiscriminantFactor_dvd_primeDiscriminantModulus d p) hq_mod).trans
      (ha_symbols p)

/-- The genus-character map from the narrow class group onto the admissible sign
vectors is surjective. -/
theorem genusCharacterMap_surjective :
    Function.Surjective (genusCharacterMap d) := by
  classical
  intro ε
  rcases exists_prime_for_genusSignVector d (ε : GenusSignVector d) with
    ⟨q, hq_prime, hq_symbols⟩
  letI : Fact q.Prime := ⟨hq_prime⟩
  have hq_ne : q ≠ 0 := hq_prime.ne_zero
  have hprod_units : ∏ p, (ε : GenusSignVector d) p = 1 :=
    (mem_admissibleGenusSignVectors_iff d (ε : GenusSignVector d)).mp ε.property
  have hprod_int : ∏ p, ((ε : GenusSignVector d) p : ℤ) = 1 := by
    simpa [Units.coe_prod] using congrArg ((↑) : ℤˣ → ℤ) hprod_units
  have hq_discr :
      kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ))) q = 1 := by
    rw [← prod_primeDiscriminantFactor_eq_discr d,
      kroneckerSymNat_prod_left Finset.univ (primeDiscriminantFactor d) hq_ne]
    calc
      ∏ p, kroneckerSymNat (primeDiscriminantFactor d p) q =
          ∏ p, ((ε : GenusSignVector d) p : ℤ) :=
        Finset.prod_congr rfl fun p _ ↦ hq_symbols p
      _ = 1 := hprod_int
  let qIdeal : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hsplit : Ideal.IsSplitIn qIdeal OK := by
    dsimp [qIdeal]
    exact (Splitting.isSplit_iff_kroneckerSymNat_discr_eq_one d q).mpr hq_discr
  let P : qIdeal.primesOver OK :=
    Classical.choice (inferInstance : Nonempty (qIdeal.primesOver OK))
  have hP_norm : Ideal.absNorm (P.1 : Ideal OK) = q :=
    Splitting.absNorm_eq_prime_of_liesOver_of_isSplitIn d q hsplit
  have hq_coprime : q.Coprime (primeDiscriminantModulus d) := by
    rw [primeDiscriminantModulus, Nat.coprime_prod_right_iff]
    intro p _
    by_contra hp_coprime
    have hzero : kroneckerSymNat (primeDiscriminantFactor d p) q = 0 :=
      kroneckerSymNat_eq_zero_of_not_coprime _ (by
        simpa [Nat.Coprime] using hp_coprime)
    have hnonzero : kroneckerSymNat (primeDiscriminantFactor d p) q ≠ 0 := by
      rw [hq_symbols p]
      exact ((ε : GenusSignVector d) p).ne_zero
    exact hnonzero hzero
  have hq_bot : qIdeal ≠ ⊥ := by
    dsimp [qIdeal]
    rw [Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hq_prime.ne_zero
  have hP_bot : (P.1 : Ideal OK) ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver hq_bot P.property
  let I0 : (Ideal OK)⁰ :=
    ⟨P.1, by
      apply mem_nonZeroDivisors_iff_ne_zero.mpr
      simpa [Ideal.zero_eq_bot] using hP_bot⟩
  let I : GenusCoprimeIdeal d :=
    ⟨I0, by
      change Nat.Coprime (Ideal.absNorm (P.1 : Ideal OK))
        (primeDiscriminantModulus d)
      rw [hP_norm]
      exact hq_coprime⟩
  refine ⟨narrowMk0OnGenusCoprimeIdeals d I, ?_⟩
  ext p
  rw [genusCharacterMap_apply, genusCharacter_apply_mk0, rawGenusCharacter_val, hP_norm]
  exact hq_symbols p

end GenusTheory
end ClassGroup
end QuadraticNumberFields
