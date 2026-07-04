/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.ClassGroup.Narrow
import QuadraticNumberFields.ClassGroup.Ambiguous.Basic
import QuadraticNumberFields.ClassGroup.RamifiedPrimes
import QuadraticNumberFields.Splitting.Qsqrtd.Factorization
import QuadraticNumberFields.Splitting.Qsqrtd.SqrtD

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
namespace Ambiguous

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
    exact Splitting.pIdeal_ne_bot (Fact.out : Nat.Prime p)
  exact Ideal.ne_bot_of_mem_primesOver hpbot
    (ramifiedPrimeIdealOfIsRamified_mem_primesOver d p hr)

/-- The narrow class of a chosen ramified prime ideal. -/
noncomputable def ramifiedPrimeNarrowClassOfIsRamified
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) :
    NarrowClassGroup OK :=
  NarrowClassGroup.mk0
    ⟨ramifiedPrimeIdealOfIsRamified d p hr,
      mem_nonZeroDivisors_iff_ne_zero.mpr (ramifiedPrimeIdealOfIsRamified_ne_bot d p hr)⟩

/-- The narrow class of a ramified prime ideal is two-torsion. -/
theorem ramifiedPrimeNarrowClassOfIsRamified_mem_twoTorsion
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) :
    ramifiedPrimeNarrowClassOfIsRamified d p hr ∈
      NarrowClassGroup.twoTorsion OK := by
  rw [NarrowClassGroup.mem_twoTorsion_iff]
  let P0 : (Ideal OK)⁰ :=
    ⟨ramifiedPrimeIdealOfIsRamified d p hr,
      mem_nonZeroDivisors_iff_ne_zero.mpr (ramifiedPrimeIdealOfIsRamified_ne_bot d p hr)⟩
  have hspan : Ideal.map (algebraMap ℤ OK) (𝔭(p)) =
      Ideal.span ({(p : OK)} : Set OK) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hP0_sq : (P0 ^ 2 : (Ideal OK)⁰) =
      Splitting.natCastSpanNonzeroIdeal d p (Fact.out : Nat.Prime p) := by
    apply Subtype.ext
    exact (map_eq_sq_ramifiedPrimeIdealOfIsRamified d p hr).symm.trans hspan
  change (NarrowClassGroup.mk0 P0) ^ 2 = 1
  rw [← map_pow, hP0_sq]
  exact NarrowClassGroup.mk0_span_singleton_eq_one_of_isTotallyPositive
    (Splitting.natCast_ne_zero_ringOfIntegers d (Fact.out : Nat.Prime p))
    (NarrowClassGroup.isTotallyPositive_natCast_fractionRing p
      (Fact.out : Nat.Prime p).pos)

/-- The concrete narrow class of an indexed ramified rational prime. -/
noncomputable def ramifiedPrimeNarrowClass (p : RamifiedPrimeIndex d) :
    NarrowClassGroup OK := by
  classical
  letI : Fact p.1.Prime := ⟨prime_of_mem_ramifiedPrimeIndex d p⟩
  exact ramifiedPrimeNarrowClassOfIsRamified d p.1
    (isRamified_of_mem_ramifiedPrimeIndex d p)

/-- Each indexed ramified-prime narrow class is two-torsion. -/
theorem ramifiedPrimeNarrowClass_mem_twoTorsion (p : RamifiedPrimeIndex d) :
    ramifiedPrimeNarrowClass d p ∈ NarrowClassGroup.twoTorsion OK := by
  classical
  letI : Fact p.1.Prime := ⟨prime_of_mem_ramifiedPrimeIndex d p⟩
  simpa [ramifiedPrimeNarrowClass] using
    ramifiedPrimeNarrowClassOfIsRamified_mem_twoTorsion d p.1
      (isRamified_of_mem_ramifiedPrimeIndex d p)

end Qsqrtd

end Ambiguous
end ClassGroup
end QuadraticNumberFields
