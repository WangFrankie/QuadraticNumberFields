/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Galois Theory

Material destined for mathlib.
-/

/-- If `S` is a quadratic extension of `R`, then the fraction field of `S` is a
quadratic extension of the fraction field of `R`. -/
-- Repository use: `Splitting/Defs.lean` uses this in the `(e, f, g)` trichotomy;
-- `Mathlib/NumberTheory/RamificationInertia/Galois.lean` uses it to build the
-- fraction-field Galois bridge.
theorem Algebra.IsQuadraticExtension.fractionRing
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra R K] [Algebra S L] [Algebra R L] [Algebra K L]
    [IsDomain R] [IsDomain S] [IsFractionRing R K] [IsFractionRing S L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsQuadraticExtension R S] :
    Algebra.IsQuadraticExtension K L := by
  letI : Algebra.IsAlgebraic R S := Algebra.IsAlgebraic.of_finite R S
  refine ⟨?_⟩
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (R := R) (R' := K) (S := S)
    (S' := L)).trans (Algebra.IsQuadraticExtension.finrank_eq_two R S)

/-- If `K` is a quadratic extension of a field `F` of characteristic not equal to
`2`, then `K/F` is separable. -/
-- Repository use: `Splitting/Defs.lean` uses this in the `(e, f, g)` trichotomy;
-- `Mathlib/NumberTheory/RamificationInertia/Galois.lean` uses it to build the
-- fraction-field Galois bridge.
theorem Algebra.IsQuadraticExtension.isSeparable_of_field_of_char_ne_two
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsQuadraticExtension F K]
    (hchar : ringChar F ≠ 2) : Algebra.IsSeparable F K := by
  rw [isSeparable_iff_finInsepDegree_eq_one]
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow (F := F) (E := K) (q := ringExpChar F)
  have hdiv : Field.finInsepDegree F K ∣ 2 := by
    refine ⟨Field.finSepDegree F K, ?_⟩
    rw [Nat.mul_comm, Field.finSepDegree_mul_finInsepDegree,
      Algebra.IsQuadraticExtension.finrank_eq_two F K]
  rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
  · exact h1
  · have hexp : ringExpChar F ≠ 2 := by
      rw [ringExpChar]
      intro h
      omega
    rw [hn] at h2
    cases n with
    | zero => simp at h2
    | succ n =>
        rcases (Nat.dvd_prime Nat.prime_two).1 ⟨(ringExpChar F) ^ n,
          by simpa [pow_succ, Nat.mul_comm] using h2.symm⟩ with hq1 | hq2
        · simp [hq1] at h2
        · exact (hexp hq2).elim
