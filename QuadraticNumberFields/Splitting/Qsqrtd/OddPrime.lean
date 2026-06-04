/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Qsqrtd.KummerDedekind
import QuadraticNumberFields.Splitting.MinpolyMod

/-!
# Odd-Prime Splitting Classification for `Qsqrtd`

This file proves the odd-prime part of the splitting classification for
`𝓞(ℚ(√d))`.

## Main Results

### Odd primes (p ≠ 2, p ∤ d)

* `isSplit_iff_legendreSym_eq_one`: `(p)` splits ↔ `legendreSym p d = 1`
* `isInert_iff_legendreSym_eq_neg_one`: `(p)` is inert ↔ `legendreSym p d = -1`
* `isRamified_of_odd_dvd`: `p ∣ d` → `(p)` ramifies

## Proof Strategy

```
Classification.lean (𝓞 = ℤ[θ])
         |
Monogenic.lean (exponent θ = 1)
         |
primesOverSpanEquivMonicFactorsMod   ← Kummer-Dedekind from mathlib
         |
monicFactorsMod θ p
= irreducible factors of minpoly ℤ θ mod p
         |
MinpolyMod.lean (X² - d mod p)
         |
legendreSym p d                      ← from mathlib
```

## Reference

K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Chapter 13, §1. The odd-prime classification is Proposition 13.1.3 (`(δ_F/p) = 1` split,
`-1` inert, `0` ramified).
-/
attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal
open Polynomial
open UniqueFactorizationMonoid

namespace QuadraticNumberFields

namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- `𝔭(p)` is shared from `Splitting.Defs`; `𝓞(d)` and `θ(d)` are shared from
-- `Splitting.Qsqrtd.Monogenic`.
-- The numerical invariants `e/f/g` and the monic-factor set `M` are file-local specialisations.
local notation3 "e(" p ")" => ramificationIdxIn (𝔭(p)) 𝓞(d)
local notation3 "f(" p ")" => inertiaDegIn (𝔭(p)) 𝓞(d)
local notation3 "g(" p ")" => (primesOver (𝔭(p)) 𝓞(d)).ncard
local notation3 "M(" p ")" => RingOfIntegers.monicFactorsMod θ(d) p

/-! ## Odd primes, p ∤ d -/

/-- Odd-prime split criterion in the `ℤ[√d]` branch of the ring of integers. -/
theorem isSplit_iff_legendreSym_eq_one_of_mod_four_ne_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) (hd4 : d % 4 ≠ 1) :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) ↔ legendreSym p d = 1 := by
  change e(p) = 1 ∧ f(p) = 1 ↔ legendreSym p d = 1
  rw [ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p,
    primesOver_ncard_eq_monicFactorsMod_card d p]
  have hmin :
      M(p) =
        (normalizedFactors ((X ^ 2 - C (d : ZMod p)) : (ZMod p)[X])).toFinset := by
    simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).1 hd4]
  rw [hmin]
  constructor
  · intro hcard
    by_contra hleg
    have hcard_one :=
      normalizedFactors_X_sq_sub_C_card_eq_one_of_legendre_ne_one d p hpd hleg
    omega
  · intro hleg
    exact normalizedFactors_X_sq_sub_C_card_eq_two_of_legendre_eq_one d p hp hpd hleg

/-- Odd-prime split criterion in the `ℤ[(1+√d)/2]` branch of the ring of integers. -/
theorem isSplit_iff_legendreSym_eq_one_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) (hd4 : d % 4 = 1) :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) ↔ legendreSym p d = 1 := by
  change e(p) = 1 ∧ f(p) = 1 ↔ legendreSym p d = 1
  rw [ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p,
    primesOver_ncard_eq_monicFactorsMod_card d p]
  have hmin :
      M(p) =
        (normalizedFactors ((X ^ 2 - X - C ((d / 4 : ℤ) : ZMod p)) : (ZMod p)[X])).toFinset := by
    simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).2 hd4]
  rw [hmin]
  constructor
  · intro hcard
    by_contra hleg
    have hcard_one :=
      normalizedFactors_X_sq_sub_X_sub_C_card_eq_one_of_legendre_ne_one d p hpd
        (show d = 1 + 4 * (d / 4) by omega) hleg
    omega
  · intro hleg
    exact normalizedFactors_X_sq_sub_X_sub_C_card_eq_two_of_legendre_eq_one d p hp hpd
      (show d = 1 + 4 * (d / 4) by omega) hleg


theorem isSplit_iff_legendreSym_eq_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) ↔ legendreSym p d = 1 := by
  by_cases hd4 : d % 4 = 1
  · exact isSplit_iff_legendreSym_eq_one_of_mod_four_eq_one d p hp hpd hd4
  · exact isSplit_iff_legendreSym_eq_one_of_mod_four_ne_one d p hp hpd hd4

/-- When `legendreSym p d = -1`, the minimal polynomial mod `p` is irreducible, so the
monic-factor set `M(p)` is a singleton whose element has degree `2`. -/
private lemma monicFactorsMod_eq_singleton_of_legendre_eq_neg_one
    (p : ℕ) [Fact p.Prime] (hpd : ¬ (p : ℤ) ∣ d) (hleg : legendreSym p d = -1) :
    ∃ poly : (ZMod p)[X], M(p) = {poly} ∧ poly.natDegree = 2 := by
  have hpd0 : (d : ZMod p) ≠ 0 := fun h => hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h)
  have hnsq : ¬ IsSquare (d : ZMod p) := (legendreSym.eq_neg_one_iff p).mp hleg
  by_cases hd4 : d % 4 = 1
  · refine ⟨X ^ 2 - X - C ((d / 4 : ℤ) : ZMod p), ?_, ?_⟩
    · have hmin :
          M(p) =
            (normalizedFactors
              ((X ^ 2 - X - C ((d / 4 : ℤ) : ZMod p)) : (ZMod p)[X])).toFinset := by
        simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).2 hd4]
      have hdint : (d : ℤ) = 1 + 4 * (d / 4) := by omega
      have hcast : (d : ZMod p) = 1 + 4 * ((d / 4 : ℤ) : ZMod p) :=
        calc (d : ZMod p) = ((1 + 4 * (d / 4) : ℤ) : ZMod p) := by rw [← hdint]
          _ = 1 + 4 * ((d / 4 : ℤ) : ZMod p) := by push_cast; ring
      have hnsq' : ¬ IsSquare ((1 : ZMod p) + 4 * ((d / 4 : ℤ) : ZMod p)) := hcast ▸ hnsq
      have hirr : Irreducible (X ^ 2 - X - C ((d / 4 : ℤ) : ZMod p) : (ZMod p)[X]) :=
        irreducible_X_sq_sub_X_sub_C_of_not_square_discr p hnsq'
      have hmon : (X ^ 2 - X - C ((d / 4 : ℤ) : ZMod p) : (ZMod p)[X]).Monic := by
        simpa [sub_eq_add_neg, one_mul] using
          (Polynomial.isMonicOfDegree_sub_add_two
            (R := ZMod p) (1 : ZMod p) (-(d / 4 : ℤ) : ZMod p)).monic
      rw [hmin, normalizedFactors_irreducible hirr, hmon.normalize_eq_self,
        Multiset.toFinset_singleton]
    · have hmd :
          Polynomial.IsMonicOfDegree
            (X ^ 2 - X - C ((d / 4 : ℤ) : ZMod p) : (ZMod p)[X]) 2 := by
        simpa [sub_eq_add_neg, one_mul] using
          (Polynomial.isMonicOfDegree_sub_add_two
            (R := ZMod p) (1 : ZMod p) (-(d / 4 : ℤ) : ZMod p))
      exact hmd.natDegree_eq
  · refine ⟨X ^ 2 - C (d : ZMod p), ?_, ?_⟩
    · have hmin :
          M(p) = (normalizedFactors ((X ^ 2 - C (d : ZMod p)) : (ZMod p)[X])).toFinset := by
        simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).1 hd4]
      have hirr : Irreducible (X ^ 2 - C (d : ZMod p) : (ZMod p)[X]) :=
        (sq_sub_C_irreducible_iff_not_isSquare (d : ZMod p)).mpr hnsq
      have hmon : (X ^ 2 - C (d : ZMod p) : (ZMod p)[X]).Monic := monic_X_pow_sub_C _ two_ne_zero
      rw [hmin, normalizedFactors_irreducible hirr, hmon.normalize_eq_self,
        Multiset.toFinset_singleton]
    · exact natDegree_X_pow_sub_C

/-- For an odd prime `p ∤ d`, the uniform inertia degree of `(p)` in `𝓞(ℚ(√d))` equals `2`
exactly when `legendreSym p d = -1` (the inert case). -/
private lemma inertiaDegIn_eq_two_of_legendre_eq_neg_one
    (p : ℕ) [Fact p.Prime] (hpd : ¬ (p : ℤ) ∣ d) (hleg : legendreSym p d = -1) :
    f(p) = 2 := by
  obtain ⟨poly, hM, hdeg⟩ :=
    monicFactorsMod_eq_singleton_of_legendre_eq_neg_one d p hpd hleg
  rw [inertiaDegIn_eq_natDegree_of_monicFactorsMod_eq_singleton d p hM]; exact hdeg

theorem isInert_iff_legendreSym_eq_neg_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    Ideal.IsInertIn (𝔭(p)) 𝓞(d) ↔ legendreSym p d = -1 := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  have hpd0 : (d : ZMod p) ≠ 0 := fun h => hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h)
  constructor
  · -- Inert excludes split, and `p ∤ d` excludes ramified, leaving `legendreSym = -1`.
    intro hinert
    have hg1 : g(p) = 1 := hinert.1
    have hnsplit : ¬ Ideal.IsSplitIn (𝔭(p)) 𝓞(d) := by
      intro hsplit
      have hg2 : g(p) = 2 :=
        (ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p).mp hsplit
      omega
    have hne1 : legendreSym p d ≠ 1 := fun h =>
      hnsplit ((isSplit_iff_legendreSym_eq_one d p hp hpd).mpr h)
    rcases legendreSym.eq_one_or_neg_one p hpd0 with h | h
    · exact absurd h hne1
    · exact h
  · -- `legendreSym = -1` forces `f(p) = 2`, which pins the inert case of the trichotomy.
    intro hleg
    have hf2 : f(p) = 2 := inertiaDegIn_eq_two_of_legendre_eq_neg_one d p hpd hleg
    rcases Ideal.efg_trichotomy (𝔭(p)) 𝓞(d) hchar hbot with ⟨_, _, hf⟩ | ⟨hg, he, _⟩ | ⟨_, _, hf⟩
    · omega
    · exact ⟨hg, he⟩
    · omega

/-- If an odd prime divides `d`, the monic-factor set modulo `p` is a singleton whose
factor is linear. -/
private lemma monicFactorsMod_eq_singleton_linear_of_odd_dvd
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : (p : ℤ) ∣ d) :
    ∃ poly : (ZMod p)[X], M(p) = {poly} ∧ poly.natDegree = 1 := by
  have hdzero : (d : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hpd
  by_cases hd4 : d % 4 = 1
  · let k : ZMod p := ((d / 4 : ℤ) : ZMod p)
    refine ⟨X - C ((1 : ZMod p) / 2), ?_, ?_⟩
    · have hmin :
          M(p) =
            (normalizedFactors
              ((X ^ 2 - X - C ((d / 4 : ℤ) : ZMod p)) : (ZMod p)[X])).toFinset := by
        simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).2 hd4]
      have hdint : (d : ℤ) = 1 + 4 * (d / 4) := by omega
      have hdisc : (1 : ZMod p) + 4 * k = 0 := by
        rw [← hdzero]
        rw [hdint]
        dsimp [k]
        push_cast
        ring
      have hp2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero_of_prime_ne_two p hp
      let a : ZMod p := (1 : ZMod p) / 2
      have hfac :
          (X ^ 2 - X - C k : (ZMod p)[X]) = (X - C a) ^ 2 := by
        have ha : a + a = 1 := by
          dsimp [a]
          field_simp [hp2]
          norm_num
        have hk : k = -(a * a) := by
          dsimp [a]
          field_simp [hp2]
          linear_combination hdisc
        calc
          (X ^ 2 - X - C k : (ZMod p)[X]) =
              X ^ 2 - C (a + a) * X + C (a * a) := by
            rw [ha, hk]
            simp [sub_eq_add_neg]
          _ = (X - C a) ^ 2 := by
            rw [pow_two, map_add, map_mul]
            ring_nf
      change
        M(p) =
          (normalizedFactors ((X ^ 2 - X - C k) : (ZMod p)[X])).toFinset at hmin
      rw [hmin, hfac, normalizedFactors_pow]
      rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C a),
        (Polynomial.monic_X_sub_C a).normalize_eq_self]
      simp [a]
    · exact natDegree_X_sub_C _
  · refine ⟨X, ?_, ?_⟩
    · have hmin :
          M(p) = (normalizedFactors ((X ^ 2 - C (d : ZMod p)) : (ZMod p)[X])).toFinset := by
        simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).1 hd4]
      rw [hdzero] at hmin
      simp only [Polynomial.C_0, sub_zero] at hmin
      rw [hmin, normalizedFactors_pow]
      have hXirr : Irreducible (X : (ZMod p)[X]) := by
        simpa using Polynomial.irreducible_X_sub_C (0 : ZMod p)
      rw [normalizedFactors_irreducible hXirr, Polynomial.monic_X.normalize_eq_self]
      simp
    · exact natDegree_X

/-- If an odd prime `p` divides `d`, then `(p)` ramifies in `𝓞(ℚ(√d))`. -/
theorem isRamified_of_odd_dvd
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : (p : ℤ) ∣ d) :
    Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) := by
  obtain ⟨poly, hM, hdeg⟩ := monicFactorsMod_eq_singleton_linear_of_odd_dvd d p hp hpd
  have hf1 : f(p) = 1 := by
    rw [inertiaDegIn_eq_natDegree_of_monicFactorsMod_eq_singleton d p hM, hdeg]
  have hg1 : g(p) = 1 := by
    rw [primesOver_ncard_eq_monicFactorsMod_card d p, hM]
    simp
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  rcases Ideal.efg_trichotomy (𝔭(p)) 𝓞(d) hchar hbot with
    ⟨hg, _, _⟩ | ⟨_, _, hf⟩ | hram
  · omega
  · omega
  · exact (Ideal.one_lt_ramificationIdxIn_iff_efg (𝔭(p)) 𝓞(d) hchar hbot).mpr hram

end Splitting
end QuadraticNumberFields
