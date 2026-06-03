/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Defs
import QuadraticNumberFields.Splitting.Monogenic
import QuadraticNumberFields.Splitting.MinpolyMod
import QuadraticNumberFields.QuadraticField.RingOfIntegers
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Prime Splitting Classification via the Legendre Symbol

This file proves the main classification theorem: for a squarefree integer `d ≠ 1`
and a prime `p`, the splitting behavior of `(p)` in `𝓞(ℚ(√d))` is determined
by the Legendre symbol `(d/p)`.

## Main Results

### Odd primes (p ≠ 2, p ∤ d)

* `isSplit_iff_legendreSym_eq_one`: `(p)` splits ↔ `legendreSym p d = 1`
* `isInert_iff_legendreSym_eq_neg_one`: `(p)` is inert ↔ `legendreSym p d = -1`
* `isRamified_of_dvd`: `p ∣ d` → `(p)` ramifies

### All primes (unified)

* `splitting_classification`: The complete trichotomy via `legendreSym p d`.

### p = 2

* Handled via `MinpolyMod.splitting_at_two_*` (d mod 4 and d mod 8 case analysis)

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
-/
attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal
open Polynomial
open UniqueFactorizationMonoid

namespace QuadraticNumberFields

namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-! ## Odd primes, p ∤ d -/

private lemma zmod_two_ne_zero_of_prime_ne_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hp (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) (Fact.out : Nat.Prime p).two_le)

private lemma normalizedFactors_X_sq_sub_C_sq_card_eq_two
    (p : ℕ) [Fact p.Prime] {r : ZMod p} (hr : r ≠ 0) (hp2 : (2 : ZMod p) ≠ 0) :
    ((normalizedFactors ((X ^ 2 - C (r * r)) : (ZMod p)[X])).toFinset.card = 2) := by
  have hfac : (X ^ 2 - C (r * r) : (ZMod p)[X]) = (X - C r) * (X + C r) := by
    rw [show r * r = r ^ 2 by rw [pow_two], map_pow]
    ring
  rw [hfac, normalizedFactors_mul]
  · rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C r)]
    rw [show (X + C r : (ZMod p)[X]) = X - C (-r) by simp]
    rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C (-r : ZMod p))]
    simp only [(Polynomial.monic_X_sub_C r).normalize_eq_self,
      (Polynomial.monic_X_sub_C (-r : ZMod p)).normalize_eq_self,
      Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]
      intro h
      have hcoeff := congrArg (fun q : (ZMod p)[X] => q.coeff 0) h
      have hcoeff' : -r = r := by simpa using hcoeff
      have hzero : (2 : ZMod p) * r = 0 := by
        have : r + r = 0 := by
          nth_rw 1 [← hcoeff']
          simp
        simpa [two_mul] using this
      exact hr ((mul_eq_zero.mp hzero).resolve_left hp2)
  · exact (Polynomial.monic_X_sub_C r).ne_zero
  · rw [show (X + C r : (ZMod p)[X]) = X - C (-r) by simp]
    exact (Polynomial.monic_X_sub_C (-r : ZMod p)).ne_zero

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private lemma normalizedFactors_X_sq_sub_C_card_eq_two_of_legendre_eq_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d)
    (hleg : legendreSym p d = 1) :
    ((normalizedFactors ((X ^ 2 - C (d : ZMod p)) : (ZMod p)[X])).toFinset.card = 2) := by
  have hpd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    exact hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd)
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hpd0).mp hleg
  have hr0 : r ≠ 0 := by
    intro hrz
    exact hpd0 (by simpa [hrz] using hr)
  rw [hr]
  exact normalizedFactors_X_sq_sub_C_sq_card_eq_two p hr0
    (zmod_two_ne_zero_of_prime_ne_two p hp)

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private lemma normalizedFactors_X_sq_sub_C_card_eq_one_of_legendre_ne_one
    (p : ℕ) [Fact p.Prime] (hpd : ¬ (p : ℤ) ∣ d) (hleg : legendreSym p d ≠ 1) :
    ((normalizedFactors ((X ^ 2 - C (d : ZMod p)) : (ZMod p)[X])).toFinset.card = 1) := by
  have hpd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    exact hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd)
  have hnsq : ¬ IsSquare (d : ZMod p) := by
    intro hs
    exact hleg ((legendreSym.eq_one_iff p hpd0).mpr hs)
  rw [normalizedFactors_irreducible]
  · simp
  · exact (sq_sub_C_irreducible_iff_not_isSquare (F := ZMod p) (d : ZMod p)).mpr hnsq

private lemma normalizedFactors_X_sq_sub_X_sub_C_card_eq_two_of_square_discr
    (p : ℕ) [Fact p.Prime] {k r : ZMod p} (hr0 : r ≠ 0) (hp2 : (2 : ZMod p) ≠ 0)
    (hr : (1 : ZMod p) + 4 * k = r * r) :
    ((normalizedFactors ((X ^ 2 - X - C k) : (ZMod p)[X])).toFinset.card = 2) := by
  have hfac : (X ^ 2 - X - C k : (ZMod p)[X]) =
      (X - C ((1 + r) / 2)) * (X - C ((1 - r) / 2)) := by
    let a : ZMod p := (1 + r) / 2
    let b : ZMod p := (1 - r) / 2
    have hsum : a + b = 1 := by
      dsimp [a, b]
      field_simp [hp2]
      ring
    have hprod : a * b = -k := by
      dsimp [a, b]
      field_simp [hp2]
      linear_combination hr
    calc
      (X ^ 2 - X - C k : (ZMod p)[X]) = X ^ 2 - C (a + b) * X + C (a * b) := by
        rw [hsum, hprod]
        simp [sub_eq_add_neg]
      _ = (X - C a) * (X - C b) := by
        rw [map_add, map_mul]
        ring_nf
      _ = (X - C ((1 + r) / 2)) * (X - C ((1 - r) / 2)) := by rfl
  rw [hfac, normalizedFactors_mul]
  · rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C ((1 + r) / 2))]
    rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C ((1 - r) / 2))]
    simp only [(Polynomial.monic_X_sub_C ((1 + r) / 2 : ZMod p)).normalize_eq_self,
      (Polynomial.monic_X_sub_C ((1 - r) / 2 : ZMod p)).normalize_eq_self,
      Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]
      intro h
      have hcoeff := congrArg (fun q : (ZMod p)[X] => q.coeff 0) h
      have halpha : ((1 + r) / 2 : ZMod p) = (1 - r) / 2 := by simpa using hcoeff
      have hmul :
          (2 : ZMod p) * ((1 + r) / 2) = (2 : ZMod p) * ((1 - r) / 2) := by
        rw [halpha]
      field_simp [hp2] at hmul
      have htwo : (2 : ZMod p) * r = 0 := by linear_combination hmul
      exact hr0 ((mul_eq_zero.mp htwo).resolve_left hp2)
  · exact (Polynomial.monic_X_sub_C ((1 + r) / 2 : ZMod p)).ne_zero
  · exact (Polynomial.monic_X_sub_C ((1 - r) / 2 : ZMod p)).ne_zero

private lemma irreducible_X_sq_sub_X_sub_C_of_not_square_discr
    (p : ℕ) [Fact p.Prime] {k : ZMod p} (hnsq : ¬ IsSquare ((1 : ZMod p) + 4 * k)) :
    Irreducible (X ^ 2 - X - C k : (ZMod p)[X]) := by
  have hmon : (X ^ 2 - X - C k : (ZMod p)[X]).Monic := by
    simpa [sub_eq_add_neg, one_mul] using
      (Polynomial.isMonicOfDegree_sub_add_two (R := ZMod p) (1 : ZMod p) (-k)).monic
  have hmd : Polynomial.IsMonicOfDegree (X ^ 2 - X - C k : (ZMod p)[X]) 2 := by
    simpa [sub_eq_add_neg, one_mul] using
      (Polynomial.isMonicOfDegree_sub_add_two (R := ZMod p) (1 : ZMod p) (-k))
  rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three hmd.natDegree_eq.ge
    (by rw [hmd.natDegree_eq]; norm_num)]
  · apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hev : (X ^ 2 - X - C k : (ZMod p)[X]).eval x = 0 :=
      (mem_roots hmon.ne_zero).mp hx
    have hquad' : x * x - x - k = 0 := by
      simpa [eval_sub, eval_pow, pow_two] using hev
    have hquad : (1 : ZMod p) * (x * x) + (-1 : ZMod p) * x + (-k) = 0 := by
      linear_combination hquad'
    have hdisc :=
      discrim_eq_sq_of_quadratic_eq_zero (a := (1 : ZMod p)) (b := (-1 : ZMod p))
        (c := -k) hquad
    apply hnsq
    use (2 : ZMod p) * 1 * x + (-1 : ZMod p)
    simpa [discrim, pow_two] using hdisc

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private lemma normalizedFactors_X_sq_sub_X_sub_C_card_eq_two_of_legendre_eq_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) {k : ℤ}
    (hk : d = 1 + 4 * k) (hleg : legendreSym p d = 1) :
    ((normalizedFactors ((X ^ 2 - X - C (k : ZMod p)) : (ZMod p)[X])).toFinset.card = 2) := by
  have hpd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    exact hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd)
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hpd0).mp hleg
  have hr0 : r ≠ 0 := by
    intro hrz
    exact hpd0 (by simpa [hrz] using hr)
  have hdisc : (1 : ZMod p) + 4 * (k : ZMod p) = r * r := by
    rw [← hr]
    norm_num [hk]
  exact normalizedFactors_X_sq_sub_X_sub_C_card_eq_two_of_square_discr p hr0
    (zmod_two_ne_zero_of_prime_ne_two p hp) hdisc

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private lemma normalizedFactors_X_sq_sub_X_sub_C_card_eq_one_of_legendre_ne_one
    (p : ℕ) [Fact p.Prime] (hpd : ¬ (p : ℤ) ∣ d) {k : ℤ} (hk : d = 1 + 4 * k)
    (hleg : legendreSym p d ≠ 1) :
    ((normalizedFactors ((X ^ 2 - X - C (k : ZMod p)) : (ZMod p)[X])).toFinset.card = 1) := by
  have hpd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    exact hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd)
  have hnsq : ¬ IsSquare ((1 : ZMod p) + 4 * (k : ZMod p)) := by
    intro hs
    have hdsq : IsSquare (d : ZMod p) := by
      simpa [hk] using hs
    exact hleg ((legendreSym.eq_one_iff p hpd0).mpr hdsq)
  rw [normalizedFactors_irreducible]
  · simp
  · exact irreducible_X_sq_sub_X_sub_C_of_not_square_discr p hnsq

/-! ## Basic trichotomy for `𝓞(ℚ(√d))` -/

private lemma ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two
    (p : ℕ) [Fact p.Prime] :
    ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ↔
      (primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard = 2 := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  rw [Ideal.ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg
    (p := Ideal.span {(p : ℤ)})
    (S := 𝓞 (Qsqrtd (d : ℚ))) hchar hbot]
  constructor
  · rintro ⟨hg, _, _⟩
    exact hg
  · intro hg
    rcases Ideal.efg_trichotomy (p := Ideal.span {(p : ℤ)})
        (S := 𝓞 (Qsqrtd (d : ℚ))) hchar hbot with h | h | h
    · exact h
    · omega
    · omega

private lemma primesOver_ncard_eq_monicFactorsMod_card (p : ℕ) [Fact p.Prime] :
    (primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard =
      (RingOfIntegers.monicFactorsMod (ringOfIntegersGenerator d) p).card := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := Qsqrtd (d : ℚ)) (θ := ringOfIntegersGenerator d)
    (not_dvd_exponent_generator d p)
  simpa using Set.ncard_congr' e

/-- Odd-prime split criterion in the `ℤ[√d]` branch of the ring of integers. -/
theorem isSplit_iff_legendreSym_eq_one_of_mod_four_ne_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) (hd4 : d % 4 ≠ 1) :
    ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ↔
      legendreSym p d = 1 := by
  rw [ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p,
    primesOver_ncard_eq_monicFactorsMod_card d p]
  have hmin :
      RingOfIntegers.monicFactorsMod (ringOfIntegersGenerator d) p =
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
    ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ↔
      legendreSym p d = 1 := by
  rw [ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p,
    primesOver_ncard_eq_monicFactorsMod_card d p]
  have hmin :
      RingOfIntegers.monicFactorsMod (ringOfIntegersGenerator d) p =
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

-- TODO: split ↔ legendreSym = 1
theorem isSplit_iff_legendreSym_eq_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ↔
      legendreSym p d = 1 := by
  by_cases hd4 : d % 4 = 1
  · exact isSplit_iff_legendreSym_eq_one_of_mod_four_eq_one d p hp hpd hd4
  · exact isSplit_iff_legendreSym_eq_one_of_mod_four_ne_one d p hp hpd hd4

-- TODO: inert ↔ legendreSym = -1
-- theorem isInert_iff_legendreSym_eq_neg_one
--     (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
--     (primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard = 1 ∧
--       ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1
--       ↔ legendreSym p d = -1 := ...

-- TODO: p ∣ d → ramified
-- theorem isRamified_of_dvd
--     (p : ℕ) [Fact p.Prime] (hpd : (p : ℤ) ∣ d) :
--     1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) := ...



/-- For a squarefree `d ≠ 1` and any prime `p`, the ideal `(p)` in `𝓞(ℚ(√d))`
satisfies one of the numerical split, inert, or ramified conditions. -/
theorem split_or_inert_or_ramified (p : ℕ) [Fact p.Prime] :
    (ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
      inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1) ∨
    ((primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard = 1 ∧
      ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1) ∨
    1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.split_or_inert_or_ramified _ _ hchar hbot

/-! ## Unified classification -/

-- TODO: complete trichotomy
-- theorem splitting_classification (p : ℕ) [Fact p.Prime] :
--     ((legendreSym p d = 1  ∧
--        ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
--        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1) ∨
--      (legendreSym p d = -1 ∧
--        (primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard = 1 ∧
--        ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1) ∨
--      (legendreSym p d = 0  ∧
--        1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))))) := ...

end Splitting
end QuadraticNumberFields
