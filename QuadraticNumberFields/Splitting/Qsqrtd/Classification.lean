/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Defs
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic
import QuadraticNumberFields.Splitting.MinpolyMod
import QuadraticNumberFields.QuadraticField.RingOfIntegers

/-!
# Prime Splitting Classification for `Qsqrtd` via the Legendre Symbol

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

## Reference

K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Chapter 13, §1. The odd-prime classification is Proposition 13.1.3 (`(δ_F/p) = 1` split,
`-1` inert, `0` ramified) and the `p = 2` classification is Proposition 13.1.4
(`d ≡ 1 (8)` split, `d ≡ 5 (8)` inert, `d ≡ 2, 3 (4)` ramified).
-/
attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal
open Polynomial
open UniqueFactorizationMonoid

namespace QuadraticNumberFields

namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- `𝓞(d)`, `𝔭(p)`, `θ(d)` are shared `scoped` notation from `Splitting.Qsqrtd.Monogenic`.
-- The numerical invariants `e/f/g` and the monic-factor set `M` are file-local specialisations.
local notation3 "e(" p ")" => ramificationIdxIn (𝔭(p)) 𝓞(d)
local notation3 "f(" p ")" => inertiaDegIn (𝔭(p)) 𝓞(d)
local notation3 "g(" p ")" => (primesOver (𝔭(p)) 𝓞(d)).ncard
local notation3 "M(" p ")" => RingOfIntegers.monicFactorsMod θ(d) p

/-! ## Odd primes, p ∤ d -/

/-! ## Basic trichotomy for `𝓞(ℚ(√d))` -/

private lemma ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two
    (p : ℕ) [Fact p.Prime] :
    e(p) = 1 ∧ f(p) = 1 ↔ g(p) = 2 := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  rw [Ideal.ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg
    (p := 𝔭(p)) (S := 𝓞(d)) hchar hbot]
  constructor
  · rintro ⟨hg, _, _⟩
    exact hg
  · intro hg
    rcases Ideal.efg_trichotomy (p := 𝔭(p)) (S := 𝓞(d)) hchar hbot with h | h | h
    · exact h
    · omega
    · omega

private lemma primesOver_ncard_eq_monicFactorsMod_card (p : ℕ) [Fact p.Prime] :
    g(p) = (M(p)).card := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := Qsqrtd (d : ℚ)) (θ := ringOfIntegersGenerator d)
    (not_dvd_exponent_generator d p)
  simpa using Set.ncard_congr' e

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

/-- Generic Kummer–Dedekind core: if the monic-factor set `M(p)` is a singleton `{poly}`,
then the unique prime above `(p)` has inertia degree `f(p) = poly.natDegree`. This packages
the `g(p)=1` → unique-prime → equiv-extraction argument, reused by both the odd-prime and
`p = 2` classifications. -/
private lemma inertiaDegIn_eq_natDegree_of_monicFactorsMod_eq_singleton
    (p : ℕ) [Fact p.Prime] {poly : (ZMod p)[X]} (hM : M(p) = {poly}) :
    f(p) = poly.natDegree := by
  -- Unique prime above `(p)`.
  have hg1 : g(p) = 1 := by
    rw [primesOver_ncard_eq_monicFactorsMod_card d p, hM]; simp
  obtain ⟨P, hPset⟩ := Set.ncard_eq_one.mp hg1
  have hPmem : P ∈ primesOver (𝔭(p)) 𝓞(d) := by rw [hPset]; exact Set.mem_singleton P
  -- Identify the corresponding monic factor `QQ` via Kummer–Dedekind.
  set eqv := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := Qsqrtd (d : ℚ)) (θ := ringOfIntegersGenerator d)
    (not_dvd_exponent_generator d p) with heqv
  set QQ := eqv ⟨P, hPmem⟩ with hQQ
  have hkey := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (K := Qsqrtd (d : ℚ)) (θ := ringOfIntegersGenerator d) (not_dvd_exponent_generator d p)
    (Q := (QQ : (ZMod p)[X])) QQ.2
  have hQQeta :
      (⟨(QQ : (ZMod p)[X]), QQ.2⟩ :
        RingOfIntegers.monicFactorsMod (ringOfIntegersGenerator d) p) = QQ := rfl
  rw [hQQeta, ← heqv] at hkey
  have hcoe : ((eqv.symm QQ : ↥(primesOver (𝔭(p)) 𝓞(d))) : Ideal 𝓞(d)) = P := by
    rw [hQQ, Equiv.symm_apply_apply]
  rw [hcoe] at hkey
  -- The factor's degree is `poly.natDegree`.
  have hfac_deg : (QQ : (ZMod p)[X]).natDegree = poly.natDegree := by
    have hmempoly : (QQ : (ZMod p)[X]) ∈ ({poly} : Finset _) := by rw [← hM]; exact QQ.2
    rw [Finset.mem_singleton.mp hmempoly]
  -- Assemble: f(p) = inertiaDeg = natDegree QQ = poly.natDegree.
  rw [Ideal.inertiaDegIn_eq_inertiaDeg_of_primesOver_eq_singleton (𝔭(p)) 𝓞(d) hPset, hkey, hfac_deg]

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

/-! ## The prime `p = 2`

The Legendre symbol is undefined at `2`, so we factor `minpoly ℤ θ` mod `2` by hand.
Everything reduces to computing `M(2)` as a concrete `Finset` over `𝔽₂`, then feeding it to
the same generic plumbing as the odd case:

* `d % 4 ≠ 1`  : `minpoly ≡ (X - d̄)²` (Frobenius)  ⟹ `M(2) = {linear}`     ⟹ ramified
* `d % 8 = 1`  : `minpoly ≡ X(X+1)`                 ⟹ `M(2).card = 2`        ⟹ split
* `d % 8 = 5`  : `minpoly ≡ X² + X + 1` irreducible ⟹ `M(2) = {quadratic}`  ⟹ inert

Key obstruction vs. the odd case: over `𝔽₂` you cannot divide by `2`, so the
`normalizedFactors_X_sq_sub_X_sub_C_*` lemmas (which use `(1 ± r)/2`) do **not** apply.
Use the Frobenius identity `X² - C a = (X - C a)²` (since `ā² = ā` and `2 = 0`) instead.

Reference: Ireland & Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Proposition 13.1.4. -/

/-- Generic split criterion: if `M(p)` has two factors, then `(p)` splits. -/
private lemma isSplitIn_of_monicFactorsMod_card_eq_two
    (p : ℕ) [Fact p.Prime] (hM : (M(p)).card = 2) :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) := by
  have hg : g(p) = 2 := by
    rw [primesOver_ncard_eq_monicFactorsMod_card d p, hM]
  exact (ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p).mpr hg

/-- **(ramified, `d % 4 ≠ 1`)** `minpoly ≡ (X - d̄)²` mod `2`, a single linear factor. -/
private lemma monicFactorsMod_two_eq_singleton_linear (hd4 : d % 4 ≠ 1) :
    ∃ poly : (ZMod 2)[X], M(2) = {poly} ∧ poly.natDegree = 1 := by
  refine ⟨X - C (d : ZMod 2), ?_, ?_⟩
  · -- M(2)={X-d̄}
    have hmin :
        M(2) = (normalizedFactors ((X ^ 2 - C (d : ZMod 2)) : (ZMod 2)[X])).toFinset := by
      simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).1 hd4]
    have hfrobenius : (X ^ 2 - C (d : ZMod 2) : (ZMod 2)[X]) = (X - C (d : ZMod 2)) ^ 2 := by
        rw [sub_eq_add_neg X,add_pow_char,sub_eq_add_neg,add_left_cancel_iff]
        simp only [← C_pow,ZMod.pow_card,ZModModule.neg_eq_self]
    have hirr := irreducible_X_sub_C (d : ZMod 2)
    rw [hmin, hfrobenius, normalizedFactors_pow]
    rw [normalizedFactors_irreducible hirr, (monic_X_sub_C _).normalize_eq_self]
    simp
  · -- HINT: `natDegree_X_sub_C`.
    exact natDegree_X_sub_C _

/-- **(inert, `d % 8 = 5`)** `minpoly ≡ X² + X + 1` mod `2`, irreducible of degree `2`. -/
private lemma monicFactorsMod_two_eq_singleton_quadratic (hd8 : d % 8 = 5) :
    ∃ poly : (ZMod 2)[X], M(2) = {poly} ∧ poly.natDegree = 2 := by
  -- HINT: `d % 8 = 5 ⟹ d % 4 = 1` (omega), so use `(minpoly_generator d).2`.
  -- HINT: `((d / 4 : ℤ) : ZMod 2) = 1` since `d / 4` is odd (omega on `d % 8 = 5`).
  -- HINT: poly = `X ^ 2 - X - C 1`; prove irreducible by monic-degree-2 + no roots,
  --   mirroring `irreducible_X_sq_sub_X_sub_C_of_not_square_discr` but checking `eval 0`, `eval 1`
  --   directly (both `= 1 ≠ 0`); `ZMod 2` is a `Fintype`, so the root check can be `decide`d.
  -- HINT: then `normalizedFactors_irreducible` + `Monic.normalize_eq_self` +
  --   `Multiset.toFinset_singleton`.
  have : ((X ^ 2 + X + 1 : (ZMod 2)[X]) = (C 1 * X ^ 2 + C 1 * X + C 1:(ZMod 2)[X])) := by
      -- rw [Polynomial.C_mul', Polynomial.C_mul', Polynomial.C_1]
      simp only [Polynomial.C_1, one_mul]
  have deg_eq_two : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by
    exact this ▸ Polynomial.natDegree_quadratic (one_ne_zero : (1 : ZMod 2) ≠ 0)
  refine ⟨X ^ 2 + X + 1, ?_, deg_eq_two⟩
  have hd4: d % 4 = 1 := by omega
    -- d=8*k+5 for some k, so d/4 = 2k + 1 is odd, so (d/4 : ZMod 2) = 1.
  have hmin :
        M(2) =
          (normalizedFactors
            ((X ^ 2 - X - C ((d / 4 : ℤ) : ZMod 2)) : (ZMod 2)[X])).toFinset := by
      simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).2 hd4]
  have hd4_odd : ((d / 4 : ℤ) : ZMod 2) = 1 := by
      have : (d / 4 : ℤ) % 2 = 1 := by omega
      rw [Odd.intCast_zmod_two]
      exact Int.odd_iff.mpr this
  rw [hd4_odd] at hmin
  simp only [sub_eq_add_neg, ZModModule.neg_eq_self, Polynomial.C_1] at hmin
  have hmon : (X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by
    simpa [sub_eq_add_neg, ZModModule.neg_eq_self, Polynomial.C_1, one_mul] using
      (Polynomial.isMonicOfDegree_sub_add_two
        (R := ZMod 2) (1 : ZMod 2) (1 : ZMod 2)).monic
  have hmd : Polynomial.IsMonicOfDegree (X ^ 2 + X + 1 : (ZMod 2)[X]) 2 := by
    simpa [sub_eq_add_neg, ZModModule.neg_eq_self, Polynomial.C_1, one_mul] using
      (Polynomial.isMonicOfDegree_sub_add_two
        (R := ZMod 2) (1 : ZMod 2) (1 : ZMod 2))
  have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three hmd.natDegree_eq.ge
      (by rw [hmd.natDegree_eq]; norm_num)]
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hxroot : (X ^ 2 + X + 1 : (ZMod 2)[X]).eval x = 0 :=
      (mem_roots hmon.ne_zero).mp hx
    fin_cases x <;> norm_num at hxroot <;> contradiction
  rw [hmin, normalizedFactors_irreducible hirr, hmon.normalize_eq_self,
    Multiset.toFinset_singleton]
/-- **(split, `d % 8 = 1`)** `minpoly ≡ X(X+1)` mod `2`, two distinct linear factors. -/
private lemma monicFactorsMod_two_card_eq_two (hd8 : d % 8 = 1) :
    (M(2)).card = 2 := by
  -- HINT: `(minpoly_generator d).2` with `((d / 4 : ℤ) : ZMod 2) = 0` (d/4 even from `d % 8 = 1`).
  -- HINT: poly = `X ^ 2 - X = X * (X - 1)` (by `ring`); both factors irreducible & distinct.
  --   Mirror `normalizedFactors_X_sq_sub_C_sq_card_eq_two`'s `Finset.card_insert_of_notMem` ending.
  sorry

/-- `(2)` ramifies in `𝓞(ℚ(√d))` when `d ≢ 1 (mod 4)`. -/
theorem isRamified_two_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    Ideal.IsRamifiedIn (𝔭(2)) 𝓞(d) := by
  -- HINT: `obtain ⟨poly, hM, hdeg⟩ := monicFactorsMod_two_eq_singleton_linear d hd4`.
  -- HINT: `f(2) = 1` via `inertiaDegIn_eq_natDegree_of_monicFactorsMod_eq_singleton d 2 hM` + hdeg.
  -- HINT: `g(2) = 1` via `primesOver_ncard_eq_monicFactorsMod_card d 2` + hM.
  -- HINT: `rcases Ideal.efg_trichotomy (𝔭(2)) 𝓞(d) ?hchar ?hbot` (cf. `isInert_iff` for the
  --   `hchar`/`hbot`); `g = 1` kills split, `f = 1` kills inert, leaving `1 < e(2)`.
  sorry

/-- `(2)` is inert in `𝓞(ℚ(√d))` when `d ≡ 5 (mod 8)`. -/
theorem isInert_two_of_mod_eight_eq_five (hd8 : d % 8 = 5) :
    Ideal.IsInertIn (𝔭(2)) 𝓞(d) := by
  -- HINT: `obtain ⟨poly, hM, hdeg⟩ := monicFactorsMod_two_eq_singleton_quadratic d hd8`.
  -- HINT: `f(2) = 2`, then `rcases efg_trichotomy ...` pins `(1, 1, 2)` as in `isInert_iff`.
  sorry

/-- `(2)` splits in `𝓞(ℚ(√d))` when `d ≡ 1 (mod 8)`. -/
theorem isSplit_two_of_mod_eight_eq_one (hd8 : d % 8 = 1) :
    Ideal.IsSplitIn (𝔭(2)) 𝓞(d) :=
  isSplitIn_of_monicFactorsMod_card_eq_two d 2 (monicFactorsMod_two_card_eq_two d hd8)

-- TODO: p ∣ d → ramified
-- theorem isRamified_of_dvd
--     (p : ℕ) [Fact p.Prime] (hpd : (p : ℤ) ∣ d) :
--     1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) := ...



/-- For a squarefree `d ≠ 1` and any prime `p`, the ideal `(p)` in `𝓞(ℚ(√d))`
satisfies one of the numerical split, inert, or ramified conditions. -/
theorem split_or_inert_or_ramified (p : ℕ) [Fact p.Prime] :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) ∨ Ideal.IsInertIn (𝔭(p)) 𝓞(d) ∨
    Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.split_or_inert_or_ramified (𝔭(p)) 𝓞(d) hchar hbot

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
