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
-/
attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal
open Polynomial
open UniqueFactorizationMonoid

namespace QuadraticNumberFields

namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation3 "𝓞d" => 𝓞 (Qsqrtd (d : ℚ))
local notation3 "𝔭(" p ")" => Ideal.span ({(p : ℤ)} : Set ℤ)
local notation3 "e(" p ")" => ramificationIdxIn (𝔭(p)) 𝓞d
local notation3 "f(" p ")" => inertiaDegIn (𝔭(p)) 𝓞d
local notation3 "g(" p ")" => (primesOver (𝔭(p)) 𝓞d).ncard
local notation3 "θd" => ringOfIntegersGenerator d
local notation3 "M(" p ")" => RingOfIntegers.monicFactorsMod θd p

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
    (p := 𝔭(p)) (S := 𝓞d) hchar hbot]
  constructor
  · rintro ⟨hg, _, _⟩
    exact hg
  · intro hg
    rcases Ideal.efg_trichotomy (p := 𝔭(p)) (S := 𝓞d) hchar hbot with h | h | h
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
    Ideal.IsSplitIn (𝔭(p)) 𝓞d ↔ legendreSym p d = 1 := by
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
    Ideal.IsSplitIn (𝔭(p)) 𝓞d ↔ legendreSym p d = 1 := by
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
    Ideal.IsSplitIn (𝔭(p)) 𝓞d ↔ legendreSym p d = 1 := by
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
  obtain ⟨poly, hMpoly, hpolydeg⟩ :=
    monicFactorsMod_eq_singleton_of_legendre_eq_neg_one d p hpd hleg
  -- Unique prime above `(p)`.
  have hg1 : g(p) = 1 := by
    rw [primesOver_ncard_eq_monicFactorsMod_card d p, hMpoly]; simp
  obtain ⟨P, hPset⟩ := Set.ncard_eq_one.mp hg1
  have hPmem : P ∈ primesOver (𝔭(p)) 𝓞d := by rw [hPset]; exact Set.mem_singleton P
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
  have hcoe : ((eqv.symm QQ : ↥(primesOver (𝔭(p)) 𝓞d)) : Ideal 𝓞d) = P := by
    rw [hQQ, Equiv.symm_apply_apply]
  rw [hcoe] at hkey
  -- The factor's degree is `2`.
  have hfac_deg : (QQ : (ZMod p)[X]).natDegree = 2 := by
    have hmempoly : (QQ : (ZMod p)[X]) ∈ ({poly} : Finset _) := by rw [← hMpoly]; exact QQ.2
    rw [Finset.mem_singleton.mp hmempoly]; exact hpolydeg
  -- Assemble: f(p) = inertiaDeg = natDegree QQ = 2.
  rw [Ideal.inertiaDegIn_eq_inertiaDeg_of_primesOver_eq_singleton (𝔭(p)) 𝓞d hPset, hkey, hfac_deg]

theorem isInert_iff_legendreSym_eq_neg_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    Ideal.IsInertIn (𝔭(p)) 𝓞d ↔ legendreSym p d = -1 := by
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
    have hnsplit : ¬ Ideal.IsSplitIn (𝔭(p)) 𝓞d := by
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
    rcases Ideal.efg_trichotomy (𝔭(p)) 𝓞d hchar hbot with ⟨_, _, hf⟩ | ⟨hg, he, _⟩ | ⟨_, _, hf⟩
    · omega
    · exact ⟨hg, he⟩
    · omega

-- TODO: p ∣ d → ramified
-- theorem isRamified_of_dvd
--     (p : ℕ) [Fact p.Prime] (hpd : (p : ℤ) ∣ d) :
--     1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) := ...



/-- For a squarefree `d ≠ 1` and any prime `p`, the ideal `(p)` in `𝓞(ℚ(√d))`
satisfies one of the numerical split, inert, or ramified conditions. -/
theorem split_or_inert_or_ramified (p : ℕ) [Fact p.Prime] :
    Ideal.IsSplitIn (𝔭(p)) 𝓞d ∨ Ideal.IsInertIn (𝔭(p)) 𝓞d ∨
    Ideal.IsRamifiedIn (𝔭(p)) 𝓞d := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.split_or_inert_or_ramified (𝔭(p)) 𝓞d hchar hbot

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
