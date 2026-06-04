/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Defs
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic
import QuadraticNumberFields.QuadraticField.RingOfIntegers

/-!
# Kummer-Dedekind Plumbing for `Qsqrtd`

This file packages the common bridge between Kummer-Dedekind factor data for the
monogenic generator `θ(d)` and the numerical `e/f/g` splitting predicates in
`𝓞(ℚ(√d))`.
-/

attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal
open Polynomial

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- `𝓞(d)`, `𝔭(p)`, `θ(d)` are shared scoped notation.
local notation3 "e(" p ")" => ramificationIdxIn (𝔭(p)) 𝓞(d)
local notation3 "f(" p ")" => inertiaDegIn (𝔭(p)) 𝓞(d)
local notation3 "g(" p ")" => (primesOver (𝔭(p)) 𝓞(d)).ncard
local notation3 "M(" p ")" => RingOfIntegers.monicFactorsMod θ(d) p

/-- In `𝓞(ℚ(√d))`, `e = f = 1` is equivalent to two primes above `(p)`. -/
theorem ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two
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

/-- Kummer-Dedekind identifies primes above `(p)` with monic factors of the reduced
minimal polynomial of `θ(d)`. -/
theorem primesOver_ncard_eq_monicFactorsMod_card (p : ℕ) [Fact p.Prime] :
    g(p) = (M(p)).card := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := Qsqrtd (d : ℚ)) (θ := ringOfIntegersGenerator d)
    (not_dvd_exponent_generator d p)
  simpa using Set.ncard_congr' e

/-- If the monic-factor set `M(p)` is a singleton `{poly}`, then the unique prime
above `(p)` has inertia degree `poly.natDegree`. -/
theorem inertiaDegIn_eq_natDegree_of_monicFactorsMod_eq_singleton
    (p : ℕ) [Fact p.Prime] {poly : (ZMod p)[X]} (hM : M(p) = {poly}) :
    f(p) = poly.natDegree := by
  have hg1 : g(p) = 1 := by
    rw [primesOver_ncard_eq_monicFactorsMod_card d p, hM]; simp
  obtain ⟨P, hPset⟩ := Set.ncard_eq_one.mp hg1
  have hPmem : P ∈ primesOver (𝔭(p)) 𝓞(d) := by rw [hPset]; exact Set.mem_singleton P
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
  have hfac_deg : (QQ : (ZMod p)[X]).natDegree = poly.natDegree := by
    have hmempoly : (QQ : (ZMod p)[X]) ∈ ({poly} : Finset _) := by rw [← hM]; exact QQ.2
    rw [Finset.mem_singleton.mp hmempoly]
  rw [Ideal.inertiaDegIn_eq_inertiaDeg_of_primesOver_eq_singleton (𝔭(p)) 𝓞(d) hPset,
    hkey, hfac_deg]

/-- If `M(p)` has two factors, then `(p)` splits. -/
theorem isSplitIn_of_monicFactorsMod_card_eq_two
    (p : ℕ) [Fact p.Prime] (hM : (M(p)).card = 2) :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) := by
  have hg : g(p) = 2 := by
    rw [primesOver_ncard_eq_monicFactorsMod_card d p, hM]
  exact (ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p).mpr hg

end Splitting
end QuadraticNumberFields
