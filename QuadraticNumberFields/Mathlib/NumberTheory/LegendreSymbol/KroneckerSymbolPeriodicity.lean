/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import QuadraticNumberFields.Mathlib.NumberTheory.LegendreSymbol.KroneckerSymbol

/-!
# Periodicity, Multiplicativity, and Vanishing for the Kronecker Symbol

Material destined for mathlib.

This file collects the three arithmetic lemmas needed to package `kroneckerSymNat`
as a `MulChar` on `ZMod D.natAbs`:

* `kroneckerSymNat_add_natAbs_eq` (Shim A): periodicity modulo `|D|`, conditional
  on `D % 4 ∈ {0, 1}`.
* `kroneckerSymNat_mul` (Shim B): full multiplicativity in the lower argument
  for nonzero inputs.
* `kroneckerSymNat_eq_zero_of_not_coprime` (Shim C): the symbol vanishes whenever
  the lower argument shares a prime factor with `D.natAbs`.

All three shims depend only on
`QuadraticNumberFields.Mathlib.NumberTheory.LegendreSymbol.KroneckerSymbol` and
mathlib; they are project-quadratic-field-independent.
-/

namespace QuadraticNumberFields

/-- A nonzero natural number split into its 2-adic valuation and odd part evaluates
under `kroneckerSymNat` as the product of the supplementary value at `2` (raised to
the 2-adic valuation) and the Jacobi symbol at the odd part. -/
private lemma kroneckerSymNat_two_pow_mul_odd (D : ℤ) (k : ℕ) {m : ℕ} (hm : Odd m) :
    kroneckerSymNat D (2 ^ k * m) = kroneckerTwo D ^ k * jacobiSym D m := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hmn0 : 2 ^ k * m ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide)) hm0
  have h2 : (2 : ℕ).Prime := Nat.prime_two
  have hfact : (2 ^ k * m).factorization 2 = k := by
    rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) hm0]
    simp [Nat.factorization_pow, Nat.Prime.factorization_self h2,
      Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat hm)]
  rw [kroneckerSymNat, if_neg hmn0, hfact]
  congr 1
  rw [Nat.mul_div_cancel_left m (pow_pos (by decide : (0 : ℕ) < 2) k)]

/-- Periodicity of the Kronecker symbol modulo `|D|`, valid for every integer
discriminant `D` with `D % 4 ∈ {0, 1}`. -/
theorem kroneckerSymNat_add_natAbs_eq (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] (n : ℕ) :
    kroneckerSymNat D (n + D.natAbs) = kroneckerSymNat D n := by
  sorry

/-- Full multiplicativity of the Kronecker symbol in the lower (natural) argument,
for nonzero inputs. -/
theorem kroneckerSymNat_mul (D : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    kroneckerSymNat D (m * n) = kroneckerSymNat D m * kroneckerSymNat D n := by
  obtain ⟨km, m', hm', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  obtain ⟨kn, n', hn', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm'n' : Odd (m' * n') := hm'.mul hn'
  have hm'0 : m' ≠ 0 := hm'.pos.ne'
  have hn'0 : n' ≠ 0 := hn'.pos.ne'
  -- LHS: (2^km * m') * (2^kn * n') = 2^(km+kn) * (m' * n')
  have hreorg : 2 ^ km * m' * (2 ^ kn * n') = 2 ^ (km + kn) * (m' * n') := by
    rw [pow_add]; ring
  rw [hreorg, kroneckerSymNat_two_pow_mul_odd D (km + kn) hm'n',
    kroneckerSymNat_two_pow_mul_odd D km hm',
    kroneckerSymNat_two_pow_mul_odd D kn hn',
    jacobiSym.mul_right' _ hm'0 hn'0, pow_add]
  ring

/-- The Kronecker symbol vanishes whenever the natural denominator shares a prime
factor with `D.natAbs`. -/
theorem kroneckerSymNat_eq_zero_of_not_coprime (D : ℤ) {n : ℕ}
    (h : Nat.gcd n D.natAbs ≠ 1) : kroneckerSymNat D n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hD : D.natAbs ≠ 1 := by simpa using h
    simp [kroneckerSymNat, hD]
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    rw [kroneckerSymNat_two_pow_mul_odd D k hm]
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h
    have hpn : p ∣ 2 ^ k * m := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpD : p ∣ D.natAbs := hpdvd.trans (Nat.gcd_dvd_right _ _)
    rcases hp.eq_two_or_odd' with rfl | hp_odd
    · -- p = 2: 2 ∣ D.natAbs so D is even, kroneckerTwo D = 0
      have h2D_int : (2 : ℤ) ∣ D :=
        (Int.natCast_dvd (m := 2) (n := D)).mpr (by exact_mod_cast hpD)
      have hDeven : D % 2 = 0 := Int.emod_eq_zero_of_dvd h2D_int
      have hkTwo : kroneckerTwo D = 0 := (kroneckerTwo_eq_zero_iff D).mpr hDeven
      have hk_pos : 0 < k := by
        by_contra hk0
        have hk_eq : k = 0 := by omega
        subst hk_eq
        simp only [pow_zero, one_mul] at hpn
        exact hm.not_two_dvd_nat hpn
      rw [hkTwo, zero_pow hk_pos.ne', zero_mul]
    · -- p odd: p ∣ m and p ∣ D.natAbs, so gcd(D.natAbs, m) ≥ p, so jacobiSym D m = 0
      have hpm : p ∣ m := by
        rcases (Nat.Prime.dvd_mul hp).mp hpn with h2k | hm_p
        · exfalso
          have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2k
          have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
          subst hpeq
          exact absurd hp_odd (by decide)
        · exact hm_p
      have hgcd : Int.gcd D m ≠ 1 := by
        have hp_dvd_gcd : p ∣ Nat.gcd D.natAbs m := Nat.dvd_gcd hpD hpm
        intro hgcd_eq_one
        have hgcd_nat : D.natAbs.gcd m = 1 := by
          have h := hgcd_eq_one
          simp only [Int.gcd, Int.natAbs_natCast] at h
          exact h
        rw [hgcd_nat] at hp_dvd_gcd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hp_dvd_gcd)
      have hm_ne : m ≠ 0 := hm.pos.ne'
      have : NeZero m := ⟨hm_ne⟩
      have hjac0 : jacobiSym D m = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr hgcd
      rw [hjac0, mul_zero]

end QuadraticNumberFields
