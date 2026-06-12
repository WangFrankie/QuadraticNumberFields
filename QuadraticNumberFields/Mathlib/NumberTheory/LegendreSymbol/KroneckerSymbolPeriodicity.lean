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
* `kroneckerSymNat_mod_natAbs_eq`: reduction of the denominator modulo `|D|`.
* `kroneckerSymNat_mul` (Shim B): full multiplicativity in the lower argument
  for nonzero inputs.
* `kroneckerSymNat_eq_zero_of_not_coprime` (Shim C): the symbol vanishes whenever
  the lower argument shares a prime factor with `D.natAbs`.
* `kroneckerSymNat_natAbs_sub_one_eq_sign`: the value at the representative of
  `-1` in `ZMod D.natAbs`.

All three shims depend only on
`QuadraticNumberFields.Mathlib.NumberTheory.LegendreSymbol.KroneckerSymbol` and
mathlib; they are project-quadratic-field-independent.
-/

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

private lemma kroneckerSymNat_of_odd (D : ℤ) {n : ℕ} (hn : Odd n) :
    kroneckerSymNat D n = jacobiSym D n := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hfact : n.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hn.not_two_dvd_nat
  rw [kroneckerSymNat, if_neg hn0, hfact, pow_zero, one_mul, pow_zero, Nat.div_one]

private lemma odd_natAbs_of_emod_four_eq_one (D : ℤ) (hD : D % 4 = 1) :
    Odd D.natAbs := by
  rcases Int.natAbs_eq D with hpos | hneg
  · have hN4 : D.natAbs % 4 = 1 := by omega
    exact Nat.odd_iff.mpr (by omega)
  · have hN4 : D.natAbs % 4 = 3 := by omega
    exact Nat.odd_iff.mpr (by omega)

private lemma kroneckerTwo_eq_jacobiSym_two_natAbs_of_emod_four_eq_one (D : ℤ)
    (hD : D % 4 = 1) :
    kroneckerTwo D = jacobiSym (2 : ℤ) D.natAbs := by
  have hNodd : Odd D.natAbs := odd_natAbs_of_emod_four_eq_one D hD
  rw [jacobiSym.at_two hNodd]
  rw [ZMod.χ₈_nat_eq_if_mod_eight]
  unfold kroneckerTwo
  split_ifs <;> omega

private lemma jacobiSym_self_eq_natAbs_right_of_emod_four_eq_one (D : ℤ)
    (hD : D % 4 = 1) {m : ℕ} (hm : Odd m) :
    jacobiSym D m = jacobiSym m D.natAbs := by
  rcases Int.natAbs_eq D with hpos | hneg
  · have hN4 : D.natAbs % 4 = 1 := by omega
    rw (occs := .pos [1]) [hpos]
    exact jacobiSym.quadratic_reciprocity_one_mod_four hN4 hm
  · have hN4 : D.natAbs % 4 = 3 := by omega
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
    have hN2 : D.natAbs % 2 = 1 := by omega
    calc
      jacobiSym D m = jacobiSym (-(D.natAbs : ℤ)) m := by
        rw (occs := .pos [1]) [hneg]
      _ = ZMod.χ₄ (m : ZMod 4) * jacobiSym (D.natAbs : ℤ) m := by
        exact jacobiSym.neg (D.natAbs : ℤ) hm
      _ = jacobiSym (m : ℤ) D.natAbs := by
        rcases Nat.odd_mod_four_iff.mp hm2 with hm4 | hm4
        · have hrec :=
            jacobiSym.quadratic_reciprocity_if (a := D.natAbs) (b := m) hN2 hm2
          have hrec' : jacobiSym (D.natAbs : ℤ) m = jacobiSym (m : ℤ) D.natAbs := by
            simpa [hN4, hm4] using hrec.symm
          rw [ZMod.χ₄_nat_one_mod_four hm4, hrec']
          ring
        · have hrec :=
            jacobiSym.quadratic_reciprocity_if (a := D.natAbs) (b := m) hN2 hm2
          have hrec' : jacobiSym (D.natAbs : ℤ) m = -jacobiSym (m : ℤ) D.natAbs := by
            simpa [hN4, hm4] using hrec.symm
          rw [ZMod.χ₄_nat_three_mod_four hm4, hrec']
          ring

private lemma kroneckerSymNat_eq_jacobiSym_natAbs_of_emod_four_eq_one (D : ℤ)
    (hD : D % 4 = 1) (n : ℕ) :
    kroneckerSymNat D n = jacobiSym n D.natAbs := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rcases eq_or_ne D.natAbs 1 with hD1 | hD1
    · simp [kroneckerSymNat, hD1]
    · have hD0 : D.natAbs ≠ 0 := by omega
      have hDgt : 1 < D.natAbs :=
        lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hD0) (Ne.symm hD1)
      rw [kroneckerSymNat, if_pos rfl, if_neg hD1]
      exact (jacobiSym.zero_left hDgt).symm
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
    rw [kroneckerSymNat_two_pow_mul_odd D k hm]
    rw [Nat.cast_mul, jacobiSym.mul_left, Nat.cast_pow, jacobiSym.pow_left]
    have htwoPow : jacobiSym ((2 : ℕ) : ℤ) D.natAbs ^ k = kroneckerTwo D ^ k := by
      exact (congrArg (fun z : ℤ => z ^ k)
        (kroneckerTwo_eq_jacobiSym_two_natAbs_of_emod_four_eq_one D hD)).symm
    rw [htwoPow, ← jacobiSym_self_eq_natAbs_right_of_emod_four_eq_one D hD hm]

private lemma gcd_ne_one_of_two_dvd {m n : ℕ} (hm : 2 ∣ m) (hn : 2 ∣ n) :
    Nat.gcd m n ≠ 1 := by
  intro h
  have h2 : 2 ∣ Nat.gcd m n := Nat.dvd_gcd hm hn
  rw [h] at h2
  norm_num at h2

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

/-- Periodicity of the Kronecker symbol modulo `|D|`, valid for every integer
discriminant `D` with `D % 4 ∈ {0, 1}`. -/
theorem kroneckerSymNat_add_natAbs_eq (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] (n : ℕ) :
    kroneckerSymNat D (n + D.natAbs) = kroneckerSymNat D n := by
  rcases eq_or_ne D.natAbs 0 with hD0 | hD0
  · simp [hD0]
  rcases (show D % 4 = 0 ∨ D % 4 = 1 from Fact.out) with hd4 | hd4
  · have h4D : (4 : ℤ) ∣ D := Int.dvd_of_emod_eq_zero hd4
    have h2Dint : (2 : ℤ) ∣ D := dvd_trans (by norm_num : (2 : ℤ) ∣ 4) h4D
    have h2Dnat : 2 ∣ D.natAbs := (Int.natCast_dvd (n := D) (m := 2)).mp h2Dint
    by_cases hn2 : 2 ∣ n
    · have hsum2 : 2 ∣ n + D.natAbs := dvd_add hn2 h2Dnat
      rw [kroneckerSymNat_eq_zero_of_not_coprime D (gcd_ne_one_of_two_dvd hsum2 h2Dnat),
        kroneckerSymNat_eq_zero_of_not_coprime D (gcd_ne_one_of_two_dvd hn2 h2Dnat)]
    · have hnodd : Odd n := Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
      have hD_even : Even D.natAbs := even_iff_two_dvd.mpr h2Dnat
      have hsumodd : Odd (n + D.natAbs) := hnodd.add_even hD_even
      rw [kroneckerSymNat_of_odd D hsumodd, kroneckerSymNat_of_odd D hnodd]
      obtain ⟨a, rfl⟩ := h4D
      have h4mod : (4 * a) % 4 = 0 := Int.mul_emod_right 4 a
      rw [← jacobiSym.div_four_left h4mod (Nat.odd_iff.mp hsumodd),
        ← jacobiSym.div_four_left h4mod (Nat.odd_iff.mp hnodd)]
      simp only [Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]
      rw [jacobiSym.mod_right a hsumodd, jacobiSym.mod_right a hnodd]
      congr 1
      have hperiod : (4 * a).natAbs = 4 * a.natAbs := by simp [Int.natAbs_mul]
      rw [← hperiod]
      exact Nat.add_mod_right n (4 * a).natAbs
  · rw [kroneckerSymNat_eq_jacobiSym_natAbs_of_emod_four_eq_one D hd4 (n + D.natAbs),
      kroneckerSymNat_eq_jacobiSym_natAbs_of_emod_four_eq_one D hd4 n]
    apply jacobiSym.mod_left'
    rw [Nat.cast_add]
    simpa using (Int.add_mul_emod_self_left (n : ℤ) (D.natAbs : ℤ) 1)

/-- Iterated periodicity of the Kronecker symbol modulo `|D|`. -/
theorem kroneckerSymNat_add_natAbs_mul_eq (D : ℤ)
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (n k : ℕ) :
    kroneckerSymNat D (n + D.natAbs * k) = kroneckerSymNat D n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, kroneckerSymNat_add_natAbs_eq D, ih]

/-- Reducing the lower argument modulo `|D|` preserves the Kronecker symbol. -/
theorem kroneckerSymNat_mod_natAbs_eq (D : ℤ)
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (n : ℕ) :
    kroneckerSymNat D (n % D.natAbs) = kroneckerSymNat D n := by
  conv_rhs => rw [← Nat.mod_add_div n D.natAbs]
  exact (kroneckerSymNat_add_natAbs_mul_eq D (n % D.natAbs) (n / D.natAbs)).symm

/-- Auxiliary computation for the canonical `-1` representative: the denominator
`4 * A - 1` is congruent to `-1` modulo `A`, so it is the natural representative
of `-1` after reducing modulo `4 * A`. -/
private lemma jacobiSym_nat_four_mul_sub_one (A : ℕ) (hA : A ≠ 0) :
    jacobiSym (A : ℤ) (4 * A - 1) = 1 := by
  obtain ⟨k, m, hm, hAeq⟩ := Nat.exists_eq_two_pow_mul_odd hA
  subst hAeq
  have hbodd : Odd (4 * (2 ^ k * m) - 1) := by
    rw [Nat.odd_iff]
    have hpos : 0 < 4 * (2 ^ k * m) := by positivity
    omega
  rw [Nat.cast_mul, jacobiSym.mul_left, Nat.cast_pow, jacobiSym.pow_left]
  have htwoPow : jacobiSym ((2 : ℕ) : ℤ) (4 * (2 ^ k * m) - 1) ^ k = 1 := by
    rcases k with rfl | k
    · simp
    · have hmul : 4 * (2 ^ (k + 1) * m) = 8 * (2 ^ k * m) := by
        rw [pow_succ]
        ring
      have hmod8 : (4 * (2 ^ (k + 1) * m) - 1) % 8 = 7 := by
        rw [hmul]
        have hmpos : 0 < m := hm.pos
        have hpos : 0 < 8 * (2 ^ k * m) := by positivity
        omega
      have htwo : jacobiSym ((2 : ℕ) : ℤ) (4 * (2 ^ (k + 1) * m) - 1) = 1 := by
        have hb2 : (4 * (2 ^ (k + 1) * m) - 1) % 2 = 1 := Nat.odd_iff.mp hbodd
        have hbodd_succ : Odd (4 * (2 ^ (k + 1) * m) - 1) := hbodd
        rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num]
        calc
          jacobiSym (2 : ℤ) (4 * (2 ^ (k + 1) * m) - 1) =
              ZMod.χ₈ ((4 * (2 ^ (k + 1) * m) - 1 : ℕ) : ZMod 8) :=
            jacobiSym.at_two hbodd_succ
          _ = 1 := by
            rw [ZMod.χ₈_nat_eq_if_mod_eight]
            simp [hb2, hmod8]
      rw [htwo, one_pow]
  have hoddpart : jacobiSym (m : ℤ) (4 * (2 ^ k * m) - 1) = 1 := by
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
    have hb2 : (4 * (2 ^ k * m) - 1) % 2 = 1 := Nat.odd_iff.mp hbodd
    have hb4 : (4 * (2 ^ k * m) - 1) % 4 = 3 := by
      have hpos : 0 < 4 * (2 ^ k * m) := by positivity
      omega
    have hmod : ((4 * (2 ^ k * m) - 1 : ℕ) : ℤ) % m = (-1 : ℤ) % m := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      have hdiff :
          ((4 * (2 ^ k * m) - 1 : ℕ) : ℤ) - (-1 : ℤ) =
            4 * ((2 ^ k : ℕ) : ℤ) * (m : ℤ) := by
        have hpos : 0 < 4 * (2 ^ k * m) := by positivity
        rw [Nat.cast_sub (by omega : 1 ≤ 4 * (2 ^ k * m))]
        norm_num
        ring
      rw [hdiff]
      apply Int.emod_eq_zero_of_dvd
      refine ⟨4 * ((2 ^ k : ℕ) : ℤ), by ring⟩
    have hbm :
        jacobiSym ((4 * (2 ^ k * m) - 1 : ℕ) : ℤ) m = jacobiSym (-1 : ℤ) m :=
      jacobiSym.mod_left' hmod
    rw [jacobiSym.at_neg_one hm] at hbm
    rcases Nat.odd_mod_four_iff.mp hm2 with hm4 | hm4
    · have hrec :=
        jacobiSym.quadratic_reciprocity_if (a := m) (b := 4 * (2 ^ k * m) - 1)
          hm2 hb2
      have hrec' : jacobiSym (m : ℤ) (4 * (2 ^ k * m) - 1) =
          jacobiSym ((4 * (2 ^ k * m) - 1 : ℕ) : ℤ) m := by
        simpa [hm4, hb4] using hrec.symm
      rw [hrec', hbm, ZMod.χ₄_nat_one_mod_four hm4]
    · have hrec :=
        jacobiSym.quadratic_reciprocity_if (a := m) (b := 4 * (2 ^ k * m) - 1)
          hm2 hb2
      have hrec' : jacobiSym (m : ℤ) (4 * (2 ^ k * m) - 1) =
          -jacobiSym ((4 * (2 ^ k * m) - 1 : ℕ) : ℤ) m := by
        simpa [hm4, hb4] using hrec.symm
      rw [hrec', hbm, ZMod.χ₄_nat_three_mod_four hm4]
      ring
  rw [htwoPow, hoddpart, one_mul]

private lemma jacobiSym_neg_nat_four_mul_sub_one (A : ℕ) (hA : A ≠ 0) :
    jacobiSym (-(A : ℤ)) (4 * A - 1) = -1 := by
  have hbodd : Odd (4 * A - 1) := by
    rw [Nat.odd_iff]
    have hpos : 0 < 4 * A := by positivity
    omega
  have hb4 : (4 * A - 1) % 4 = 3 := by
    have hpos : 0 < 4 * A := by positivity
    omega
  rw [jacobiSym.neg (A : ℤ) hbodd, jacobiSym_nat_four_mul_sub_one A hA,
    ZMod.χ₄_nat_three_mod_four hb4]
  ring

/-- The Kronecker symbol at the representative `|D| - 1` is the sign factor
appearing in the integer-denominator convention `(D / -1)`. -/
theorem kroneckerSymNat_natAbs_sub_one_eq_sign (D : ℤ)
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD0 : D.natAbs ≠ 0) :
    kroneckerSymNat D (D.natAbs - 1) = if D < 0 then -1 else 1 := by
  rcases (show D % 4 = 0 ∨ D % 4 = 1 from Fact.out) with hd4 | hd4
  · have h4D : (4 : ℤ) ∣ D := Int.dvd_of_emod_eq_zero hd4
    obtain ⟨a, rfl⟩ := h4D
    have ha0 : a.natAbs ≠ 0 := by
      intro ha
      apply hD0
      simp [ha, Int.natAbs_mul]
    have hN : (4 * a).natAbs = 4 * a.natAbs := by simp [Int.natAbs_mul]
    have hbodd : Odd ((4 * a).natAbs - 1) := by
      rw [hN]
      rw [Nat.odd_iff]
      have hpos : 0 < 4 * a.natAbs := by positivity
      omega
    rw [kroneckerSymNat_of_odd (4 * a) hbodd]
    have h4mod : (4 * a) % 4 = 0 := Int.mul_emod_right 4 a
    rw [← jacobiSym.div_four_left h4mod (Nat.odd_iff.mp hbodd)]
    simp only [Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]
    rcases Int.natAbs_eq a with hpos | hneg
    · rw (occs := .pos [1]) [hpos]
      rw [hN]
      have hlt : ¬4 * a < 0 := by omega
      rw [if_neg hlt]
      exact jacobiSym_nat_four_mul_sub_one a.natAbs ha0
    · calc
        jacobiSym a ((4 * a).natAbs - 1) =
            jacobiSym (-(a.natAbs : ℤ)) ((4 * a).natAbs - 1) := by
          rw (occs := .pos [1]) [hneg]
        _ = if 4 * a < 0 then -1 else 1 := by
          rw [hN]
          have hlt : 4 * a < 0 := by omega
          rw [if_pos hlt]
          exact jacobiSym_neg_nat_four_mul_sub_one a.natAbs ha0
  · rw [kroneckerSymNat_eq_jacobiSym_natAbs_of_emod_four_eq_one D hd4]
    have hNodd : Odd D.natAbs := odd_natAbs_of_emod_four_eq_one D hd4
    have hmod : ((D.natAbs - 1 : ℕ) : ℤ) % D.natAbs = (-1 : ℤ) % D.natAbs := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      have hdiff : ((D.natAbs - 1 : ℕ) : ℤ) - (-1 : ℤ) = D.natAbs := by
        have hNpos : 0 < D.natAbs := Nat.pos_of_ne_zero hD0
        omega
      rw [hdiff, Int.emod_self]
    have hneg :
        jacobiSym ((D.natAbs - 1 : ℕ) : ℤ) D.natAbs =
          jacobiSym (-1 : ℤ) D.natAbs :=
      jacobiSym.mod_left' hmod
    rw [hneg, jacobiSym.at_neg_one hNodd]
    change ZMod.χ₄ (D.natAbs : ZMod 4) = if D < 0 then -1 else 1
    rcases Int.natAbs_eq D with hpos | hnegD
    · have hN4 : D.natAbs % 4 = 1 := by omega
      have hlt : ¬D < 0 := by omega
      rw [ZMod.χ₄_nat_one_mod_four hN4, if_neg hlt]
    · have hN4 : D.natAbs % 4 = 3 := by omega
      have hlt : D < 0 := by omega
      rw [ZMod.χ₄_nat_three_mod_four hN4, if_pos hlt]

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
