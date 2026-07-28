/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Kronecker Symbol

Material destined for mathlib.

This file defines the Kronecker symbol for arbitrary integer numerators and
denominators. The natural-denominator core extends the Jacobi symbol by the
supplementary value at `2`; the integer interface adds the conventions at
`-1` and `0`.

## Main definitions

* `kroneckerTwo`: the supplementary Kronecker value `(D / 2)`.
* `kroneckerNegOne`: the supplementary Kronecker value `(D / -1)`.
* `kroneckerSymNat`: the Kronecker symbol `(D / n)` with natural denominator `n`.
* `kroneckerSym`: the Kronecker symbol `(D / n)` with integer denominator `n`.

## Main results

* `kroneckerSym_zero_right`, `kroneckerSym_one_right`,
  `kroneckerSym_neg_one_right`: the exceptional denominator values.
* `kroneckerSymNat_two`: `(D / 2)` is the supplementary value.
* `kroneckerTwo_eq_zero_iff`, `kroneckerTwo_eq_one_iff`,
  `kroneckerTwo_eq_neg_one_iff`: the mod-8 supplementary law.
* `kroneckerSym_natCast`, `kroneckerSym_neg_natCast`: reduction of integer
  denominators to `kroneckerSymNat`.
* `kroneckerSymNat_eq_legendreSym_of_ne_two`,
  `kroneckerSym_eq_legendreSym_of_ne_two`: for an odd prime `p`, `(D / p)` is the
  Legendre symbol `legendreSym p D`.
-/

/-- The supplementary Kronecker value `(D / 2)`: zero for even `D`, and otherwise
determined by `D % 8` (`1` for `D ≡ ±1 [ZMOD 8]`, `-1` for `D ≡ ±3 [ZMOD 8]`). -/
def kroneckerTwo (D : ℤ) : ℤ :=
  if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1

/-- The supplementary Kronecker value `(D / -1)`: `-1` for negative `D`, and
`1` for nonnegative `D`. In particular, `(0 / -1) = 1`. -/
def kroneckerNegOne (D : ℤ) : ℤ :=
  if D < 0 then -1 else 1

/-- The Kronecker symbol `(D / n)` with natural denominator `n`: the Jacobi symbol
on the odd part of `n` times the supplementary value `(D / 2)` raised to the
`2`-adic valuation of `n`. -/
def kroneckerSymNat (D : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then
    if D.natAbs = 1 then 1 else 0
  else
    kroneckerTwo D ^ n.factorization 2 * jacobiSym D (n / 2 ^ n.factorization 2)

/-- The Kronecker symbol `(D / n)` with integer denominator `n`, extending
`kroneckerSymNat` by the supplementary factor `(D / -1)` for negative `n`.
The zero-denominator convention is inherited from `kroneckerSymNat`. -/
def kroneckerSym (D n : ℤ) : ℤ :=
  (if n < 0 then kroneckerNegOne D else 1) * kroneckerSymNat D n.natAbs

/-! ### Supplementary and exceptional values -/

/-- The supplementary value `(D / -1)` is `-1` for negative `D`. -/
@[simp]
theorem kroneckerNegOne_of_neg {D : ℤ} (hD : D < 0) :
    kroneckerNegOne D = -1 := by
  simp [kroneckerNegOne, hD]

/-- The supplementary value `(D / -1)` is `1` for nonnegative `D`. -/
@[simp]
theorem kroneckerNegOne_of_nonneg {D : ℤ} (hD : 0 ≤ D) :
    kroneckerNegOne D = 1 := by
  rw [kroneckerNegOne, if_neg (not_lt.mpr hD)]

/-- The supplementary value `(D / -1)` has square one. -/
@[simp]
theorem kroneckerNegOne_sq (D : ℤ) : kroneckerNegOne D ^ 2 = 1 := by
  simp [kroneckerNegOne]

/-- The supplementary value `(D / -1)` never vanishes. -/
@[simp]
theorem kroneckerNegOne_ne_zero (D : ℤ) : kroneckerNegOne D ≠ 0 := by
  unfold kroneckerNegOne
  split_ifs <;> norm_num

/-- Away from the exceptional numerator `0`, `(D / -1)` is the integer sign. -/
theorem kroneckerNegOne_eq_sign_of_ne_zero {D : ℤ} (hD : D ≠ 0) :
    kroneckerNegOne D = D.sign := by
  by_cases hDneg : D < 0
  · rw [kroneckerNegOne_of_neg hDneg,
      Int.sign_eq_neg_one_iff_neg.mpr hDneg]
  · have hDpos : 0 < D :=
      lt_of_le_of_ne (not_lt.mp hDneg) (Ne.symm hD)
    rw [kroneckerNegOne_of_nonneg (le_of_lt hDpos),
      Int.sign_eq_one_iff_pos.mpr hDpos]

/-- The supplementary value `(D / -1)` is multiplicative on nonzero
numerators. The hypotheses exclude the exceptional convention `(0 / -1) = 1`. -/
theorem kroneckerNegOne_mul (D E : ℤ) (hD : D ≠ 0) (hE : E ≠ 0) :
    kroneckerNegOne (D * E) = kroneckerNegOne D * kroneckerNegOne E := by
  calc
    kroneckerNegOne (D * E) = (D * E).sign :=
      kroneckerNegOne_eq_sign_of_ne_zero (mul_ne_zero hD hE)
    _ = D.sign * E.sign := Int.sign_mul D E
    _ = kroneckerNegOne D * kroneckerNegOne E := by
      rw [← kroneckerNegOne_eq_sign_of_ne_zero hD,
        ← kroneckerNegOne_eq_sign_of_ne_zero hE]

/-- The natural-denominator Kronecker symbol at denominator `0`. -/
@[simp]
theorem kroneckerSymNat_zero_right (D : ℤ) :
    kroneckerSymNat D 0 = if D.natAbs = 1 then 1 else 0 := by
  simp [kroneckerSymNat]

/-- The natural-denominator Kronecker symbol at denominator `1`. -/
@[simp]
theorem kroneckerSymNat_one_right (D : ℤ) : kroneckerSymNat D 1 = 1 := by
  simp [kroneckerSymNat, kroneckerTwo, jacobiSym.one_right]

/-- The Kronecker symbol at denominator `2` is the supplementary value. -/
@[simp]
theorem kroneckerSymNat_two (D : ℤ) : kroneckerSymNat D 2 = kroneckerTwo D := by
  have h : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  simp [kroneckerSymNat, h]

/-- The supplementary value `(D / 2)` vanishes exactly for even `D`. -/
theorem kroneckerTwo_eq_zero_iff (D : ℤ) : kroneckerTwo D = 0 ↔ D % 2 = 0 := by
  unfold kroneckerTwo
  split_ifs <;> simp_all

/-- The supplementary value `(D / 2)` is `1` exactly for `D ≡ ±1 [ZMOD 8]`. -/
theorem kroneckerTwo_eq_one_iff (D : ℤ) : kroneckerTwo D = 1 ↔ D % 8 = 1 ∨ D % 8 = 7 := by
  unfold kroneckerTwo
  split_ifs <;> simp_all
  omega

/-- The supplementary value `(D / 2)` is `-1` exactly for `D ≡ ±3 [ZMOD 8]`. -/
theorem kroneckerTwo_eq_neg_one_iff (D : ℤ) :
    kroneckerTwo D = -1 ↔ D % 8 = 3 ∨ D % 8 = 5 := by
  unfold kroneckerTwo
  split_ifs <;> simp_all <;> omega

/-- At a nonnegative integer denominator, `kroneckerSym` reduces to
`kroneckerSymNat` at its absolute value. -/
theorem kroneckerSym_of_nonneg (D : ℤ) {n : ℤ} (hn : 0 ≤ n) :
    kroneckerSym D n = kroneckerSymNat D n.natAbs := by
  rw [kroneckerSym, if_neg (not_lt.mpr hn), one_mul]

/-- At a negative denominator, `kroneckerSym` is the natural-denominator value
times the supplementary factor `(D / -1)`. -/
theorem kroneckerSym_of_neg (D : ℤ) {n : ℤ} (hn : n < 0) :
    kroneckerSym D n = kroneckerNegOne D * kroneckerSymNat D n.natAbs := by
  simp [kroneckerSym, hn]

/-- The integer-denominator Kronecker symbol at denominator `0`. -/
@[simp]
theorem kroneckerSym_zero_right (D : ℤ) :
    kroneckerSym D 0 = if D.natAbs = 1 then 1 else 0 := by
  simp [kroneckerSym]

/-- The integer-denominator Kronecker symbol at denominator `1`. -/
@[simp]
theorem kroneckerSym_one_right (D : ℤ) : kroneckerSym D 1 = 1 := by
  simp [kroneckerSym]

/-- The integer-denominator Kronecker symbol at denominator `-1`. -/
@[simp]
theorem kroneckerSym_neg_one_right (D : ℤ) :
    kroneckerSym D (-1) = kroneckerNegOne D := by
  simp [kroneckerSym]

/-- At a natural denominator, the integer-denominator Kronecker symbol agrees with
the natural-denominator interface. -/
@[simp]
theorem kroneckerSym_natCast (D : ℤ) (n : ℕ) :
    kroneckerSym D n = kroneckerSymNat D n := by
  simp [kroneckerSym]

/-- At a negative natural cast, the integer-denominator Kronecker symbol reduces
to `kroneckerSymNat` and the supplementary factor `(D / -1)`. -/
@[simp]
theorem kroneckerSym_neg_natCast (D : ℤ) {n : ℕ} (hn : n ≠ 0) :
    kroneckerSym D (-(n : ℤ)) = kroneckerNegOne D * kroneckerSymNat D n := by
  have hneg : -(n : ℤ) < 0 :=
    neg_neg_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)
  rw [kroneckerSym_of_neg D hneg, Int.natAbs_neg, Int.natAbs_natCast]

/-- The integer-denominator Kronecker symbol at denominator `2`. -/
@[simp]
theorem kroneckerSym_two_right (D : ℤ) : kroneckerSym D 2 = kroneckerTwo D := by
  change kroneckerSym D ((2 : ℕ) : ℤ) = kroneckerTwo D
  rw [kroneckerSym_natCast, kroneckerSymNat_two]

/-- The integer-denominator Kronecker symbol at denominator `-2`. -/
@[simp]
theorem kroneckerSym_neg_two_right (D : ℤ) :
    kroneckerSym D (-2) = kroneckerNegOne D * kroneckerTwo D := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
    kroneckerSym_neg_natCast D (by norm_num), kroneckerSymNat_two]

/-- For an odd prime `p`, the Kronecker symbol `(D / p)` is the Legendre symbol. -/
theorem kroneckerSymNat_eq_legendreSym_of_ne_two (D : ℤ) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) : kroneckerSymNat D p = legendreSym p D := by
  have h2 : p.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp hdvd).symm
  rw [kroneckerSymNat, if_neg hp.out.ne_zero, h2, pow_zero, one_mul, pow_zero, Nat.div_one,
    jacobiSym.legendreSym.to_jacobiSym]

/-- For an odd natural prime viewed as an integer denominator, the Kronecker
symbol `(D / p)` is the Legendre symbol. -/
theorem kroneckerSym_eq_legendreSym_of_ne_two (D : ℤ) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : kroneckerSym D (p : ℤ) = legendreSym p D := by
  rw [kroneckerSym_natCast, kroneckerSymNat_eq_legendreSym_of_ne_two D hp2]
