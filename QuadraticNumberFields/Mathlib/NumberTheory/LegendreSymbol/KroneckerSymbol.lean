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

This file provides a small Kronecker-symbol API needed for prime splitting in
quadratic number fields.  The Kronecker symbol `(D / n)` extends the Jacobi
symbol to arbitrary denominators by the supplementary value at `2` and the
sign convention at `-1` and `0`.

## Main definitions

* `QuadraticNumberFields.kroneckerTwo`: the supplementary Kronecker value `(D / 2)`.
* `QuadraticNumberFields.kroneckerSymNat`: the Kronecker symbol `(D / n)` with
  natural denominator `n`.
* `QuadraticNumberFields.kroneckerSym`: the Kronecker symbol `(D / n)` with
  integer denominator `n`.

## Main results

* `QuadraticNumberFields.kroneckerSymNat_two`: `(D / 2)` is the supplementary value.
* `QuadraticNumberFields.kroneckerTwo_eq_zero_iff`,
  `QuadraticNumberFields.kroneckerTwo_eq_one_iff`,
  `QuadraticNumberFields.kroneckerTwo_eq_neg_one_iff`: the mod-8 supplementary law.
* `QuadraticNumberFields.kroneckerSymNat_of_prime_ne_two`: for an odd prime `p`,
  `(D / p)` is the Legendre symbol `legendreSym p D`.
-/

namespace QuadraticNumberFields

/-- The supplementary Kronecker value `(D / 2)`: zero for even `D`, and otherwise
determined by `D % 8` (`1` for `D ≡ ±1 [ZMOD 8]`, `-1` for `D ≡ ±3 [ZMOD 8]`). -/
def kroneckerTwo (D : ℤ) : ℤ :=
  if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1

/-- The Kronecker symbol `(D / n)` with natural denominator `n`: the Jacobi symbol
on the odd part of `n` times the supplementary value `(D / 2)` raised to the
`2`-adic valuation of `n`. -/
def kroneckerSymNat (D : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then
    if D.natAbs = 1 then 1 else 0
  else
    kroneckerTwo D ^ n.factorization 2 * jacobiSym D (n / 2 ^ n.factorization 2)

/-- The Kronecker symbol `(D / n)` with integer denominator `n`, extending
`kroneckerSymNat` by the sign convention `(D / -1) = sign D` for negative `n`. -/
def kroneckerSym (D n : ℤ) : ℤ :=
  if n = 0 then
    if D.natAbs = 1 then 1 else 0
  else if n < 0 then
    (if D < 0 then -1 else 1) * kroneckerSymNat D n.natAbs
  else
    kroneckerSymNat D n.natAbs

/-- The Kronecker symbol at denominator `2` is the supplementary value. -/
@[simp] theorem kroneckerSymNat_two (D : ℤ) : kroneckerSymNat D 2 = kroneckerTwo D := by
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

/-- For an odd prime `p`, the Kronecker symbol `(D / p)` is the Legendre symbol. -/
theorem kroneckerSymNat_of_prime_ne_two (D : ℤ) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    kroneckerSymNat D p = legendreSym p D := by
  have h2 : p.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp hdvd).symm
  rw [kroneckerSymNat, if_neg hp.out.ne_zero, h2, pow_zero, one_mul, pow_zero, Nat.div_one,
    jacobiSym.legendreSym.to_jacobiSym]

end QuadraticNumberFields
