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

/-- Periodicity of the Kronecker symbol modulo `|D|`, valid for every integer
discriminant `D` with `D % 4 ∈ {0, 1}`. -/
theorem kroneckerSymNat_add_natAbs_eq (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] (n : ℕ) :
    kroneckerSymNat D (n + D.natAbs) = kroneckerSymNat D n := by
  sorry

/-- Full multiplicativity of the Kronecker symbol in the lower (natural) argument,
for nonzero inputs. -/
theorem kroneckerSymNat_mul (D : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    kroneckerSymNat D (m * n) = kroneckerSymNat D m * kroneckerSymNat D n := by
  sorry

/-- The Kronecker symbol vanishes whenever the natural denominator shares a prime
factor with `D.natAbs`. -/
theorem kroneckerSymNat_eq_zero_of_not_coprime (D : ℤ) {n : ℕ}
    (h : Nat.gcd n D.natAbs ≠ 1) : kroneckerSymNat D n = 0 := by
  sorry

end QuadraticNumberFields
