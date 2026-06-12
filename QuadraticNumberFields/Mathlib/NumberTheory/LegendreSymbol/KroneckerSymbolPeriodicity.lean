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
* `kroneckerSymNat_mul` (Shim B): full multiplicativity in the lower argument.
* `kroneckerSymNat_eq_zero_of_not_coprime` (Shim C): the symbol vanishes whenever
  the lower argument shares a prime factor with `D.natAbs`.

All three shims depend only on
`QuadraticNumberFields.Mathlib.NumberTheory.LegendreSymbol.KroneckerSymbol` and
mathlib; they are project-quadratic-field-independent.
-/

namespace QuadraticNumberFields

-- Declarations populated by Shims A/B/C in subsequent commits.

end QuadraticNumberFields
