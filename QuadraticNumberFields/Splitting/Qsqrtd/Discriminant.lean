/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Qsqrtd.Classification
import QuadraticNumberFields.RingOfIntegers.Discriminant

/-!
# Ramification and the Discriminant for `Qsqrtd`

This file proves that a prime `p` ramifies in `𝓞(ℚ(√d))` if and only if
`p` divides the discriminant of `ℚ(√d)`.

## Main Results

* `isRamified_iff_dvd_disc`: `(p)` ramifies in `𝓞(ℚ(√d))` ↔
  `p ∣ NumberField.discr (ℚ(√d))`

Combined with the explicit discriminant formulas from `RingOfIntegers/Discriminant.lean`:
* `disc = 4d` when `d % 4 ≠ 1`
* `disc = d`  when `d % 4 = 1`

this gives an explicit characterization of ramified primes.

## Proof Strategy

Forward (ramified → p ∣ disc):
  ramified → legendreSym p d = 0 → p ∣ d → p ∣ disc (using disc formula)

Backward (p ∣ disc → ramified):
  p ∣ disc → p ∣ d (for odd p: gcd(p,4)=1; for p=2: case split) → ramified

## Reference

K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Chapter 13, §1. The discriminant formulas are Proposition 13.1.2; ramification is the
`p ∣ δ_F` case of Propositions 13.1.3 (odd `p`) and 13.1.4 (`p = 2`).
-/

open scoped NumberField
open Ideal

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- `𝔭(p)` is shared from `Splitting.Defs`; `𝓞(d)` is shared from
-- `Splitting.Qsqrtd.Monogenic`.
/-- The discriminant of `ℚ(√d)`. -/
scoped notation3 "disc(" d ")" => NumberField.discr (Qsqrtd (d : ℚ))

-- TODO: ramified ↔ p | disc
theorem isRamified_iff_dvd_disc (p : ℕ) [Fact p.Prime] :
    Ideal.IsRamifiedIn 𝔭(p) 𝓞(d) ↔ (p : ℤ) ∣ disc(d) := sorry
-- TODO: explicit characterization of ramified primes
-- theorem ramified_primes_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
--     1 < Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))
--       ↔ (p : ℤ) ∣ d := ...

-- theorem ramified_prime_two :
--     1 < Ideal.ramificationIdxIn (Ideal.span {(2 : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))
--       ↔ d % 4 ≠ 1 := ...

end Splitting
end QuadraticNumberFields
