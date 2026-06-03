/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Classification
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.QuadraticField.Basic

/-!
# Ramification and the Discriminant

This file proves that a prime `p` ramifies in `𝓞(ℚ(√d))` if and only if
`p` divides the discriminant of `ℚ(√d)`.

## Main Results

* `isRamified_iff_dvd_disc`: `(p)` ramifies in `𝓞(ℚ(√d))` ↔ `p ∣ disc(ℚ(√d))`

Combined with the explicit discriminant formulas from `RingOfIntegers/Discriminant.lean`:
* `disc = 4d` when `d % 4 ≠ 1`
* `disc = d`  when `d % 4 = 1`

this gives an explicit characterization of ramified primes.

## Proof Strategy

Forward (ramified → p ∣ disc):
  ramified → legendreSym p d = 0 → p ∣ d → p ∣ disc (using disc formula)

Backward (p ∣ disc → ramified):
  p ∣ disc → p ∣ d (for odd p: gcd(p,4)=1; for p=2: case split) → ramified
-/

open scoped NumberField
open Ideal

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- TODO: ramified ↔ p | disc
theorem isRamified_iff_dvd_disc (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ)))
      ↔ (p : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ)) := sorry

-- TODO: explicit characterization of ramified primes
-- theorem ramified_primes_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
--     (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ)))
--       ↔ (p : ℤ) ∣ d := ...

-- theorem ramified_prime_two :
--     (Ideal.span {(2 : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ)))
--       ↔ d % 4 ≠ 1 := ...

end Splitting
end QuadraticNumberFields
