/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting
import QuadraticNumberFields.RingOfIntegers.CommonInstances

/-!
# Prime Splitting in `ℚ(√17)` (real quadratic example)

This file instantiates the general splitting classification
(`QuadraticNumberFields.Splitting`) on the real quadratic field `ℚ(√17)`,
reading off the split / inert / ramified type of small rational primes from the
`legendreSym` and `d mod 8` criteria.

Together with `Examples.ZsqrtdNeg5.Splitting` (the imaginary field `ℚ(√-5)`),
this exercises every branch of the classification:

* `p = 2` is handled by the `d mod 8` criterion; here `17 ≡ 1 (mod 8)` gives the
  **split** case, complementing the **ramified** case `-5 ≡ 3 (mod 4)` of
  `ℚ(√-5)`.
* odd primes use the Legendre symbol, covering split, inert, and ramified.

Since `17 ≡ 1 (mod 4)`, the ring of integers is `ℤ[(1+√17)/2]`.

## Summary Table

| Prime `p` | `legendreSym p 17` / congruence | Behaviour |
|-----------|---------------------------------|-----------|
| `2`       | `17 ≡ 1 (mod 8)`                | split     |
| `3`       | `legendreSym 3 17 = -1`         | inert     |
| `13`      | `legendreSym 13 17 = 1`         | split     |
| `17`      | `17 ∣ 17`                       | ramified  |
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField
open Ideal
open QuadraticNumberFields.Splitting

namespace QuadraticNumberFields.Examples.Sqrt17

/-! ## Prime `Fact` instances for the primes used below -/

-- `Fact (Nat.Prime 2)` and `Fact (Nat.Prime 3)` are already global mathlib instances.
instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ## Splitting behaviour of small primes in `ℚ(√17)` -/

/-- `(2)` splits in `ℚ(√17)`: indeed `17 ≡ 1 (mod 8)`. -/
theorem two_isSplit : Ideal.IsSplitIn (𝔭(2)) 𝓞((17 : ℤ)) :=
  isSplit_two_of_mod_eight_eq_one 17 (by decide)

/-- `(3)` is inert in `ℚ(√17)`: indeed `legendreSym 3 17 = -1`. -/
theorem three_isInert : Ideal.IsInertIn (𝔭(3)) 𝓞((17 : ℤ)) :=
  (isInert_iff_legendreSym_eq_neg_one (17) 3 (by decide) (by decide)).mpr (by decide)

/-- `(13)` splits in `ℚ(√17)`: indeed `legendreSym 13 17 = 1`. -/
theorem thirteen_isSplit : Ideal.IsSplitIn (𝔭(13)) 𝓞((17 : ℤ)) :=
  (isSplit_iff_legendreSym_eq_one (17) 13 (by decide) (by decide)).mpr (by decide)

/-- `(17)` ramifies in `ℚ(√17)`: indeed `17 ∣ 17`. -/
theorem seventeen_isRamified : Ideal.IsRamifiedIn (𝔭(17)) 𝓞((17 : ℤ)) :=
  isRamified_of_dvd (17) 17 (by decide)

end QuadraticNumberFields.Examples.Sqrt17
