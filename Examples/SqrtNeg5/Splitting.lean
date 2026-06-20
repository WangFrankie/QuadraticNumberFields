/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Defs
import QuadraticNumberFields.Splitting.Factorization
import QuadraticNumberFields.Splitting.MinpolyMod
import QuadraticNumberFields.Splitting.Qsqrtd.Classification
import QuadraticNumberFields.Splitting.Qsqrtd.Discriminant
import QuadraticNumberFields.Splitting.Qsqrtd.KummerDedekind
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic
import QuadraticNumberFields.Splitting.Qsqrtd.OddPrime
import QuadraticNumberFields.Splitting.Qsqrtd.Two
import QuadraticNumberFields.Splitting.QuadraticField.Basic
import QuadraticNumberFields.RingOfIntegers.CommonInstances

/-!
# Prime Splitting in `ℚ(√-5)` (abstract classification view)

This file instantiates the general splitting classification
(`QuadraticNumberFields.Splitting`) on the imaginary quadratic field `ℚ(√-5)`,
reading off the split / inert / ramified type of small rational primes from the
`legendreSym` and `d mod 8` criteria.

It is the *abstract*, numerical-invariant counterpart of the explicit,
ideal-level factorizations in `Examples.SqrtNeg5.Ideals` and
`Examples.SqrtNeg5.RamificationInertia`, which exhibit concrete prime ideals
such as `(2, 1+√-5)` and prove identities like `(2) = (2, 1+√-5)²` on the model
ring `ℤ[√-5]`. Here we instead apply the crown-jewel theorem
`splitting_classification` directly to `𝓞(ℚ(√-5))`.

Since `-5 ≡ 3 (mod 4)`, the ring of integers is `ℤ[√-5]`.

## Summary Table

| Prime `p` | `legendreSym p (-5)` / congruence | Behaviour |
|-----------|-----------------------------------|-----------|
| `2`       | `-5 ≡ 3 (mod 4)`                   | ramified  |
| `3`       | `legendreSym 3 (-5) = 1`          | split     |
| `5`       | `5 ∣ -5`                          | ramified  |
| `7`       | `legendreSym 7 (-5) = 1`          | split     |
| `11`      | `legendreSym 11 (-5) = -1`        | inert     |
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField
open Ideal
open QuadraticNumberFields.Splitting

namespace QuadraticNumberFields.Examples.SqrtNeg5

/-! ## Prime `Fact` instances for the primes used below -/

instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance fact_prime_11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-! ## Splitting behaviour of small primes in `ℚ(√-5)` -/

/-- `(2)` ramifies in `ℚ(√-5)`: indeed `-5 ≡ 3 (mod 4)`. -/
theorem two_isRamified : Ideal.IsRamifiedIn (𝔭(2)) 𝓞((-5 : ℤ)) :=
  isRamified_two_of_mod_four_ne_one (-5) (by decide)

/-- `(3)` splits in `ℚ(√-5)`: indeed `legendreSym 3 (-5) = 1`. -/
theorem three_isSplit : Ideal.IsSplitIn (𝔭(3)) 𝓞((-5 : ℤ)) :=
  (isSplit_iff_legendreSym_eq_one (-5) 3 (by decide) (by decide)).mpr (by decide)

/-- `(5)` ramifies in `ℚ(√-5)`: indeed `5 ∣ -5`. -/
theorem five_isRamified : Ideal.IsRamifiedIn (𝔭(5)) 𝓞((-5 : ℤ)) :=
  isRamified_of_dvd (-5) 5 (by decide)

/-- `(7)` splits in `ℚ(√-5)`: indeed `legendreSym 7 (-5) = 1`. -/
theorem seven_isSplit : Ideal.IsSplitIn (𝔭(7)) 𝓞((-5 : ℤ)) :=
  (isSplit_iff_legendreSym_eq_one (-5) 7 (by decide) (by decide)).mpr (by decide)

/-- `(11)` is inert in `ℚ(√-5)`: indeed `legendreSym 11 (-5) = -1`. -/
theorem eleven_isInert : Ideal.IsInertIn (𝔭(11)) 𝓞((-5 : ℤ)) :=
  (isInert_iff_legendreSym_eq_neg_one (-5) 11 (by decide) (by decide)).mpr (by decide)

end QuadraticNumberFields.Examples.SqrtNeg5
