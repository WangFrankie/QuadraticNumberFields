/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Zsqrtd.Basic

/-!
# Half-Integer Representatives

This file defines half-integer representatives `(a + b√d) / 2` in quadratic fields
and provides basic structural lemmas. These are used in the classification of
rings of integers when `d ≡ 1 (mod 4)`.

## Main Definitions

* `halfInt d a' b'`: The half-integer `(a' + b'√d) / 2` in `Q(√d)`.
* `omegaHalf d`: The distinguished generator `(1 + √d) / 2`.

## Main Theorems

* `halfInt_re`, `halfInt_im`: Coordinate simp lemmas.
* `omegaHalf_re`, `omegaHalf_im`: Coordinates of `omegaHalf`.
* `trace_halfInt`: Trace of `halfInt d a' b'` is `a'`.
* `norm_halfInt`: Norm of `halfInt d a' b'` is `(a'² - d·b'²) / 4`.
-/

namespace QuadraticNumberFields
namespace RingOfIntegers

/-- Canonical half-integer representative `(a' + b'√d)/2` in `Q(√d)`. -/
abbrev halfInt (d : ℤ) (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  Zsqrtd.halfInt (d := d) a' b'

/-- The distinguished half-integer generator `(1 + √d)/2`. -/
abbrev omegaHalf (d : ℤ) : Qsqrtd (d : ℚ) := halfInt d 1 1

@[simp] theorem halfInt_re (d a' b' : ℤ) :
    (halfInt d a' b').re = (a' : ℚ) / 2 := rfl

@[simp] theorem halfInt_im (d a' b' : ℤ) :
    (halfInt d a' b').im = (b' : ℚ) / 2 := rfl

@[simp] theorem omegaHalf_re (d : ℤ) :
    (omegaHalf d).re = (1 : ℚ) / 2 := rfl

@[simp] theorem omegaHalf_im (d : ℤ) :
    (omegaHalf d).im = (1 : ℚ) / 2 := rfl

/-- Trace of `halfInt` is `a'`. -/
theorem trace_halfInt (d a' b' : ℤ) : Algebra.trace ℚ (Qsqrtd d) (halfInt d a' b') = a' := by
  -- The trace on `Q(√d)` is twice the real part, so for `(a' + b'√d)/2`
  -- the denominator cancels and leaves `a'`.
  simp [halfInt]

/-- Norm of `halfInt` is `(a'² - d*b'²)/4`. -/
theorem norm_halfInt (d a' b' : ℤ) :
    Qsqrtd.norm (halfInt d a' b') = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := by
  -- Expand `re = a'/2` and `im = b'/2` in the formula
  -- `N(r + s√d) = r² - d s²`.
  simp [halfInt, Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

end RingOfIntegers
end QuadraticNumberFields
