/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.Ring

/-!
# Lemmas for Mathlib's `Zsqrtd`

Material destined for mathlib.
-/

namespace Zsqrtd

variable {d : ℤ}

/-- The fundamental identity for `re + im` of a product in mathlib's `ℤ√d`. -/
lemma mul_re_add_im_eq (a b : Zsqrtd d) :
    (a * b).re + (a * b).im =
      (a.re + a.im) * (b.re + b.im) + (d - 1) * a.im * b.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

/-- The fundamental identity for `re - im` of a product in mathlib's `ℤ√d`. -/
lemma mul_re_sub_im_eq (a b : Zsqrtd d) :
    (a * b).re - (a * b).im =
      (a.re - a.im) * (b.re - b.im) + (d - 1) * a.im * b.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

end Zsqrtd
