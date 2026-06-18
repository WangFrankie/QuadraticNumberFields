/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Zsqrtd.Dedekind
import QNFMathlib.RingTheory.DedekindDomain.Basic
import QuadraticNumberFields.Zsqrtd.MathlibBridge
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Additional Instances for mathlib `Zsqrtd`

This module adds generic algebraic instances for mathlib's `_root_.Zsqrtd d`
under useful arithmetic hypotheses.

## Main Definitions

* `Zsqrtd.instNoZeroDivisors`: `NoZeroDivisors (Zsqrtd d)` for `d < 0`.
* `Zsqrtd.instIsDomain`: `IsDomain (Zsqrtd d)` for `d < 0`.
* `Zsqrtd.isDedekindDomain_of_mod_four_ne_one`: `IsDedekindDomain (Zsqrtd d)`
  for squarefree `d ≠ 1` with `d % 4 ≠ 1`.
* `Zsqrtd.instIsDedekindDomain_zsqrtd_of_mod_four_ne_one`: instance providing
  `IsDedekindDomain (Zsqrtd d)` when `[Fact (d % 4 ≠ 1)]` is available.
* `Zsqrtd.not_isDedekindDomain_of_mod_four_eq_one`: `ℤ√d` is not Dedekind when
  `d % 4 = 1`.
-/

namespace Zsqrtd

instance instNoZeroDivisors {d : ℤ} [Fact (d < 0)] : NoZeroDivisors (Zsqrtd d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have hnorm : Zsqrtd.norm (a * b) = 0 := by
      simp [hab, Zsqrtd.norm_zero (d := d)]
    have hmulnorm : Zsqrtd.norm a * Zsqrtd.norm b = 0 := by
      simpa [Zsqrtd.norm_mul] using hnorm
    rcases mul_eq_zero.mp hmulnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (d := d) Fact.out a).1 ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (d := d) Fact.out b).1 hb)

instance instIsDomain {d : ℤ} [Fact (d < 0)] : IsDomain (Zsqrtd d) :=
  NoZeroDivisors.to_isDomain (Zsqrtd d)

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

theorem isDedekindDomain_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    IsDedekindDomain (Zsqrtd d) := by
  let e := QuadraticNumberFields.Zsqrtd.equivMathlib d
  letI : IsDedekindDomain (QuadraticNumberFields.Zsqrtd d) :=
    QuadraticNumberFields.Zsqrtd.isDedekindDomain_of_mod_four_ne_one
      d hd4
  exact RingEquiv.isDedekindDomain e
instance instIsDedekindDomain_zsqrtd_of_mod_four_ne_one
    [Fact (d % 4 ≠ 1)] :
    IsDedekindDomain (Zsqrtd d) :=
  isDedekindDomain_of_mod_four_ne_one d Fact.out


theorem not_isDedekindDomain_of_mod_four_eq_one
    (hd4 : d % 4 = 1) :
    ¬ IsDedekindDomain (Zsqrtd d) := by
  intro hDed
  letI : IsDedekindDomain (Zsqrtd d) := hDed
  have hDedQA : IsDedekindDomain (QuadraticNumberFields.Zsqrtd d) :=
    RingEquiv.isDedekindDomain
      (QuadraticNumberFields.Zsqrtd.equivMathlib d).symm
  exact
    ((QuadraticNumberFields.Zsqrtd.isDedekindDomain_iff_mod_four_ne_one
      d).mp hDedQA) hd4

/-- For a squarefree `d ≠ 1`, mathlib's `ℤ√d` is Dedekind exactly in
the `d % 4 ≠ 1` branch. -/
theorem isDedekindDomain_iff_mod_four_ne_one
    :
    IsDedekindDomain (Zsqrtd d) ↔ d % 4 ≠ 1 := by
  constructor
  · intro hDed hd4
    exact not_isDedekindDomain_of_mod_four_eq_one d hd4 hDed
  · exact isDedekindDomain_of_mod_four_ne_one d

end SquarefreeIntegerParameter

end Zsqrtd
