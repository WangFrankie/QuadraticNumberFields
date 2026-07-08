/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Zsqrtd.MathlibBridge
import QNFMathlib.Data.Int.Parity
import QNFMathlib.RingTheory.Coprime
import QNFMathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# The Project-Owned Gaussian Order

This module equips the project model `QuadraticNumberFields.Zsqrtd (-1)` with
the algebraic structure needed for Gaussian-integer arguments. The Euclidean
structure is transported through `Zsqrtd.equivMathlib`; the public API remains
about the project-owned `Zsqrtd`, not mathlib's `_root_.Zsqrtd`.
-/

namespace QuadraticNumberFields
namespace Zsqrtd

/-- The project-owned Gaussian order `Zsqrtd (-1)` is a principal ideal ring. -/
noncomputable instance instIsPrincipalIdealRingNegOne :
    IsPrincipalIdealRing (Zsqrtd (-1)) :=
  RingEquiv.isPrincipalIdealRing (Zsqrtd.equivMathlib (-1)).symm

/-- The project-owned Gaussian order `Zsqrtd (-1)` is a domain. -/
instance instIsDomainNegOne : IsDomain (Zsqrtd (-1)) := by
  haveI : Fact ((-1 : ℤ) < 0) := ⟨by norm_num⟩
  infer_instance

/-- In the project-owned Gaussian order, the two factors `z ± √-1` are
coprime when their product has odd cube norm `n ^ 3 = z ^ 2 + 1`. -/
theorem isCoprime_mk_im_one_mk_im_neg_one_of_cube_eq_sq_add_one {n z : ℤ}
    (h : n ^ 3 = z ^ 2 + 1) :
    IsCoprime (⟨z, 1⟩ : Zsqrtd (-1)) (⟨z, -1⟩ : Zsqrtd (-1)) := by
  refine isCoprime_of_dvd _ _ ?_ ?_
  · rintro ⟨hzero, _⟩
    have him := congrArg QuadraticAlgebra.im hzero
    norm_num at him
  · intro c hc_nonunit _hc_ne hcα hcβ
    have hcdiff :
        c ∣ (⟨z, 1⟩ : Zsqrtd (-1)) - (⟨z, -1⟩ : Zsqrtd (-1)) :=
      dvd_sub hcα hcβ
    have hnormα : Zsqrtd.norm c ∣ n ^ 3 := by
      have hdvd := Zsqrtd.norm_dvd_norm_of_dvd hcα
      simpa [Zsqrtd.norm_mk, h] using hdvd
    have hnormdiff : Zsqrtd.norm c ∣ (4 : ℤ) := by
      have hdvd := Zsqrtd.norm_dvd_norm_of_dvd hcdiff
      have hdiff_norm :
          Zsqrtd.norm
              ((⟨z, 1⟩ : Zsqrtd (-1)) - (⟨z, -1⟩ : Zsqrtd (-1))) = 4 := by
        simp [Zsqrtd.norm_def, sub_eq_add_neg, QuadraticAlgebra.re_add,
          QuadraticAlgebra.im_add]
      rwa [hdiff_norm] at hdvd
    have hunit_norm : IsUnit (Zsqrtd.norm c) :=
      Int.isUnit_of_dvd_odd_cube_and_dvd_four (Int.odd_of_cube_eq_sq_add_one h)
        hnormα hnormdiff
    have hc_unit : IsUnit c := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
      exact hunit_norm
    exact (mem_nonunits_iff.mp hc_nonunit) hc_unit

/-- If `n ^ 3 = z ^ 2 + 1`, then the Gaussian factor `z + √-1` is associated
to a cube in the project-owned `Zsqrtd (-1)`. -/
theorem exists_associated_cube_mk_im_one_of_cube_eq_sq_add_one {n z : ℤ}
    (h : n ^ 3 = z ^ 2 + 1) :
    ∃ w : Zsqrtd (-1), Associated (w ^ 3) (⟨z, 1⟩ : Zsqrtd (-1)) := by
  have hcop := Zsqrtd.isCoprime_mk_im_one_mk_im_neg_one_of_cube_eq_sq_add_one h
  have hprod :
      (⟨z, 1⟩ : Zsqrtd (-1)) * (⟨z, -1⟩ : Zsqrtd (-1)) =
        (n : Zsqrtd (-1)) ^ 3 := by
    ext <;> simp [pow_succ]
    nlinarith
  exact exists_associated_pow_of_mul_eq_pow' hcop hprod

end Zsqrtd
end QuadraticNumberFields
