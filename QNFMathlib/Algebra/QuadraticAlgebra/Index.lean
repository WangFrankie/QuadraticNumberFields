/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticAlgebra.AlgHom
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Indices of homomorphisms of quadratic algebras

The additive index of the range of an algebra homomorphism between quadratic
algebras over `ℤ` is the absolute value of its determinant, namely the imaginary
coordinate of the image of `ω`. This includes noninjective homomorphisms: both
sides are zero when the determinant vanishes.

This generalizes the index calculations by Frankie Wang in
[`HalfIntegral.lean`](https://github.com/WangFrankie/BakerHeegnerStark/blob/42c273b84c375c93258ca00774d7d3efe314d7ef/BakerHeegnerStark/ComplexMultiplication/Orders/HalfIntegral.lean).
-/

namespace QuadraticAlgebra

variable {a b a' b' : ℤ}

/-- The additive index of the range of an algebra homomorphism between quadratic
algebras over `ℤ` is the absolute value of the imaginary coordinate of `f ω`.
No injectivity hypothesis is needed: a zero coordinate gives infinite index,
which is encoded as zero. -/
theorem index_range_algHom (f : QuadraticAlgebra ℤ a' b' →ₐ[ℤ] QuadraticAlgebra ℤ a b) :
    f.toRingHom.range.toAddSubgroup.index = (f omega).im.natAbs := by
  classical
  by_cases h : (f omega).im = 0
  · rw [h, Int.natAbs_zero]
    by_contra hi
    obtain ⟨n, hn, _, x, hx⟩ :=
      AddSubgroup.exists_nsmul_mem_of_index_ne_zero hi (omega : QuadraticAlgebra ℤ a b)
    have him (x : QuadraticAlgebra ℤ a' b') : (f x).im = 0 := by
      rw [← re_smul_add_im_smul x, map_add, map_smul, map_smul, map_one]
      simp [h]
    have hz : (n : ℤ) = 0 := by
      simpa [him x] using congrArg QuadraticAlgebra.im hx.symm
    exact (Nat.ne_of_gt hn) (Int.natCast_eq_zero.mp hz)
  · have hf : Function.Injective f :=
      (isRegular_im_omega_iff_injective f).mp (isRegular_iff_ne_zero.mpr h)
    let e : QuadraticAlgebra ℤ a' b' ≃ₗ[ℤ] f.toLinearMap.range :=
      LinearEquiv.ofInjective f.toLinearMap hf
    let bN : Module.Basis (Fin 2) ℤ f.toRingHom.range.toAddSubgroup :=
      (basis a' b').map e
    rw [AddSubgroup.index_eq_natAbs_det (basis a b) _ bN,
      ← det_toMatrix_algHom f, Module.Basis.det_apply]
    congr 2
    ext i j
    rw [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    exact congrArg (fun x : QuadraticAlgebra ℤ a b => ((basis a b).repr x) i)
      (congrArg Subtype.val ((basis a' b').map_apply e j))

end QuadraticAlgebra
