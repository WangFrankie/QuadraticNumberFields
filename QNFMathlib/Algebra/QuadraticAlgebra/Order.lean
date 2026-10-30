/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.Order.Basic
import QNFMathlib.Algebra.QuadraticAlgebra.Conductor
import QNFMathlib.Algebra.QuadraticAlgebra.Index
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension

/-!
# Quadratic orders

A quadratic order is a `ℤ`-order in a degree-two `ℚ`-algebra. For
`x : QuadraticAlgebra ℤ a b`, the image of `ℤ[x]` in `QuadraticAlgebra ℚ a b` is a
quadratic order exactly when `x.im ≠ 0`. The range of a model homomorphism `f` is a
quadratic order exactly when `(f omega).im ≠ 0`, or equivalently when its index is nonzero.
No domain or non-square hypothesis on `a, b` is needed: split and reducible models are included.
-/

namespace Subalgebra

/-- A quadratic order: a `ℤ`-order in a quadratic `ℚ`-algebra. The ambient algebra need not
be a field. -/
structure IsQuadraticOrder {A : Type*} [Ring A] [Algebra ℚ A] (Λ : Subalgebra ℤ A) : Prop
    extends Λ.IsOrder ℚ where
  /-- The ambient algebra has degree two over `ℚ`. -/
  isQuadraticExtension : Algebra.IsQuadraticExtension ℚ A

/-- Over a quadratic `ℚ`-algebra, quadratic orders are exactly the `ℤ`-orders. -/
theorem isQuadraticOrder_iff_isOrder {A : Type*} [Ring A] [Algebra ℚ A]
    [Algebra.IsQuadraticExtension ℚ A] (Λ : Subalgebra ℤ A) :
    Λ.IsQuadraticOrder ↔ Λ.IsOrder ℚ :=
  ⟨fun h ↦ h.toIsOrder, fun h ↦ ⟨h, inferInstance⟩⟩

end Subalgebra

namespace QuadraticAlgebra

variable {a b a' b' : ℤ}

/-- The inclusion of the integral model into the rational model, `ℤ`-linearly. -/
noncomputable abbrev toRat (a b : ℤ) : QuadraticAlgebra ℤ a b →ₐ[ℤ] QuadraticAlgebra ℚ a b :=
  IsScalarTower.toAlgHom ℤ (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)

/-- The image of `ℤ[x]` in the rational model is a quadratic order exactly when `x.im ≠ 0`.
No hypothesis on `a, b` is needed. -/
theorem isQuadraticOrder_map_adjoin_iff (x : QuadraticAlgebra ℤ a b) :
    ((Algebra.adjoin ℤ {x}).map (toRat a b)).IsQuadraticOrder ↔ x.im ≠ 0 := by
  rw [Subalgebra.isQuadraticOrder_iff_isOrder]
  constructor
  · rintro ⟨-, hspan⟩ h0
    have hle : Submodule.span ℚ (((Algebra.adjoin ℤ {x}).map (toRat a b) : Subalgebra ℤ _) :
        Set (QuadraticAlgebra ℚ a b)) ≤ LinearMap.ker ((basis (a : ℚ) b).coord 1) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have := (mem_adjoin_singleton_iff_dvd_im x y).mp hy
      rw [h0, zero_dvd_iff] at this
      simp [this]
    rw [hspan, top_le_iff] at hle
    have : (omega : QuadraticAlgebra ℚ a b) ∈ LinearMap.ker ((basis (a : ℚ) b).coord 1) := by
      rw [hle]; trivial
    simp at this
  · intro hx
    refine ⟨?_, ?_⟩
    · have : Module.Finite ℤ
          (Subalgebra.toSubmodule ((Algebra.adjoin ℤ {x}).map (toRat a b))) := by
        rw [Subalgebra.map_toSubmodule]; infer_instance
      exact this
    · rw [eq_top_iff]
      rintro z -
      have h1 : (1 : QuadraticAlgebra ℚ a b) ∈ Submodule.span ℚ
          (((Algebra.adjoin ℤ {x}).map (toRat a b) : Subalgebra ℤ _) : Set _) :=
        Submodule.subset_span (Subalgebra.one_mem _)
      have hx' : toRat a b x ∈ Submodule.span ℚ
          (((Algebra.adjoin ℤ {x}).map (toRat a b) : Subalgebra ℤ _) : Set _) :=
        Submodule.subset_span ⟨x, Algebra.self_mem_adjoin_singleton ℤ x, rfl⟩
      have hz : z = (z.re - z.im * x.re / x.im) • (1 : QuadraticAlgebra ℚ a b) +
          (z.im / x.im) • toRat a b x := by
        have : (x.im : ℚ) ≠ 0 := by exact_mod_cast hx
        ext
        · simp; field_simp; ring_nf
        · simp; field_simp
      rw [hz]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ hx')

/-- The range of a model homomorphism is a quadratic order exactly when `(f ω).im ≠ 0`;
`f` need not be injective. -/
theorem isQuadraticOrder_map_range_iff
    (f : QuadraticAlgebra ℤ a' b' →ₐ[ℤ] QuadraticAlgebra ℤ a b) :
    (f.range.map (toRat a b)).IsQuadraticOrder ↔ (f omega).im ≠ 0 := by
  rw [range_algHom_eq_adjoin, isQuadraticOrder_map_adjoin_iff]

/-- The range of a model homomorphism is a quadratic order exactly when it has finite index. -/
theorem isQuadraticOrder_map_range_iff_index_ne_zero
    (f : QuadraticAlgebra ℤ a' b' →ₐ[ℤ] QuadraticAlgebra ℤ a b) :
    (f.range.map (toRat a b)).IsQuadraticOrder ↔
      f.toRingHom.range.toAddSubgroup.index ≠ 0 := by
  rw [isQuadraticOrder_map_range_iff, index_range_algHom, Int.natAbs_ne_zero]

/-- `QuadraticAlgebra ℤ a b` is a quadratic order in `QuadraticAlgebra ℚ a b`. -/
theorem isQuadraticOrder_range_toRat (a b : ℤ) : (toRat a b).range.IsQuadraticOrder := by
  rw [← Algebra.map_top, ← adjoin_omega_eq_top, isQuadraticOrder_map_adjoin_iff]
  simp

end QuadraticAlgebra
