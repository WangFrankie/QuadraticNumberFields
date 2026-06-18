/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import QNFMathlib.RingTheory.Ideal.Span

/-!
# Generic Cox 7.7 ideal relation for `QuadraticAlgebra ℤ DD bb`

The Cox 7.7 bridge sends a binary quadratic form `A x² + B x y + C y²` of
discriminant `B² - 4AC` to the ideal `(A, β)` of the relevant order, where `β`
is the quadratic generator `⟨u, 1⟩` with `2u = -(B + bb)`.  Concretely the
imaginary-side bridge uses two orders:

* `Zsqrtd D = QuadraticAlgebra ℤ D 0`        (the `bb = 0` case);
* `ZOnePlusSqrtdOverTwo k = QuadraticAlgebra ℤ k 1`  (the `bb = 1` case).

The algebra underlying the bridge is identical in both cases: it only depends on
the linear coefficient `bb` of `QuadraticAlgebra ℤ DD bb` and the discriminant
normalisation `B² - 4AC = bb² + 4 · DD`.  This module proves the shared core once,
generic in `bb`, so the `Bridge` module can specialise it at `bb = 0` and
`bb = 1` rather than duplicating the whole computation.

All proofs reduce, via the quadratic-algebra coordinate simp set, to integer
identities closed by `linear_combination`/`ring` using the determinant relation
`p s - q r = 1`.

This material is project-local Cox-bridge infrastructure; it is not intended for
mathlib.
-/

open QuadraticAlgebra
open Module

namespace QuadraticNumberFields.CoxIdealRelation

variable {DD bb A B C p q r s u v : ℤ}

/-! ## Scalar identities

The integer identities that drive the coordinate computations.  Each follows
from substituting `B = -2u - bb` and `DD = u² + bb·u - A·C` and using the
determinant relation `p s - q r = 1`. -/

/-- Closed form for the transformed quadratic coordinate `v`. -/
theorem v_eq (hdet : p * s - q * r = 1) (hu : 2 * u = -(B + bb))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + bb)) :
    v = -A * p * q + u * (p * s + q * r) + bb * (q * r) - C * r * s := by
  have hB : B = -2 * u - bb := by omega
  apply mul_left_cancel₀ (a := (2 : ℤ)) two_ne_zero
  rw [hB] at hv
  linear_combination hv + bb * hdet

/-- The imaginary-part identity: the real coordinate of `λ = p A - r β` agrees
with the transformed first coefficient `A' = A p² + B p r + C r²`. -/
theorem lin (hdet : p * s - q * r = 1) (hu : 2 * u = -(B + bb))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + bb)) :
    p * A - r * u - bb * r = s * (A * p ^ 2 + B * p * r + C * r ^ 2) + r * v := by
  have hB : B = -2 * u - bb := by omega
  have hvd := v_eq hdet hu hv
  rw [hB, hvd]
  linear_combination (-(A * p) + u * r + bb * r) * hdet

/-- The real-part identity relating `λ`, `β'` and the transformed coefficient. -/
theorem root_re (hdet : p * s - q * r = 1)
    (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD) (hu : 2 * u = -(B + bb))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + bb)) :
    (p * A - r * u) * v - DD * r =
      (A * p ^ 2 + B * p * r + C * r ^ 2) * (s * u - q * A) := by
  have hB : B = -2 * u - bb := by omega
  have hDD : DD = u ^ 2 + bb * u - A * C := by rw [hB] at hdisc; nlinarith
  have hvd := v_eq hdet hu hv
  subst hB hDD hvd
  linear_combination (r * (u ^ 2 + bb * u - A * C)) * hdet

/-- The norm identity `N(λ) = A · A'`. -/
theorem norm_rel (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD)
    (hu : 2 * u = -(B + bb)) :
    (p * A - r * u) * (p * A - r * u - bb * r) - DD * r ^ 2 =
      A * (A * p ^ 2 + B * p * r + C * r ^ 2) := by
  have hB : B = -2 * u - bb := by omega
  have hDD : DD = u ^ 2 + bb * u - A * C := by rw [hB] at hdisc; nlinarith
  rw [hB, hDD]; ring

/-! ## Quadratic-algebra identities

The three multiplicative relations between `λ`, `α = A'`, `β = ⟨u, 1⟩` and
`β' = ⟨v, 1⟩` inside `QuadraticAlgebra ℤ DD bb`, obtained by reducing to the
scalar identities above in each coordinate. -/

/-- The root relation `λ · β' = α · (s β - q A)`. -/
theorem root_relation (hdet : p * s - q * r = 1)
    (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD) (hu : 2 * u = -(B + bb))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + bb)) :
    (((p * A : ℤ) : QuadraticAlgebra ℤ DD bb) -
          (r : QuadraticAlgebra ℤ DD bb) * (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb)) *
        (⟨v, 1⟩ : QuadraticAlgebra ℤ DD bb) =
      ((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : QuadraticAlgebra ℤ DD bb) *
        ((s : QuadraticAlgebra ℤ DD bb) * (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb) -
          (q : QuadraticAlgebra ℤ DD bb) * (A : QuadraticAlgebra ℤ DD bb)) := by
  have hl := lin hdet hu hv
  have hr := root_re hdet hdisc hu hv
  ext <;>
    simp only [re_sub, re_mul, re_intCast, im_sub, im_mul, im_intCast, zero_mul,
      mul_zero, add_zero, mul_one] <;> push_cast
  · linear_combination hr
  · linear_combination hl

/-- The conjugate relation `λ · (s A' + r β') = α · A`. -/
theorem conj_relation (hdet : p * s - q * r = 1)
    (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD) (hu : 2 * u = -(B + bb))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + bb)) :
    (((p * A : ℤ) : QuadraticAlgebra ℤ DD bb) -
          (r : QuadraticAlgebra ℤ DD bb) * (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb)) *
        (((s * (A * p ^ 2 + B * p * r + C * r ^ 2) : ℤ) : QuadraticAlgebra ℤ DD bb) +
          (r : QuadraticAlgebra ℤ DD bb) * (⟨v, 1⟩ : QuadraticAlgebra ℤ DD bb)) =
      ((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : QuadraticAlgebra ℤ DD bb) *
        (A : QuadraticAlgebra ℤ DD bb) := by
  have hl := lin hdet hu hv
  have hn := norm_rel (DD := DD) (bb := bb) (A := A) (B := B) (C := C) (p := p) (r := r)
    (u := u) hdisc hu
  ext <;>
    simp only [re_add, im_add, re_sub, re_mul, re_intCast, im_sub, im_mul, im_intCast,
      zero_mul, mul_zero, add_zero, zero_add, mul_one] <;> push_cast
  · rw [show s * (A * p ^ 2 + B * p * r + C * r ^ 2) + r * v = p * A - r * u - bb * r by
        rw [hl]]
    linear_combination hn
  · linear_combination r * hl

/-- The basis relation `λ · (p β' + q A') = α · β`. -/
theorem beta_relation (hdet : p * s - q * r = 1)
    (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD) (hu : 2 * u = -(B + bb))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + bb)) :
    (((p * A : ℤ) : QuadraticAlgebra ℤ DD bb) -
          (r : QuadraticAlgebra ℤ DD bb) * (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb)) *
        ((p : QuadraticAlgebra ℤ DD bb) * (⟨v, 1⟩ : QuadraticAlgebra ℤ DD bb) +
          (q : QuadraticAlgebra ℤ DD bb) *
            ((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : QuadraticAlgebra ℤ DD bb)) =
      ((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : QuadraticAlgebra ℤ DD bb) *
        (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb) := by
  have hl := lin hdet hu hv
  have hr := root_re hdet hdisc hu hv
  ext <;>
    simp only [re_add, im_add, re_sub, re_mul, re_intCast, im_sub, im_mul, im_intCast,
      zero_mul, mul_zero, add_zero, mul_one] <;> push_cast
  · calc
      (p * A - r * u) * (p * v + q * (A * p ^ 2 + B * p * r + C * r ^ 2)) + DD * (0 - r) * p
          = p * ((p * A - r * u) * v - DD * r) +
            q * (A * p ^ 2 + B * p * r + C * r ^ 2) * (p * A - r * u) := by ring
      _ = p * ((A * p ^ 2 + B * p * r + C * r ^ 2) * (s * u - q * A)) +
            q * (A * p ^ 2 + B * p * r + C * r ^ 2) * (p * A - r * u) := by rw [hr]
      _ = (A * p ^ 2 + B * p * r + C * r ^ 2) * (u * (p * s - q * r)) := by ring
      _ = (A * p ^ 2 + B * p * r + C * r ^ 2) * u := by rw [hdet]; ring
  · linear_combination p * hl + (A * p ^ 2 + B * p * r + C * r ^ 2) * hdet

/-- The generator `λ = p A - r β` is nonzero whenever `A ≠ 0`. -/
theorem lam_ne_zero (hA : A ≠ 0) (hdet : p * s - q * r = 1) :
    (((p * A : ℤ) : QuadraticAlgebra ℤ DD bb) -
      (r : QuadraticAlgebra ℤ DD bb) * (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb)) ≠ 0 := by
  intro hzero
  have him := congrArg QuadraticAlgebra.im hzero
  have hre := congrArg QuadraticAlgebra.re hzero
  simp only [im_sub, im_intCast, im_mul, re_intCast, re_sub, re_mul, im_zero, re_zero,
    zero_mul, mul_one, mul_zero, zero_sub, neg_eq_zero] at him hre
  have hr : r = 0 := by push_cast at him; omega
  rw [hr] at hre
  have hpA : p * A = 0 := by push_cast at hre; linarith
  rcases Int.mul_eq_zero.mp hpA with hp | hA0
  · rw [hp, hr] at hdet; simp at hdet
  · exact hA hA0

/-! ## Ideal relation -/

/-- The Cox 7.7 ideal identity in `QuadraticAlgebra ℤ DD bb`:

`(A') · (A, β) = (λ) · (A', β')`,

where `A' = A p² + B p r + C r²`, `β = ⟨u, 1⟩`, `β' = ⟨v, 1⟩` and
`λ = p A - r β`.  This is the proper-equivalence step underlying the Cox bridge,
proved once generically in the linear coefficient `bb`. -/
theorem ideal_relation (hdet : p * s - q * r = 1)
    (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD) (hu : 2 * u = -(B + bb))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + bb)) :
    Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : QuadraticAlgebra ℤ DD bb)} :
          Set (QuadraticAlgebra ℤ DD bb)) *
      Ideal.span
        ({(A : QuadraticAlgebra ℤ DD bb), (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb)} :
          Set (QuadraticAlgebra ℤ DD bb)) =
    Ideal.span
        ({(((p * A : ℤ) : QuadraticAlgebra ℤ DD bb) -
          (r : QuadraticAlgebra ℤ DD bb) * (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb))} :
          Set (QuadraticAlgebra ℤ DD bb)) *
      Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : QuadraticAlgebra ℤ DD bb),
          (⟨v, 1⟩ : QuadraticAlgebra ℤ DD bb)} : Set (QuadraticAlgebra ℤ DD bb)) := by
  let A' : ℤ := A * p ^ 2 + B * p * r + C * r ^ 2
  let α : QuadraticAlgebra ℤ DD bb := (A' : QuadraticAlgebra ℤ DD bb)
  let β : QuadraticAlgebra ℤ DD bb := ⟨u, 1⟩
  let β' : QuadraticAlgebra ℤ DD bb := ⟨v, 1⟩
  let lam : QuadraticAlgebra ℤ DD bb :=
    ((p * A : ℤ) : QuadraticAlgebra ℤ DD bb) - (r : QuadraticAlgebra ℤ DD bb) * β
  let I : Ideal (QuadraticAlgebra ℤ DD bb) :=
    Ideal.span ({(A : QuadraticAlgebra ℤ DD bb), β} : Set (QuadraticAlgebra ℤ DD bb))
  let J : Ideal (QuadraticAlgebra ℤ DD bb) := Ideal.span ({α, β'} : Set (QuadraticAlgebra ℤ DD bb))
  change Ideal.span ({α} : Set (QuadraticAlgebra ℤ DD bb)) * I =
    Ideal.span ({lam} : Set (QuadraticAlgebra ℤ DD bb)) * J
  have hroot : lam * β' = α * ((s : QuadraticAlgebra ℤ DD bb) * β -
      (q : QuadraticAlgebra ℤ DD bb) * (A : QuadraticAlgebra ℤ DD bb)) := by
    simpa [A', α, β, β', lam] using root_relation hdet hdisc hu hv
  have hconj : lam * (((s * A' : ℤ) : QuadraticAlgebra ℤ DD bb) +
      (r : QuadraticAlgebra ℤ DD bb) * β') = α * (A : QuadraticAlgebra ℤ DD bb) := by
    simpa [A', α, β, β', lam] using conj_relation hdet hdisc hu hv
  have hbeta : lam * ((p : QuadraticAlgebra ℤ DD bb) * β' +
      (q : QuadraticAlgebra ℤ DD bb) * α) = α * β := by
    simpa [A', α, β, β', lam] using beta_relation hdet hdisc hu hv
  have hA_mem_I : (A : QuadraticAlgebra ℤ DD bb) ∈ I := Ideal.subset_span (by simp)
  have hβ_mem_I : β ∈ I := Ideal.subset_span (by simp)
  have hα_mem_J : α ∈ J := Ideal.subset_span (by simp)
  have hβ'_mem_J : β' ∈ J := Ideal.subset_span (by simp)
  have hlam_mem_I : lam ∈ I := by
    have hpA_mem_I : ((p * A : ℤ) : QuadraticAlgebra ℤ DD bb) ∈ I := by
      simpa using I.mul_mem_left (p : QuadraticAlgebra ℤ DD bb) hA_mem_I
    exact I.sub_mem hpA_mem_I (I.mul_mem_left (r : QuadraticAlgebra ℤ DD bb) hβ_mem_I)
  have hsα_add_rβ'_mem_J :
      ((s * A' : ℤ) : QuadraticAlgebra ℤ DD bb) + (r : QuadraticAlgebra ℤ DD bb) * β' ∈ J := by
    have hsα_mem_J : ((s * A' : ℤ) : QuadraticAlgebra ℤ DD bb) ∈ J := by
      simpa [A', α] using J.mul_mem_left (s : QuadraticAlgebra ℤ DD bb) hα_mem_J
    exact J.add_mem hsα_mem_J (J.mul_mem_left (r : QuadraticAlgebra ℤ DD bb) hβ'_mem_J)
  have hpβ'_add_qα_mem_J :
      (p : QuadraticAlgebra ℤ DD bb) * β' + (q : QuadraticAlgebra ℤ DD bb) * α ∈ J :=
    J.add_mem (J.mul_mem_left (p : QuadraticAlgebra ℤ DD bb) hβ'_mem_J)
      (J.mul_mem_left (q : QuadraticAlgebra ℤ DD bb) hα_mem_J)
  have hsβ_sub_qA_mem_I :
      (s : QuadraticAlgebra ℤ DD bb) * β -
        (q : QuadraticAlgebra ℤ DD bb) * (A : QuadraticAlgebra ℤ DD bb) ∈ I :=
    I.sub_mem (I.mul_mem_left (s : QuadraticAlgebra ℤ DD bb) hβ_mem_I)
      (I.mul_mem_left (q : QuadraticAlgebra ℤ DD bb) hA_mem_I)
  apply le_antisymm
  · apply Ideal.span_singleton_mul_span_pair_le
    · rw [← hconj]
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp [lam])) hsα_add_rβ'_mem_J
    · rw [← hbeta]
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp [lam])) hpβ'_add_qα_mem_J
  · apply Ideal.span_singleton_mul_span_pair_le
    · have hα_mem_left : α * lam ∈ Ideal.span ({α} : Set (QuadraticAlgebra ℤ DD bb)) * I :=
        Ideal.mul_mem_mul (Ideal.subset_span (by simp [α])) hlam_mem_I
      simpa [mul_comm] using hα_mem_left
    · rw [hroot]
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp [α])) hsβ_sub_qA_mem_I

/-! ## Generic Cox ℤ-basis

The Cox ideal `(A, ⟨u, 1⟩)` is a free `ℤ`-module of rank `2` with basis
`{A, coxBeta}`, where `coxBeta = ⟨-u, -1⟩ = -⟨u, 1⟩`.  This is the integral
backbone of the left-inverse round-trip, shared by the `bb = 0` (`Zsqrtd`) and
`bb = 1` (`ZOnePlusSqrtdOverTwo`) specialisations: each branch transports this
basis to `𝓞K` and reads off its `K`-coordinates. -/

/-- The second Cox `ℤ`-basis generator, the negated quadratic generator `-⟨u, 1⟩`. -/
def coxBeta (DD bb u : ℤ) : QuadraticAlgebra ℤ DD bb := ⟨-u, -1⟩

@[simp] theorem coxBeta_re (DD bb u : ℤ) : (coxBeta DD bb u).re = -u := rfl

@[simp] theorem coxBeta_im (DD bb u : ℤ) : (coxBeta DD bb u).im = -1 := rfl

theorem coxBeta_eq_neg (DD bb u : ℤ) :
    coxBeta DD bb u = -(⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb) := by
  apply QuadraticAlgebra.ext <;> simp [coxBeta]

/-- The Cox ideal `(A, ⟨u, 1⟩)` of `QuadraticAlgebra ℤ DD bb`. -/
def coxIdeal (DD bb A u : ℤ) : Ideal (QuadraticAlgebra ℤ DD bb) :=
  Ideal.span ({(A : QuadraticAlgebra ℤ DD bb), (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb)} :
    Set (QuadraticAlgebra ℤ DD bb))

theorem self_mem_coxIdeal (DD bb A u : ℤ) :
    (A : QuadraticAlgebra ℤ DD bb) ∈ coxIdeal DD bb A u :=
  Ideal.subset_span (by simp)

theorem coxBeta_mem_coxIdeal (DD bb A u : ℤ) :
    coxBeta DD bb u ∈ coxIdeal DD bb A u := by
  rw [coxBeta_eq_neg]
  exact Submodule.neg_mem _ (Ideal.subset_span (by simp))

/-- Every element of the Cox ideal `(A, ⟨u, 1⟩)` is a `ℤ`-linear combination of
`{A, coxBeta}`, provided the discriminant normalisation `B² - 4AC = bb² + 4DD`
and the root relation `2u = -(B + bb)` hold.  The integer coefficients are
`m = x₁ - u·x₂ - C·y₂` and `n = -(x₂·A + y₁ + y₂·u + bb·y₂)`, where
`x = ⟨x₁, x₂⟩`, `y = ⟨y₁, y₂⟩` express the ideal membership `z = x·A + y·⟨u,1⟩`;
integrality of the leading coefficient uses `DD = u² + bb·u - A·C`. -/
theorem mem_span_coxBeta_of_mem_coxIdeal {DD bb A B C u : ℤ}
    (hu : 2 * u = -(B + bb)) (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD)
    {z : QuadraticAlgebra ℤ DD bb} (hz : z ∈ coxIdeal DD bb A u) :
    z ∈ Submodule.span ℤ ({(A : QuadraticAlgebra ℤ DD bb), coxBeta DD bb u} :
      Set (QuadraticAlgebra ℤ DD bb)) := by
  have hDD : DD = u ^ 2 + bb * u - A * C := by
    have hB : B = -2 * u - bb := by omega
    rw [hB] at hdisc; nlinarith
  rcases (Ideal.mem_span_pair).mp hz with ⟨x, y, hz⟩
  rw [← hz]
  set x₁ := x.re with hx₁
  set x₂ := x.im with hx₂
  set y₁ := y.re with hy₁
  set y₂ := y.im with hy₂
  have hx : x = (⟨x₁, x₂⟩ : QuadraticAlgebra ℤ DD bb) := by apply QuadraticAlgebra.ext <;> rfl
  have hy : y = (⟨y₁, y₂⟩ : QuadraticAlgebra ℤ DD bb) := by apply QuadraticAlgebra.ext <;> rfl
  rw [hx, hy]
  set m : ℤ := x₁ - u * x₂ - C * y₂ with hm
  set n : ℤ := -(x₂ * A + y₁ + y₂ * u + bb * y₂) with hn
  have hsum : (m • (A : QuadraticAlgebra ℤ DD bb) + n • coxBeta DD bb u) =
      (⟨x₁, x₂⟩ : QuadraticAlgebra ℤ DD bb) * (A : QuadraticAlgebra ℤ DD bb) +
      (⟨y₁, y₂⟩ : QuadraticAlgebra ℤ DD bb) * (⟨u, 1⟩ : QuadraticAlgebra ℤ DD bb) := by
    rw [hm, hn]
    apply QuadraticAlgebra.ext
    · simp only [zsmul_eq_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, QuadraticAlgebra.mk_mul_mk,
        coxBeta_re, coxBeta_im, mul_zero, mul_one, zero_mul, add_zero]
      push_cast
      linear_combination (-y₂) * hDD
    · simp only [zsmul_eq_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, QuadraticAlgebra.mk_mul_mk,
        coxBeta_re, coxBeta_im, mul_zero, mul_one, zero_mul, add_zero, zero_add]
      push_cast
      ring
  rw [← hsum]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The `ℤ`-basis `{A, coxBeta}` of the Cox ideal `(A, ⟨u, 1⟩)`. -/
noncomputable def coxIdealBasis {DD bb A B C u : ℤ} (hA : A ≠ 0)
    (hu : 2 * u = -(B + bb)) (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD) :
    Basis (Fin 2) ℤ (coxIdeal DD bb A u) := by
  let v0 : coxIdeal DD bb A u := ⟨(A : QuadraticAlgebra ℤ DD bb), self_mem_coxIdeal DD bb A u⟩
  let v1 : coxIdeal DD bb A u := ⟨coxBeta DD bb u, coxBeta_mem_coxIdeal DD bb A u⟩
  refine Basis.mk (v := ![v0, v1]) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro g hsum
    have hzero : g 0 • (A : QuadraticAlgebra ℤ DD bb) + g 1 • coxBeta DD bb u = 0 := by
      have hsum' := congrArg Subtype.val hsum
      simpa [v0, v1] using hsum'
    have him : (g 0 • (A : QuadraticAlgebra ℤ DD bb) + g 1 • coxBeta DD bb u).im = 0 := by
      rw [hzero]; rfl
    have him_eq : -g 1 = 0 := by
      simpa [coxBeta] using him
    have hg1 : g 1 = 0 := by linarith
    have hre : (g 0 • (A : QuadraticAlgebra ℤ DD bb) + g 1 • coxBeta DD bb u).re = 0 := by
      rw [hzero]; rfl
    rw [hg1] at hre
    have hmul : g 0 * A = 0 := by
      simpa using hre
    have hg0 : g 0 = 0 := by
      exact Or.resolve_right (Int.eq_zero_or_eq_zero_of_mul_eq_zero hmul) hA
    intro i; fin_cases i <;> assumption
  · intro x _
    have h_span := mem_span_coxBeta_of_mem_coxIdeal hu hdisc x.2
    rcases Submodule.mem_span_insert.mp h_span with ⟨m, z, hz, hz_eq⟩
    rcases Submodule.mem_span_singleton.mp hz with ⟨n, hn⟩
    have h_val : (x : QuadraticAlgebra ℤ DD bb) =
        m • (A : QuadraticAlgebra ℤ DD bb) + n • coxBeta DD bb u := by
      rw [hz_eq, hn]
    have h_sub_val :
        (m • v0 + n • v1 : coxIdeal DD bb A u).val =
          (x : QuadraticAlgebra ℤ DD bb) := by
      simp [v0, v1, h_val]
    have h_eq : m • v0 + n • v1 = x := Subtype.ext h_sub_val
    rw [← h_eq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The value of the generic Cox basis at index 0 is the scalar `A`. -/
theorem coxIdealBasis_val_0 {DD bb A B C u : ℤ} (hA : A ≠ 0)
    (hu : 2 * u = -(B + bb)) (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD) :
    ((coxIdealBasis hA hu hdisc) 0 : QuadraticAlgebra ℤ DD bb) =
      (A : QuadraticAlgebra ℤ DD bb) := by
  unfold coxIdealBasis; simp

/-- The value of the generic Cox basis at index 1 is `coxBeta`. -/
theorem coxIdealBasis_val_1 {DD bb A B C u : ℤ} (hA : A ≠ 0)
    (hu : 2 * u = -(B + bb)) (hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD) :
    ((coxIdealBasis hA hu hdisc) 1 : QuadraticAlgebra ℤ DD bb) =
      coxBeta DD bb u := by
  unfold coxIdealBasis; simp

end QuadraticNumberFields.CoxIdealRelation
