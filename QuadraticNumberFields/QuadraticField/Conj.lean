/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import QuadraticNumberFields.Qsqrtd.Basic
import QuadraticNumberFields.QuadraticField.Basic

/-!
# Conjugation on Quadratic Fields

This file introduces a lightweight conjugation interface for quadratic
number fields.  The goal is to provide a stable minimal layer: a class
`QuadraticField.Conj` that records a distinguished non-trivial `ℚ`-algebra
automorphism of a quadratic field, plus the standard-model construction
`Qsqrtd.starAlgEquiv` and its `Conj` instance for `Qsqrtd d` with
squarefree `d ≠ 1`.

The `Conj` class is deliberately weaker than "the field has a
non-trivial automorphism"; the `conj_ne_refl` field is here so that
applications that require a *distinguished* non-trivial involution (such
as the trace/norm-star identities in `Task 6` and the Galois-group
identification in `Task 10`/`Task 11`) can assume the automorphism is
genuinely non-trivial.

## Main Definitions

* `Qsqrtd.starAlgEquiv`: the conjugation `ℚ(√d) → ℚ(√d)` as a `ℚ`-algebra
  equivalence.
* `QuadraticField.Conj`: a class packaging a distinguished non-trivial
  `ℚ`-algebra involution on a quadratic field.
* `QuadraticField.conjAut`: the underlying `AlgEquiv` of a `Conj` instance.
* `QuadraticField.instConjQsqrtd`: the `Conj` instance for `Qsqrtd d`
  with squarefree `d ≠ 1`.

## Main Theorems

* `QuadraticField.univ_aut_eq_pair`: the `ℚ`-automorphism group of a
  quadratic field is exactly `{AlgEquiv.refl, conjAut K}`.
* `QuadraticField.add_conj_eq_trace_image`: `x + conjAut K x` is the image
  of `Algebra.trace ℚ K x`.
* `QuadraticField.mul_conj_eq_norm_image`: `x * conjAut K x` is the image
  of `Algebra.norm ℚ x`.
-/

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd` models.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticField

/-- A `Conj` structure on a quadratic field `K` is a distinguished
non-trivial `ℚ`-algebra involution on `K`.

The `conj_conj` and `conj_ne_refl` fields are here so that the
distinguished involution is genuinely non-trivial: any involution of a
quadratic field is automatically either `id` or the conjugation
(`Task 5`), so the `conj_ne_refl` field is a redundant-but-cheap
guarantee that the picked automorphism is the conjugation. -/
class Conj (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] where
  /-- The distinguished involution. -/
  conj : K ≃ₐ[ℚ] K
  /-- The involution is involutive. -/
  conj_conj : ∀ x, conj (conj x) = x
  /-- The involution is not the identity. -/
  conj_ne_refl : conj ≠ AlgEquiv.refl

/-- The distinguished `ℚ`-algebra involution associated to a `Conj`
instance. -/
abbrev conjAut (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [Conj K] : K ≃ₐ[ℚ] K :=
  Conj.conj

end QuadraticField

namespace Qsqrtd

/-! ## The Standard-Model Conjugation

The `QuadraticAlgebra R a b` model has a canonical involution given by
`(re + im · ω) ↦ (re + b · im) - im · ω`, which for our `Qsqrtd d =
QuadraticAlgebra ℚ d 0` (where `b = 0`) is the familiar conjugation
`re + im · √d ↦ re - im · √d`.  Mathlib provides the `Star`/`StarRing`
machinery for this involution; we package it here as a `ℚ`-algebra
equivalence. -/

/-- The conjugation on `Q(√d)` as a `ℚ`-algebra equivalence.  The
`[Fact (¬ IsSquare d)]` constraint ensures the `Field` instance on
`Qsqrtd d` is available, which fixes the `Semiring`/`Algebra` instances
to match the ones used by the `Conj` class. -/
noncomputable def starAlgEquiv (d : ℚ) [Fact (¬ IsSquare d)] :
    Qsqrtd d ≃ₐ[ℚ] Qsqrtd d where
  toFun := star
  invFun := star
  left_inv x := star_involutive x
  right_inv x := star_involutive x
  map_mul' := fun x y => by
    -- `star_mul` is the anti-multiplicative form; the ring is commutative,
    -- so `star y * star x = star x * star y`.
    rw [star_mul, mul_comm]
  map_add' := star_add
  commutes' := fun r => by
    -- For `Qsqrtd d = QuadraticAlgebra ℚ d 0`, the rational algebra
    -- map sends `r ↦ ⟨r, 0⟩` and `star ⟨r, 0⟩ = ⟨r, 0⟩`.
    simp

theorem starAlgEquiv_apply {d : ℚ} [Fact (¬ IsSquare d)] (x : Qsqrtd d) :
    starAlgEquiv d x = star x := by
  rfl

theorem starAlgEquiv_symm_apply {d : ℚ} [Fact (¬ IsSquare d)] (x : Qsqrtd d) :
    (starAlgEquiv d).symm x = star x := by
  rfl

end Qsqrtd

namespace QuadraticField

/-- The standard model `ℚ(√d)` carries the conjugation `Qsqrtd.starAlgEquiv`
as a `Conj` instance, for squarefree `d ≠ 1`. -/
noncomputable instance instConjQsqrtd (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Conj (Qsqrtd (d : ℚ)) where
  conj := Qsqrtd.starAlgEquiv (d : ℚ)
  conj_conj x := star_involutive x
  conj_ne_refl := by
    -- For squarefree `d ≠ 1`, `Qsqrtd d` is a field, so `star ⟨0, 1⟩ = ⟨0, -1⟩ ≠ ⟨0, 1⟩`.
    intro h
    -- If `starAlgEquiv = AlgEquiv.refl`, applying to `⟨0, 1⟩` gives `star ⟨0, 1⟩ = ⟨0, 1⟩`.
    have hsqrtd : star (⟨0, 1⟩ : Qsqrtd (d : ℚ)) = (⟨0, 1⟩ : Qsqrtd (d : ℚ)) := by
      have h' := DFunLike.congr_fun h (⟨0, 1⟩ : Qsqrtd (d : ℚ))
      simpa [Qsqrtd.starAlgEquiv_apply] using h'
    -- But `star ⟨0, 1⟩ = ⟨0, -1⟩` for `b = 0`.
    have hstar' : star (⟨0, 1⟩ : Qsqrtd (d : ℚ)) = (⟨0, -1⟩ : Qsqrtd (d : ℚ)) := by
      simp [QuadraticAlgebra.star_mk]
    -- Combining, `⟨0, 1⟩ = ⟨0, -1⟩`, so the imaginary parts satisfy `1 = -1`.
    have hcontra : (1 : ℚ) = -1 := by
      have h₁ : (⟨0, 1⟩ : Qsqrtd (d : ℚ)) = (⟨0, -1⟩ : Qsqrtd (d : ℚ)) := by
        rw [← hstar', hsqrtd]
      rw [QuadraticAlgebra.ext_iff] at h₁
      simpa using h₁
    -- `omega` doesn't see the `1 = -1` directly; extract the imaginary parts.
    have h₂ : (1 : ℚ) = -1 := by
      linarith
    exact absurd h₂ (by norm_num)

/-! ## Trace and Norm via the Distinguished Conjugation

For a quadratic field `K` over `ℚ`, the extension is Galois with group of
order two.  The distinguished involution `conjAut K` is non-trivial, so the
automorphism group is exactly `{AlgEquiv.refl, conjAut K}`.  Summing/multiplying
the Galois orbit then recovers the trace and norm. -/

section TraceNorm

variable {K : Type*} [Field K] [Algebra ℚ K] [QuadraticField K] [Conj K]

/-- The `ℚ`-automorphism group of a quadratic field is exactly the pair
`{AlgEquiv.refl, conjAut K}`. -/
theorem univ_aut_eq_pair [DecidableEq (K ≃ₐ[ℚ] K)] :
    (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {AlgEquiv.refl, conjAut K} := by
  haveI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  have hne : (AlgEquiv.refl : K ≃ₐ[ℚ] K) ≠ conjAut K := (Conj.conj_ne_refl).symm
  have hcard : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  refine (Finset.eq_univ_of_card _ ?_).symm
  rw [Finset.card_pair hne, hcard]

/-- For a quadratic field `K`, `x + conjAut K x` equals the image of the trace
`Algebra.trace ℚ K x` under the algebra map. -/
theorem add_conj_eq_trace_image (x : K) :
    x + conjAut K x = algebraMap ℚ K (Algebra.trace ℚ K x) := by
  classical
  haveI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  have hne : (AlgEquiv.refl : K ≃ₐ[ℚ] K) ≠ conjAut K := (Conj.conj_ne_refl).symm
  rw [trace_eq_sum_automorphisms, univ_aut_eq_pair, Finset.sum_pair hne]
  rfl

/-- For a quadratic field `K`, `x * conjAut K x` equals the image of the norm
`Algebra.norm ℚ x` under the algebra map. -/
theorem mul_conj_eq_norm_image (x : K) :
    x * conjAut K x = algebraMap ℚ K (Algebra.norm ℚ x) := by
  classical
  haveI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  have hne : (AlgEquiv.refl : K ≃ₐ[ℚ] K) ≠ conjAut K := (Conj.conj_ne_refl).symm
  rw [Algebra.norm_eq_prod_automorphisms, univ_aut_eq_pair, Finset.prod_pair hne]
  rfl

end TraceNorm

end QuadraticField
