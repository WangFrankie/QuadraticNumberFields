/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Qsqrtd.Basic

/-!
# Model of `ℤ[√d]`

This module provides a QA-owned model of `ℤ[√d]` based on `QuadraticAlgebra ℤ d 0`,
along with its embedding into `Q(√d)`.

This file is deliberately independent of mathlib's `_root_.Zsqrtd` (`ℤ√d`).

## Main Definitions

* `Zsqrtd d`: The ring `ℤ[√d]` as `QuadraticAlgebra ℤ d 0`.
* `Zsqrtd.sqrtd`: The distinguished element `√d`.
* `Zsqrtd.conj`: Conjugation `(a + b√d) ↦ (a - b√d)`.
* `Zsqrtd.trace`, `Zsqrtd.norm`: Trace and norm on `ℤ[√d]`.
* `Zsqrtd.toQsqrtdHom`: Ring hom embedding into `Q(√d)`.
* `Zsqrtd.halfInt`: Half-integer representative `(a' + b'√d)/2`.

## Main Theorems

* `Zsqrtd.toQsqrtdHom_injective`: The embedding is injective.
* `Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even`: Characterization of
  half-integers in the image of `Zsqrtd d`.
-/

namespace QuadraticNumberFields

/-- QA base model of `ℤ[√d]` reusing `QuadraticAlgebra`. -/
abbrev Zsqrtd (d : ℤ) : Type := QuadraticAlgebra ℤ d 0

namespace Zsqrtd

variable {d : ℤ}

/-- Integer embedding into `Zsqrtd`. -/
abbrev ofInt (n : ℤ) : Zsqrtd d := algebraMap ℤ (Zsqrtd d) n

/-- The distinguished square-root element `√d`. -/
abbrev sqrtd : Zsqrtd d := ⟨0, 1⟩

/-- Conjugation `(a + b√d) ↦ (a - b√d)`. -/
abbrev conj (z : Zsqrtd d) : Zsqrtd d := star z

/-- Extensionality: two elements of `Zsqrtd d` are equal if and only if
their real and imaginary parts are equal. -/
@[ext] theorem ext {x y : Zsqrtd d} (hre : x.re = y.re) (him : x.im = y.im) : x = y :=
  QuadraticAlgebra.ext hre him

/-- Trace API on `Zsqrtd`. -/
abbrev trace (z : Zsqrtd d) : ℤ := z.re + (star z).re

/-- Norm API on `Zsqrtd`. -/
abbrev norm (z : Zsqrtd d) : ℤ := QuadraticAlgebra.norm z

/-- The norm on `ℤ[√d]` as a `MonoidHom` to `ℤ`. -/
abbrev normHom (d : ℤ) : Zsqrtd d →* ℤ :=
  QuadraticAlgebra.norm

theorem normHom_apply (d : ℤ) (z : Zsqrtd d) :
    normHom d z = Zsqrtd.norm z :=
  rfl

/-- The norm on the unit group of `ℤ[√d]`, as a `MonoidHom` to `ℤˣ`. -/
abbrev normUnitsHom (d : ℤ) : (Zsqrtd d)ˣ →* ℤˣ :=
  Units.map (normHom d)

theorem normUnitsHom_coe (d : ℤ) (u : (Zsqrtd d)ˣ) :
    ((normUnitsHom d u : ℤˣ) : ℤ) = Zsqrtd.norm (u : Zsqrtd d) := by
  simp [normUnitsHom, normHom]

/-- Rational embedding into `Q(√d)`. -/
def toQsqrtd (z : Zsqrtd d) : Qsqrtd (d : ℚ) := ⟨(z.re : ℚ), (z.im : ℚ)⟩

/-- Rational embedding into `Q(√d)` as a ring hom. -/
def toQsqrtdHom (d : ℤ) : Zsqrtd d →+* Qsqrtd (d : ℚ) where
  toFun := fun z => ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by
    change ({ re := ((1 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 1
    rfl
  map_mul' := by
    intro x y
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
  map_zero' := by
    change ({ re := ((0 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 0
    rfl
  map_add' := by
    intro x y
    ext <;> simp

@[simp] theorem toQsqrtdHom_apply (d : ℤ) (z : Zsqrtd d) :
    toQsqrtdHom d z = toQsqrtd z := rfl

/-- The canonical map `toQsqrtdHom` is injective. -/
theorem toQsqrtdHom_injective (d : ℤ) : Function.Injective (toQsqrtdHom d) := by
  intro x y hxy
  ext
  · simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.re hxy
  · simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.im hxy

/-- Pair conversion helper for interoperability. -/
abbrev toPair (z : Zsqrtd d) : ℤ × ℤ := (z.re, z.im)

/-- Pair conversion helper for interoperability. -/
abbrev fromPair (p : ℤ × ℤ) : Zsqrtd d := ⟨p.1, p.2⟩

/-- Half-integer representative `(a' + b'√d)/2` in `Q(√d)`. -/
def halfInt (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  ⟨(a' : ℚ) / 2, (b' : ℚ) / 2⟩

/-- `halfInt` is in the image of `Zsqrtd d` iff both numerators are even. -/
theorem halfInt_mem_range_toQsqrtdHom_iff_even_even (d a' b' : ℤ) :
    (∃ z : Zsqrtd d, toQsqrtdHom d z = halfInt (d := d) a' b') ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · rintro ⟨z, hz⟩
    have hm : (a' : ℚ) / 2 = z.re := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.re hz.symm
    have hn : (b' : ℚ) / 2 = z.im := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.im hz.symm
    refine ⟨?_, ?_⟩
    · refine ⟨z.re, ?_⟩
      have hq : (a' : ℚ) = 2 * z.re := by nlinarith [hm]
      exact_mod_cast hq
    · refine ⟨z.im, ?_⟩
      have hq : (b' : ℚ) = 2 * z.im := by nlinarith [hn]
      exact_mod_cast hq
  · rintro ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext <;> simp [toQsqrtdHom, halfInt, hm, hn]

/-- The element `(a, b) : Zsqrtd d` decomposes as `a + b·√d`. -/
theorem decompose {a b : ℤ} :
    (⟨a, b⟩ : Zsqrtd d) = (a : Zsqrtd d) + sqrtd * (b : Zsqrtd d) := by
  ext <;> simp [sqrtd, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
                QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

/-- The unique ring homomorphism `Zsqrtd d →+* R` that sends `√d` to a chosen
root `r` of `X² - d` in `R`. Built on top of the `QuadraticAlgebra.lift`
universal property. -/
noncomputable def lift {R : Type*} [CommRing R] (r : R) (hd : r * r = (d : R)) :
    Zsqrtd d →+* R :=
  (QuadraticAlgebra.lift (R := ℤ) (a := d) (b := (0 : ℤ))
      ⟨r, hd.trans (by simp [Algebra.smul_def])⟩).toRingHom

theorem lift_apply {R : Type*} [CommRing R] (r : R) (hd : r * r = (d : R))
    (z : Zsqrtd d) :
    lift r hd z = (z.re : R) + (z.im : R) * r := by
  -- The `AlgHom`'s `toFun` is `fun z => z.re • (1 : R) + z.im • r`.
  -- `simp` with `Algebra.smul_def` reduces `↑z.re` to `z.re • 1` and `↑z.im * r` to `z.im • r`.
  change (QuadraticAlgebra.lift (R := ℤ) (a := d) (b := (0 : ℤ))
      ⟨r, hd.trans (by simp [Algebra.smul_def])⟩ : Zsqrtd d →ₐ[ℤ] R) z
    = (z.re : R) + (z.im : R) * r
  simp [QuadraticAlgebra.lift, Algebra.smul_def]

/-- `lift` computes on integer inputs as the obvious coercion. -/
theorem lift_intCast {R : Type*} [CommRing R] (r : R) (hd : r * r = (d : R))
    (n : ℤ) :
    lift r hd (n : Zsqrtd d) = (n : R) := by
  rw [lift_apply]
  simp

/-- The fundamental identity for `re + im` of a product in the project `Zsqrtd`. -/
theorem mul_re_add_im_eq (a b : Zsqrtd d) :
    (a * b).re + (a * b).im =
      (a.re + a.im) * (b.re + b.im) + (d - 1) * a.im * b.im := by
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  ring

/-- The fundamental identity for `re - im` of a product in the project `Zsqrtd`. -/
theorem mul_re_sub_im_eq (a b : Zsqrtd d) :
    (a * b).re - (a * b).im =
      (a.re - a.im) * (b.re - b.im) + (d - 1) * a.im * b.im := by
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  ring

/-- The real part of `(a + b√d) ^ 3` in the project `Zsqrtd` model. -/
theorem re_cube_mk (d a b : ℤ) :
    ((⟨a, b⟩ : Zsqrtd d) ^ 3).re = a ^ 3 + 3 * d * a * b ^ 2 := by
  simp [pow_succ]
  ring

/-- The imaginary part of `(a + b√d) ^ 3` in the project `Zsqrtd` model. -/
theorem im_cube_mk (d a b : ℤ) :
    ((⟨a, b⟩ : Zsqrtd d) ^ 3).im = 3 * a ^ 2 * b + d * b ^ 3 := by
  simp [pow_succ]
  ring

/-! ### Domain and no-zero-divisors for `d < 0` -/

/-- Explicit formula for the norm on `Zsqrtd d`: `‖(a, b)‖ = a² - d·b²`. -/
theorem norm_def (z : Zsqrtd d) :
    Zsqrtd.norm z = z.re * z.re - d * z.im * z.im := by
  change QuadraticAlgebra.norm z = z.re * z.re - d * z.im * z.im
  rw [QuadraticAlgebra.norm_def]
  ring

/-- The norm of the element `x + y·√d` in coordinates: `‖x + y√d‖ = x² - d·y²`. -/
@[simp]
theorem norm_mk (x y : ℤ) : Zsqrtd.norm (⟨x, y⟩ : Zsqrtd d) = x ^ 2 - d * y ^ 2 := by
  have h : Zsqrtd.norm (⟨x, y⟩ : Zsqrtd d) = x * x - d * y * y := norm_def _
  rw [h]; ring

/-- Multiplicativity of the norm on `Zsqrtd d`. -/
theorem norm_mul (a b : Zsqrtd d) :
    Zsqrtd.norm (a * b) = Zsqrtd.norm a * Zsqrtd.norm b :=
  MonoidHom.map_mul (M := Zsqrtd d) QuadraticAlgebra.norm a b

/-- Divisibility in `Zsqrtd d` descends to divisibility of integer norms. -/
theorem norm_dvd_norm_of_dvd {a b : Zsqrtd d} (h : a ∣ b) :
    Zsqrtd.norm a ∣ Zsqrtd.norm b := by
  rcases h with ⟨c, rfl⟩
  rw [Zsqrtd.norm_mul]
  exact dvd_mul_right _ _

/-- For `d < 0`, the norm of `z` is zero iff `z = 0`. -/
theorem norm_eq_zero_iff (hd : d < 0) (z : Zsqrtd d) :
    Zsqrtd.norm z = 0 ↔ z = 0 := by
  rw [norm_def]
  constructor
  · intro h
    have hre_sq : z.re * z.re = 0 := by nlinarith [h, hd, mul_self_nonneg z.im]
    have him_sq : z.im * z.im = 0 := by nlinarith [h, hd, mul_self_nonneg z.re]
    have hre : z.re = 0 := eq_zero_of_mul_self_eq_zero hre_sq
    have him : z.im = 0 := eq_zero_of_mul_self_eq_zero him_sq
    ext <;> assumption
  · rintro rfl
    simp

instance instNoZeroDivisors {d : ℤ} [Fact (d < 0)] : NoZeroDivisors (Zsqrtd d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have hnorm : Zsqrtd.norm (a * b) = 0 := by
      simp [hab, QuadraticAlgebra.norm_zero]
    have hmulnorm : Zsqrtd.norm a * Zsqrtd.norm b = 0 := by
      simpa [Zsqrtd.norm_mul] using hnorm
    rcases mul_eq_zero.mp hmulnorm with ha | hb
    · exact Or.inl ((norm_eq_zero_iff Fact.out a).1 ha)
    · exact Or.inr ((norm_eq_zero_iff Fact.out b).1 hb)

instance instIsDomain {d : ℤ} [Fact (d < 0)] : IsDomain (Zsqrtd d) :=
  NoZeroDivisors.to_isDomain (Zsqrtd d)

end Zsqrtd

/-- Candidate carrier of `ℤ[√d]` inside `Q(√d)` as a set. -/
def zsqrtdCarrierInQ (d : ℤ) : Set (Qsqrtd (d : ℚ)) :=
  Set.range (Zsqrtd.toQsqrtd (d := d))

end QuadraticNumberFields
