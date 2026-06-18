/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

General ideal membership, primality, and quotient results for the project-owned
`Zsqrtd d` (i.e., `QuadraticAlgebra ℤ d 0`).
-/
import QuadraticNumberFields.Zsqrtd.Basic
import QNFMathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideal Theory for the project `Zsqrtd d`

This module provides the general ideal-span results for the project-owned
`Zsqrtd d := QuadraticAlgebra ℤ d 0`. It mirrors the corresponding mathlib
`Zsqrtd.Ideal` API but is keyed off the project model.

## Main Results

### General theory for any prime `p` with `p ∣ (d - 1)`

* `Zsqrtd.Ideal.mem_span_p_one_minus_sqrtd_iff`:
  `z ∈ (p, 1-√d) ↔ p ∣ (z.re + z.im)`
* `Zsqrtd.Ideal.mem_span_p_one_plus_sqrtd_iff`:
  `z ∈ (p, 1+√d) ↔ p ∣ (z.re - z.im)`
* `Zsqrtd.Ideal.isPrime_span_p_one_minus_sqrtd`: `(p, 1-√d)` is prime
* `Zsqrtd.Ideal.isPrime_span_p_one_plus_sqrtd`: `(p, 1+√d)` is prime
* `Zsqrtd.Ideal.liftModP`: `Zsqrtd d →+* ZMod p` sending `√d ↦ 1`
* `Zsqrtd.Ideal.liftModPNeg`: `Zsqrtd d →+* ZMod p` sending `√d ↦ -1`
* `Zsqrtd.Ideal.quotEquivZModP`: `Zsqrtd d ⧸ (p, 1-√d) ≃+* ZMod p`
* `Zsqrtd.Ideal.quotEquivZModPNeg`: `Zsqrtd d ⧸ (p, 1+√d) ≃+* ZMod p`
* `Zsqrtd.Ideal.comap_span_p_one_minus_sqrtd`: `comap algebraMap (p, 1-√d) = (p)`
* `Zsqrtd.Ideal.comap_span_p_one_plus_sqrtd`: `comap algebraMap (p, 1+√d) = (p)`

### Utility lemmas

The general ideal-span helper used in this file is imported from
`QNFMathlib.RingTheory.Ideal.Span`.
-/

open Ideal

open scoped QuadraticAlgebra

namespace QuadraticNumberFields

namespace Zsqrtd

namespace Ideal

variable (d : ℤ)

@[simp] lemma algebraMap_int_coe (n : ℤ) : algebraMap ℤ (Zsqrtd d) n = n := rfl

lemma map_span_int_singleton (n : ℤ) :
    Ideal.map (algebraMap ℤ (Zsqrtd d)) (Ideal.span {n}) = Ideal.span {(n : Zsqrtd d)} := by
  rw [Ideal.map_span, Set.image_singleton, algebraMap_int_coe]

variable {d}

private lemma prime_int_not_isUnit (p : ℕ) [Fact p.Prime] : ¬ IsUnit (p : ℤ) := by
  intro hunit
  exact absurd (Int.isUnit_iff.mp hunit) (by
    have hp := (Fact.out : p.Prime).one_lt
    omega)

private lemma not_top_of_one_mem_dvd_one
    (p : ℕ) [Fact p.Prime] {I : Ideal (Zsqrtd d)}
    (hcrit : (1 : Zsqrtd d) ∈ I → (p : ℤ) ∣ 1) :
  I ≠ ⊤ := by
  intro hI
  have hpunit : IsUnit (p : ℤ) := isUnit_of_dvd_one (hcrit (by simp [hI]))
  exact prime_int_not_isUnit p hpunit

private lemma ker_eq_of_apply_eq_intCast
    (p : ℕ) [Fact p.Prime] (f : Zsqrtd d →+* ZMod p) (I : Ideal (Zsqrtd d))
    (coord : Zsqrtd d → ℤ)
    (hf : ∀ z, f z = (coord z : ZMod p))
    (hI : ∀ z, z ∈ I ↔ (p : ℤ) ∣ coord z) :
    RingHom.ker f = I := by
  ext z
  constructor
  · intro hz
    rw [RingHom.mem_ker, hf] at hz
    exact (hI z).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hz)
  · intro hz
    rw [RingHom.mem_ker, hf]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 ((hI z).1 hz)

private lemma comap_eq_span_singleton_of_mem_iff_dvd
    (p : ℕ) [Fact p.Prime] (I : Ideal (Zsqrtd d))
    (coord : Zsqrtd d → ℤ)
    (hI : ∀ z, z ∈ I ↔ (p : ℤ) ∣ coord z)
    (hcoord_intCast : ∀ z : ℤ, coord (z : Zsqrtd d) = z) :
    Ideal.comap (algebraMap ℤ (Zsqrtd d)) I =
      (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ) := by
  ext z
  constructor
  · intro hz
    change ((z : Zsqrtd d) ∈ I) at hz
    have hz' : (p : ℤ) ∣ coord (z : Zsqrtd d) := (hI (z : Zsqrtd d)).1 hz
    rw [Ideal.mem_span_singleton]
    simpa [hcoord_intCast z] using hz'
  · intro hz
    change ((z : Zsqrtd d) ∈ I)
    have hz' : (p : ℤ) ∣ coord (z : Zsqrtd d) := by
      simpa [hcoord_intCast z, Ideal.mem_span_singleton] using hz
    exact (hI (z : Zsqrtd d)).2 hz'

private noncomputable def quotEquivZModOfKerEq
    (p : ℕ) [Fact p.Prime] (f : Zsqrtd d →+* ZMod p) (I : Ideal (Zsqrtd d))
    (hker : RingHom.ker f = I) :
    (Zsqrtd d ⧸ I) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := f) (ZMod.ringHom_surjective f))

private lemma d_cast_zmodp_eq_one (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    (d : ZMod p) = 1 := by
  have h : ((d - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
  have h2 : (d : ZMod p) - 1 = 0 := by push_cast at h; exact h
  exact sub_eq_zero.mp h2

private lemma prime_dvd_or_dvd_of_dvd_mul_add
    (p : ℕ) [Fact p.Prime] {x y corr : ℤ}
    (hxy : (p : ℤ) ∣ x * y + corr) (hcorr : (p : ℤ) ∣ corr) :
    (p : ℤ) ∣ x ∨ (p : ℤ) ∣ y := by
  have hprod : (p : ℤ) ∣ x * y := by
    obtain ⟨k1, hk1⟩ := hxy
    obtain ⟨k2, hk2⟩ := hcorr
    exact ⟨k1 - k2, by linarith⟩
  exact (Nat.prime_iff_prime_int.mp Fact.out).dvd_or_dvd hprod

/-- The ring hom `Zsqrtd d →+* ℤ/pℤ` sending `√d ↦ 1`, valid when `p ∣ (d - 1)`
(since `1² = 1 ≡ d (mod p)`). -/
noncomputable def liftModP (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    Zsqrtd d →+* ZMod p :=
  Zsqrtd.lift (1 : ZMod p) (by simp [d_cast_zmodp_eq_one p hd])

lemma liftModP_apply (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) (z : Zsqrtd d) :
    liftModP p hd z = (z.re + z.im : ZMod p) := by
  simp [liftModP, Zsqrtd.lift_apply]

/-- The ring hom `Zsqrtd d →+* ℤ/pℤ` sending `√d ↦ -1`, valid when `p ∣ (d - 1)`
(since `(-1)² = 1 ≡ d (mod p)`). -/
noncomputable def liftModPNeg (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    Zsqrtd d →+* ZMod p :=
  Zsqrtd.lift (-1 : ZMod p) (by simp [d_cast_zmodp_eq_one p hd])

lemma liftModPNeg_apply (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) (z : Zsqrtd d) :
    liftModPNeg p hd z = (z.re - z.im : ZMod p) := by
  simp [liftModPNeg, Zsqrtd.lift_apply, sub_eq_add_neg]

/-- An element of `Zsqrtd d` belongs to `(p, 1-√d)` iff `p ∣ (re + im)`,
provided `p ∣ (d - 1)` for a prime `p`. -/
@[nolint unusedArguments]
lemma mem_span_p_one_minus_sqrtd_iff (p : ℕ) [Fact p.Prime]
    (hd : (p : ℤ) ∣ (d - 1)) (z : Zsqrtd d) :
    z ∈ (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) ↔
      (p : ℤ) ∣ (z.re + z.im) := by
  obtain ⟨c, hc⟩ := hd
  constructor
  · -- (⇒) If z = a·p + b·(1-√d), show p ∣ (re + im)
    intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg QuadraticAlgebra.re hab
    have him := congr_arg QuadraticAlgebra.im hab
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
               QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
               sqrtd, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast] at hre him
    norm_num at hre him
    -- z.re + z.im = p*(a.re + a.im) + (1-d)*b.im = p*(a.re + a.im - c*b.im)
    have hdb : d * b.im = (↑p * c + 1) * b.im := by congr 1; linarith
    exact ⟨a.re + a.im - c * b.im, by linarith⟩
  · -- (⇐) Given p | (re + im), construct a = ⟨k, 0⟩, b = ⟨-im, 0⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k, 0⟩, ⟨-z.im, 0⟩, ?_⟩
    ext
    · simp [sqrtd, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]; linarith
    · simp [sqrtd, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]

/-- An element of `Zsqrtd d` belongs to `(p, 1+√d)` iff `p ∣ (re - im)`,
provided `p ∣ (d - 1)` for a prime `p`. -/
@[nolint unusedArguments]
lemma mem_span_p_one_plus_sqrtd_iff (p : ℕ) [Fact p.Prime]
    (hd : (p : ℤ) ∣ (d - 1)) (z : Zsqrtd d) :
    z ∈ (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) ↔
      (p : ℤ) ∣ (z.re - z.im) := by
  obtain ⟨c, hc⟩ := hd
  constructor
  · -- (⇒) If z = a·p + b·(1+√d), show p ∣ (re - im)
    intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg QuadraticAlgebra.re hab
    have him := congr_arg QuadraticAlgebra.im hab
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
               QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
               sqrtd, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast] at hre him
    norm_num at hre him
    -- z.re - z.im = p*(a.re - a.im) + (d-1)*b.im = p*(a.re - a.im + c*b.im)
    have hdb : d * b.im = (↑p * c + 1) * b.im := by congr 1; linarith
    exact ⟨a.re - a.im + c * b.im, by linarith⟩
  · -- (⇐) Given p | (re - im), construct a = ⟨k, 0⟩, b = ⟨im, 0⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k, 0⟩, ⟨z.im, 0⟩, ?_⟩
    ext
    · simp [sqrtd, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]; linarith
    · simp [sqrtd, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]

/-- The ideal `(p, 1-√d)` is prime in `Zsqrtd d` when `p ∣ (d - 1)` for a prime `p`. -/
theorem isPrime_span_p_one_minus_sqrtd (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    IsPrime (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · refine not_top_of_one_mem_dvd_one p
      (I := (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d)))) ?_
    intro h1
    rw [mem_span_p_one_minus_sqrtd_iff p hd] at h1
    simpa using h1
  · intro a b hab
    simp only [mem_span_p_one_minus_sqrtd_iff p hd] at hab ⊢
    rw [Zsqrtd.mul_re_add_im_eq] at hab
    obtain ⟨c, hc⟩ := hd
    have hcorr : ((p : ℤ) ∣ (d - 1) * a.im * b.im) :=
      ⟨c * a.im * b.im, by rw [hc]; ring⟩
    exact prime_dvd_or_dvd_of_dvd_mul_add p hab hcorr

/-- The ideal `(p, 1+√d)` is prime in `Zsqrtd d` when `p ∣ (d - 1)` for a prime `p`. -/
theorem isPrime_span_p_one_plus_sqrtd (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    IsPrime (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · refine not_top_of_one_mem_dvd_one p
      (I := (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)))) ?_
    intro h1
    rw [mem_span_p_one_plus_sqrtd_iff p hd] at h1
    simpa using h1
  · intro a b hab
    simp only [mem_span_p_one_plus_sqrtd_iff p hd] at hab ⊢
    rw [Zsqrtd.mul_re_sub_im_eq] at hab
    obtain ⟨c, hc⟩ := hd
    have hcorr : ((p : ℤ) ∣ (d - 1) * a.im * b.im) :=
      ⟨c * a.im * b.im, by rw [hc]; ring⟩
    exact prime_dvd_or_dvd_of_dvd_mul_add p hab hcorr

lemma ker_liftModP (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    RingHom.ker (liftModP p hd) =
      (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d))) := by
  refine ker_eq_of_apply_eq_intCast p (liftModP p hd)
      (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d)))
      (fun z => z.re + z.im) ?_ ?_
  · intro z
    simpa [Int.cast_add] using liftModP_apply p hd z
  · intro z
    exact mem_span_p_one_minus_sqrtd_iff p hd z

lemma ker_liftModPNeg (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    RingHom.ker (liftModPNeg p hd) =
      (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d))) := by
  refine ker_eq_of_apply_eq_intCast p (liftModPNeg p hd)
      (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)))
      (fun z => z.re - z.im) ?_ ?_
  · intro z
    simpa [Int.cast_sub] using liftModPNeg_apply p hd z
  · intro z
    exact mem_span_p_one_plus_sqrtd_iff p hd z

/-- `Zsqrtd d ⧸ (p, 1-√d) ≃+* ℤ/pℤ` when `p ∣ (d - 1)` for a prime `p`. -/
noncomputable def quotEquivZModP (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    (Zsqrtd d) ⧸ (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d))) ≃+* ZMod p :=
  quotEquivZModOfKerEq p (liftModP p hd)
    (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d)))
    (ker_liftModP p hd)

/-- `Zsqrtd d ⧸ (p, 1+√d) ≃+* ℤ/pℤ` when `p ∣ (d - 1)` for a prime `p`. -/
noncomputable def quotEquivZModPNeg (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    (Zsqrtd d) ⧸ (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d))) ≃+* ZMod p :=
  quotEquivZModOfKerEq p (liftModPNeg p hd)
    (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)))
    (ker_liftModPNeg p hd)

lemma comap_span_p_one_minus_sqrtd (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    Ideal.comap (algebraMap ℤ (Zsqrtd d))
      (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d))) =
      (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ) := by
  refine comap_eq_span_singleton_of_mem_iff_dvd p
      (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d)))
      (fun z => z.re + z.im) ?_ ?_
  · intro z
    exact mem_span_p_one_minus_sqrtd_iff p hd z
  · intro z
    simp [QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

lemma comap_span_p_one_plus_sqrtd (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    Ideal.comap (algebraMap ℤ (Zsqrtd d))
      (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d))) =
      (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ) := by
  refine comap_eq_span_singleton_of_mem_iff_dvd p
      (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)))
      (fun z => z.re - z.im) ?_ ?_
  · intro z
    exact mem_span_p_one_plus_sqrtd_iff p hd z
  · intro z
    simp [QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

/-! ## Explicit factorization of rational primes -/

/-- Divisibility by a rational integer in `Zsqrtd d` is coordinatewise:
`(n : Zsqrtd d) ∣ w ↔ n ∣ w.re ∧ n ∣ w.im`. -/
lemma intCast_dvd_iff (n : ℤ) (w : Zsqrtd d) :
    (n : Zsqrtd d) ∣ w ↔ n ∣ w.re ∧ n ∣ w.im := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z.re, ?_⟩, ⟨z.im, ?_⟩⟩ <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    exact ⟨⟨r, i⟩, by ext <;> simp [hr, hi]⟩

/-- Explicit split-type factorization of an odd prime: for an odd prime `p` with
`p ∣ (d - 1)`, the rational prime factors as
`(p) = (p, 1 + √d) · (p, 1 - √d)` in `Zsqrtd d`.

This generalizes concrete computations such as `(3) = (3, 1+√-5)(3, 1-√-5)`.
The oddness of `p` is essential: at `p = 2` the two ideals coincide and the
product becomes a square (see `span_two_eq_sq`). -/
theorem span_p_eq_span_mul_span (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hd : (p : ℤ) ∣ (d - 1)) :
    Ideal.span ({(p : Zsqrtd d)} : Set (Zsqrtd d)) =
      (Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d))) *
        (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d))) := by
  set I : Ideal (Zsqrtd d) :=
    Ideal.span ({(p : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)) with hI
  set K : Ideal (Zsqrtd d) :=
    Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d)) with hK
  have hnp2 : ¬ (p : ℤ) ∣ 2 := by
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast hdvd))
  apply le_antisymm
  · -- `(p) ⊆ I * K`, witnessed by `p = p² · s + p(1+√d) · t + p(1-√d) · t` with `ps + 2t = 1`.
    rw [Ideal.span_singleton_le_iff_mem]
    have hpI : (p : Zsqrtd d) ∈ I := Ideal.subset_span (by simp)
    have hpK : (p : Zsqrtd d) ∈ K := Ideal.subset_span (by simp)
    have hoI : (1 + sqrtd : Zsqrtd d) ∈ I := Ideal.subset_span (by simp)
    have hoK : (1 - sqrtd : Zsqrtd d) ∈ K := Ideal.subset_span (by simp)
    have g1 : (p : Zsqrtd d) * (p : Zsqrtd d) ∈ I * K := Ideal.mul_mem_mul hpI hpK
    have g2 : (1 + sqrtd : Zsqrtd d) * (p : Zsqrtd d) ∈ I * K := Ideal.mul_mem_mul hoI hpK
    have g3 : (p : Zsqrtd d) * (1 - sqrtd) ∈ I * K := Ideal.mul_mem_mul hpI hoK
    obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two Fact.out hp2
    have hpcast : (p : Zsqrtd d) = 2 * (k : Zsqrtd d) + 1 := by
      have h : (p : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
      have := congrArg (fun z : ℤ => (z : Zsqrtd d)) h
      push_cast at this ⊢; exact this
    have hcomb : (p : Zsqrtd d) =
        1 * ((p : Zsqrtd d) * (p : Zsqrtd d))
        + (-(k : Zsqrtd d)) * ((1 + sqrtd) * (p : Zsqrtd d))
        + (-(k : Zsqrtd d)) * ((p : Zsqrtd d) * (1 - sqrtd)) := by
      rw [hpcast]; ring
    rw [hcomb]
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ g1) (Ideal.mul_mem_left _ _ g2))
      (Ideal.mul_mem_left _ _ g3)
  · -- `I * K ⊆ (p)`: any product `x * y` with `x ∈ I`, `y ∈ K` is divisible by `p`.
    rw [Ideal.mul_le]
    intro x hx y hy
    rw [hI, mem_span_p_one_plus_sqrtd_iff p hd] at hx
    rw [hK, mem_span_p_one_minus_sqrtd_iff p hd] at hy
    rw [Ideal.mem_span_singleton]
    have hcast : ((p : ℤ) : Zsqrtd d) = (p : Zsqrtd d) := by push_cast; ring
    rw [← hcast, intCast_dvd_iff]
    obtain ⟨ax, hax⟩ := hx
    obtain ⟨bb, hbb⟩ := hy
    obtain ⟨c, hc⟩ := hd
    have hsub : (p : ℤ) ∣ ((x * y).re - (x * y).im) := by
      rw [mul_re_sub_im_eq]
      exact ⟨ax * (y.re - y.im) + c * x.im * y.im, by rw [hax, hc]; ring⟩
    have hadd : (p : ℤ) ∣ ((x * y).re + (x * y).im) := by
      rw [mul_re_add_im_eq]
      exact ⟨(x.re + x.im) * bb + c * x.im * y.im, by rw [hbb, hc]; ring⟩
    refine ⟨?_, ?_⟩
    · have h2 : (p : ℤ) ∣ 2 * (x * y).re := by
        have he : 2 * (x * y).re = ((x * y).re + (x * y).im) + ((x * y).re - (x * y).im) := by ring
        rw [he]; exact dvd_add hadd hsub
      exact ((Nat.prime_iff_prime_int.mp Fact.out).dvd_or_dvd h2).resolve_left hnp2
    · have h2 : (p : ℤ) ∣ 2 * (x * y).im := by
        have he : 2 * (x * y).im = ((x * y).re + (x * y).im) - ((x * y).re - (x * y).im) := by ring
        rw [he]; exact dvd_sub hadd hsub
      exact ((Nat.prime_iff_prime_int.mp Fact.out).dvd_or_dvd h2).resolve_left hnp2

/-- Explicit ramified factorization of `2`: when `d ≡ 3 (mod 4)`, the rational
prime `2` is the square of the prime `(2, 1 + √d)` in `Zsqrtd d`:
`(2) = (2, 1 + √d)²`.

This generalizes the concrete identity `(2) = (2, 1+√-5)²`. The congruence
`d ≡ 3 (mod 4)` is exactly the condition for the equality: at `d ≡ 1 (mod 4)`
the order `Zsqrtd d` is non-maximal at `2` and `(2, 1+√d)² = 2·(2, 1+√d) ⊊ (2)`. -/
theorem span_two_eq_sq (hd4 : d % 4 = 3) :
    Ideal.span ({(2 : Zsqrtd d)} : Set (Zsqrtd d)) =
      (Ideal.span ({(2 : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d))) ^ 2 := by
  have hd2 : (2 : ℤ) ∣ (d - 1) := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Ideal (Zsqrtd d) :=
    Ideal.span ({(2 : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)) with hI
  have e2 : ((2 : ℕ) : Zsqrtd d) = (2 : Zsqrtd d) := by push_cast; ring
  -- Membership in `I` controls `re - im` modulo `2`, via the general prime API at `p = 2`.
  have key : ∀ z : Zsqrtd d, z ∈ I → (2 : ℤ) ∣ (z.re - z.im) := by
    intro z hz
    have hz' : z ∈ Ideal.span ({((2 : ℕ) : Zsqrtd d), 1 + sqrtd} : Set (Zsqrtd d)) := by rwa [e2]
    simpa using (mem_span_p_one_plus_sqrtd_iff (2 : ℕ) hd2 z).1 hz'
  rw [pow_two]
  apply le_antisymm
  · -- `(2) ⊆ I²`, witnessed by `2 = (1+√d)² − 2(1+√d) − m·4` with `d = 4m + 3`.
    rw [Ideal.span_singleton_le_iff_mem]
    have h2I : (2 : Zsqrtd d) ∈ I := Ideal.subset_span (by simp)
    have hoI : (1 + sqrtd : Zsqrtd d) ∈ I := Ideal.subset_span (by simp)
    have g1 : (2 : Zsqrtd d) * (2 : Zsqrtd d) ∈ I * I := Ideal.mul_mem_mul h2I h2I
    have g2 : (2 : Zsqrtd d) * (1 + sqrtd) ∈ I * I := Ideal.mul_mem_mul h2I hoI
    have g3 : (1 + sqrtd : Zsqrtd d) * (1 + sqrtd) ∈ I * I := Ideal.mul_mem_mul hoI hoI
    obtain ⟨m, hm⟩ : ∃ m : ℤ, d = 4 * m + 3 := ⟨d / 4, by omega⟩
    have hmc : (d : Zsqrtd d) = 4 * (m : Zsqrtd d) + 3 := by
      have := congrArg (fun z : ℤ => (z : Zsqrtd d)) hm
      push_cast at this ⊢; exact this
    have hcomb : (2 : Zsqrtd d) =
        (-(m : Zsqrtd d)) * ((2 : Zsqrtd d) * 2)
        + (-1) * ((2 : Zsqrtd d) * (1 + sqrtd))
        + 1 * ((1 + sqrtd) * (1 + sqrtd)) := by
      ext <;>
        simp [sqrtd, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]
      nlinarith [congrArg QuadraticAlgebra.re hmc, congrArg QuadraticAlgebra.im hmc]
    rw [hcomb]
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ g1) (Ideal.mul_mem_left _ _ g2))
      (Ideal.mul_mem_left _ _ g3)
  · -- `I² ⊆ (2)`: both coordinates of `x * y` are even when `x, y ∈ I`.
    rw [Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_span_singleton]
    have hcast : ((2 : ℤ) : Zsqrtd d) = (2 : Zsqrtd d) := by push_cast; ring
    rw [← hcast, intCast_dvd_iff]
    obtain ⟨ax, hax⟩ := key x hx
    obtain ⟨ay, hay⟩ := key y hy
    obtain ⟨c, hc⟩ := hd2
    have ex : x.re = x.im + 2 * ax := by linarith
    have ey : y.re = y.im + 2 * ay := by linarith
    have ed : d = 2 * c + 1 := by linarith
    refine ⟨⟨x.im * y.im + ax * y.im + ay * x.im + 2 * ax * ay + c * x.im * y.im, ?_⟩,
            ⟨x.im * y.im + ax * y.im + x.im * ay, ?_⟩⟩
    · simp only [QuadraticAlgebra.re_mul]; rw [ex, ey]; linear_combination (x.im * y.im) * ed
    · simp only [QuadraticAlgebra.im_mul]; rw [ex, ey]; ring

end Ideal

end Zsqrtd

end QuadraticNumberFields
