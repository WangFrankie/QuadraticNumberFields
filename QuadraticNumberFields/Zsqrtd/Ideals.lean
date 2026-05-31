/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

General ideal membership, primality, and quotient results for `Zsqrtd d`.
-/
import QuadraticNumberFields.Zsqrtd.MathlibInstances
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideal Theory for ℤ[√d]

General results about ideals in the quadratic integer ring `ℤ[√d]`, parameterised
by an integer `d` satisfying appropriate arithmetic conditions.

## Main Results

### Key algebraic identities

* `Zsqrtd.Ideal.mul_re_add_im_eq`:
  `(a*b).re + (a*b).im = (a.re+a.im)*(b.re+b.im) + (d-1)*a.im*b.im`
* `Zsqrtd.Ideal.mul_re_sub_im_eq`:
  `(a*b).re - (a*b).im = (a.re-a.im)*(b.re-b.im) + (d-1)*a.im*b.im`

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

* `Zsqrtd.Ideal.span_le_span_singleton_of_forall_dvd`
* `Zsqrtd.Ideal.ideal_of_prime_norm_is_prime`
-/

open Ideal Zsqrtd

namespace Zsqrtd.Ideal

variable (d : ℤ)

-- ============================================================================
-- Utility lemmas
-- ============================================================================

/-- If `a` divides every element of `S`, then `Ideal.span S ≤ Ideal.span {a}`.

This is a **general ideal-lattice lemma** for any commutative semiring —
it has nothing to do with `ℤ[√d]` and would be useful throughout ring theory.

**mathlib target: `Mathlib.RingTheory.Ideal.Operations`** -/
theorem span_le_span_singleton_of_forall_dvd
    {α : Type*} [CommSemiring α] {a : α} {S : Set α}
    (h : ∀ x ∈ S, a ∣ x) :
    Ideal.span S ≤ Ideal.span {a} :=
  Ideal.span_le.2 fun x hx => Ideal.mem_span_singleton.mpr (h x hx)

/-- An ideal whose absolute norm is a prime number is a prime ideal.

This is a **general fact for Dedekind domains** — an ideal with prime norm
is irreducible in the ideal monoid, hence prime by unique factorization of ideals.

**mathlib target: `Mathlib.RingTheory.DedekindDomain.Ideal`** -/
theorem ideal_of_prime_norm_is_prime {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] (I : Ideal R) (hI : I.absNorm.Prime) : I.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm hI

@[simp] lemma algebraMap_int_coe (n : ℤ) : algebraMap ℤ (Zsqrtd d) n = n := rfl

lemma map_span_int_singleton (n : ℤ) :
    Ideal.map (algebraMap ℤ (Zsqrtd d)) (Ideal.span {n}) = Ideal.span {(n : Zsqrtd d)} := by
  rw [Ideal.map_span, Set.image_singleton, algebraMap_int_coe]

-- ============================================================================
-- Key algebraic identities
-- ============================================================================

/-- The fundamental identity for `re + im` of a product in `ℤ[√d]`:
`(a*b).re + (a*b).im = (a.re + a.im) * (b.re + b.im) + (d - 1) * a.im * b.im`.

This identity is purely algebraic in the multiplication law of `QuadraticAlgebra ℤ d 0`.
It shows that the "augmentation" map `z ↦ z.re + z.im` is *almost* multiplicative,
with a correction term proportional to `d - 1`. When `p ∣ (d - 1)`, the correction
vanishes mod `p`, making the augmentation a ring hom `ℤ[√d] → ℤ/pℤ`.

**mathlib target: `Mathlib.NumberTheory.Zsqrtd.Basic`** -/
lemma mul_re_add_im_eq (a b : Zsqrtd d) :
    (a * b).re + (a * b).im =
      (a.re + a.im) * (b.re + b.im) + (d - 1) * a.im * b.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

/-- The fundamental identity for `re - im` of a product in `ℤ[√d]`:
`(a*b).re - (a*b).im = (a.re - a.im) * (b.re - b.im) + (d - 1) * a.im * b.im`. -/
lemma mul_re_sub_im_eq (a b : Zsqrtd d) :
    (a * b).re - (a * b).im =
      (a.re - a.im) * (b.re - b.im) + (d - 1) * a.im * b.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

-- ============================================================================
-- General theory for any prime p with p | (d - 1)
-- ============================================================================

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

/-- The ring hom `ℤ[√d] →+* ℤ/pℤ` sending `√d ↦ 1`, valid when `p ∣ (d - 1)`
(since `1² = 1 ≡ d (mod p)`). -/
noncomputable def liftModP (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    Zsqrtd d →+* ZMod p :=
  Zsqrtd.lift ⟨(1 : ZMod p), by simp [d_cast_zmodp_eq_one p hd]⟩

lemma liftModP_apply (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) (z : Zsqrtd d) :
    liftModP p hd z = (z.re + z.im : ZMod p) := by
  rcases z with ⟨a, b⟩
  simp [liftModP, Zsqrtd.lift, Zsqrtd.decompose]

/-- The ring hom `ℤ[√d] →+* ℤ/pℤ` sending `√d ↦ -1`, valid when `p ∣ (d - 1)`
(since `(-1)² = 1 ≡ d (mod p)`). -/
noncomputable def liftModPNeg (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    Zsqrtd d →+* ZMod p :=
  Zsqrtd.lift ⟨(-1 : ZMod p), by simp [d_cast_zmodp_eq_one p hd]⟩

lemma liftModPNeg_apply (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) (z : Zsqrtd d) :
    liftModPNeg p hd z = (z.re - z.im : ZMod p) := by
  rcases z with ⟨a, b⟩
  simp [liftModPNeg, Zsqrtd.lift, Zsqrtd.decompose, sub_eq_add_neg]

/-- An element of `ℤ[√d]` belongs to `(p, 1-√d)` iff `p ∣ (re + im)`,
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
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd, Zsqrtd.re_natCast, Zsqrtd.im_natCast] at hre him
    norm_num at hre him
    -- z.re + z.im = p*(a.re + a.im) + (1-d)*b.im = p*(a.re + a.im - c*b.im)
    have hdb : d * b.im = (↑p * c + 1) * b.im := by congr 1; linarith
    exact ⟨a.re + a.im - c * b.im, by linarith⟩
  · -- (⇐) Given p | (re + im), construct a = ⟨k, 0⟩, b = ⟨-im, 0⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k, 0⟩, ⟨-z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd, Zsqrtd.re_natCast, Zsqrtd.im_natCast]; linarith
    · simp [Zsqrtd.sqrtd, Zsqrtd.re_natCast, Zsqrtd.im_natCast]

/-- An element of `ℤ[√d]` belongs to `(p, 1+√d)` iff `p ∣ (re - im)`,
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
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd, Zsqrtd.re_natCast, Zsqrtd.im_natCast] at hre him
    norm_num at hre him
    -- z.re - z.im = p*(a.re - a.im) + (d-1)*b.im = p*(a.re - a.im + c*b.im)
    have hdb : d * b.im = (↑p * c + 1) * b.im := by congr 1; linarith
    exact ⟨a.re - a.im + c * b.im, by linarith⟩
  · -- (⇐) Given p | (re - im), construct a = ⟨k, 0⟩, b = ⟨im, 0⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k, 0⟩, ⟨z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd, Zsqrtd.re_natCast, Zsqrtd.im_natCast]; linarith
    · simp [Zsqrtd.sqrtd, Zsqrtd.re_natCast, Zsqrtd.im_natCast]

/-- The ideal `(p, 1-√d)` is prime in `ℤ[√d]` when `p ∣ (d - 1)` for a prime `p`. -/
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
    rw [mul_re_add_im_eq] at hab
    obtain ⟨c, hc⟩ := hd
    have hcorr : ((p : ℤ) ∣ (d - 1) * a.im * b.im) :=
      ⟨c * a.im * b.im, by rw [hc]; ring⟩
    exact prime_dvd_or_dvd_of_dvd_mul_add p hab hcorr

/-- The ideal `(p, 1+√d)` is prime in `ℤ[√d]` when `p ∣ (d - 1)` for a prime `p`. -/
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
    rw [mul_re_sub_im_eq] at hab
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

/-- `ℤ[√d] ⧸ (p, 1-√d) ≃+* ℤ/pℤ` when `p ∣ (d - 1)` for a prime `p`. -/
noncomputable def quotEquivZModP (p : ℕ) [Fact p.Prime] (hd : (p : ℤ) ∣ (d - 1)) :
    (Zsqrtd d) ⧸ (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d))) ≃+* ZMod p :=
  quotEquivZModOfKerEq p (liftModP p hd)
    (Ideal.span ({(p : Zsqrtd d), 1 - sqrtd} : Set (Zsqrtd d)))
    (ker_liftModP p hd)

/-- `ℤ[√d] ⧸ (p, 1+√d) ≃+* ℤ/pℤ` when `p ∣ (d - 1)` for a prime `p`. -/
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
    simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

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
    simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

end Zsqrtd.Ideal
