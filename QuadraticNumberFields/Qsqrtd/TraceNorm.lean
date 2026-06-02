/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.QuadraticField.Parameters

/-!
# Trace and Norm Preparations for Quadratic Integrality

This file isolates the trace/norm computations used in the integrality
classification for quadratic number fields.

It does not introduce new trace or norm definitions: trace is always
`Algebra.trace ℚ (Qsqrtd d)`, and norm is always `Qsqrtd.norm`.

## Main Theorems

* `TraceNorm.norm_eq_sqr_minus_d_sqr`: the norm in `Q(√d)` is `re² - d * im²`.
* `TraceNorm.exists_int_trace`: an integral element has integral trace.
* `TraceNorm.exists_int_norm`: an integral element has integral norm.
* `TraceNorm.exists_int_double_im`: an integral element has doubled imaginary part in `ℤ`.
-/


namespace QuadraticNumberFields
namespace RingOfIntegers
namespace TraceNorm

/-! ## `Qsqrtd` Trace/Norm-Star API

Trace/norm-star identities exposed in the `Qsqrtd` namespace for reuse by the
Galois-group, classification, and `Conj` interfaces. -/

namespace Qsqrtd

/-- The sum `x + star x` is the trace of `x` viewed inside `Q(√d)`. -/
theorem add_star_eq_trace_image {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    x + star x =
      algebraMap ℚ (Qsqrtd (d : ℚ)) (Algebra.trace ℚ (Qsqrtd (d : ℚ)) x) := by
  ext
  · simp [Qsqrtd.trace_eq_re_add_re_star, star]
  · simp [star]

/-- The norm of `x`, viewed inside `Q(√d)`, is the product `x * star x`. -/
theorem norm_image_eq_mul_star {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x) = x * star x := by
  simpa [Qsqrtd.norm, mul_comm] using
    (QuadraticAlgebra.algebraMap_norm_eq_mul_star (a := (d : ℚ)) (b := (0 : ℚ)) x)

end Qsqrtd

/-- Integrality is preserved by the quadratic conjugation map. -/
private lemma isIntegral_star {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd (Qsqrtd (d : ℚ))) hx

/-- Norm in `Q(√d)` is `re² - d * im²`. -/
theorem norm_eq_sqr_minus_d_sqr {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    Qsqrtd.norm x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  simp [Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

/-- The trace, viewed inside `Q(√d)`, is integral over `ℤ`. -/
private lemma isIntegral_trace_image {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Algebra.trace ℚ (Qsqrtd d) x)) := by
  simpa [Qsqrtd.add_star_eq_trace_image x] using hx.add (isIntegral_star hx)

/-- The trace of an integral element of `Q(√d)` is integral over `ℤ`. -/
private lemma isIntegral_trace {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (Algebra.trace ℚ (Qsqrtd d) x) :=
  (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
    (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 (isIntegral_trace_image hx)

/-- The trace of an integral element of `Q(√d)` is an integer. -/
lemma exists_int_trace {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' : ℤ, (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x := by
  obtain ⟨a', ha'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1
    (isIntegral_trace hx)
  exact ⟨a', by simpa using ha'⟩

/-- The norm, viewed inside `Q(√d)`, is integral over `ℤ`. -/
private lemma isIntegral_norm_image {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x)) := by
  simpa [Qsqrtd.norm_image_eq_mul_star x] using hx.mul (isIntegral_star hx)

/-- The norm of an integral element of `Q(√d)` is integral over `ℤ`. -/
private lemma isIntegral_norm {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (Qsqrtd.norm x) :=
  (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
    (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 (isIntegral_norm_image hx)

/-- The norm of an integral element of `Q(√d)` is an integer. -/
lemma exists_int_norm {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ n' : ℤ, (n' : ℚ) = Qsqrtd.norm x := by
  obtain ⟨n', hn'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1
    (isIntegral_norm hx)
  exact ⟨n', by simpa using hn'⟩

/-- Once the trace is integral, the real part has denominator at most `2`. -/
lemma re_eq_half_trace_int {d : ℤ} {x : Qsqrtd (d : ℚ)} {a' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x) :
    x.re = (a' : ℚ) / 2 := by
  nlinarith [show 2 * x.re = (a' : ℚ) by
    calc
      2 * x.re = Algebra.trace ℚ (Qsqrtd d) x := (Qsqrtd.trace_eq_two_re x).symm
      _ = (a' : ℚ) := ha'trace.symm]

/-- A rational square equal to an integer is integral over `ℤ`. -/
lemma isIntegral_of_sq_int {q : ℚ} {k : ℤ} (hq2 : q ^ 2 = (k : ℚ)) :
    IsIntegral ℤ q := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C k,
    Polynomial.monic_X_pow_sub_C (R := ℤ) (n := 2) k (by decide), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp [hq2]

/-- The doubled imaginary part satisfies the basic norm identity. -/
private lemma double_im_sq_mul_eq
    (d : ℤ) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (d : ℚ) * (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) := by
  have hre : x.re = (a' : ℚ) / 2 := re_eq_half_trace_int ha'trace
  have hnorm' :
      (n' : ℚ) = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by
    calc
      (n' : ℚ) = Qsqrtd.norm x := hn'norm
      _ = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := norm_eq_sqr_minus_d_sqr x
      _ = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by simp [hre]
  have haux : (a' : ℚ) ^ 2 - 4 * (n' : ℚ) = 4 * (d : ℚ) * x.im ^ 2 := by
    nlinarith [hnorm']
  have hmcast : ((a' ^ 2 - 4 * n' : ℤ) : ℚ) = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by
    norm_cast
  calc
    (d : ℚ) * (2 * x.im) ^ 2 = 4 * (d : ℚ) * x.im ^ 2 := by ring
    _ = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by linarith [haux]
    _ = (a' ^ 2 - 4 * n' : ℤ) := hmcast.symm

/-- The doubled imaginary part is a square root of `(a'^2 - 4 n') / d`. -/
private lemma double_im_sq_eq_ratio
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) := by
  calc
    (2 * x.im) ^ 2 = ((d : ℚ) * (2 * x.im) ^ 2) / (d : ℚ) := by field_simp [hd0Q]
    _ = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) := by
      simp [double_im_sq_mul_eq d ha'trace hn'norm]

/-- The ratio `(a'^2 - 4 n') / d` is a square. -/
private lemma isSquare_trace_norm_ratio
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    IsSquare ((a' ^ 2 - 4 * n' : ℤ) / (d : ℚ)) :=
  ⟨2 * x.im, by simpa [pow_two] using (double_im_sq_eq_ratio d hd0Q ha'trace hn'norm).symm⟩

/-- The quotient square gives divisibility by the squarefree parameter. -/
private lemma dvd_trace_norm_delta
    (d : ℤ) (hd0 : d ≠ 0) (hd_sf : Squarefree d) (hd0Q : (d : ℚ) ≠ 0)
    {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    d ∣ (a' ^ 2 - 4 * n') :=
  int_dvd_of_ratio_square (a' ^ 2 - 4 * n') d hd0 hd_sf
    (isSquare_trace_norm_ratio d hd0Q ha'trace hn'norm)

/-- The doubled imaginary part squares to an integer. -/
private lemma double_im_sq_eq_int
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' k : ℤ}
    (hk : a' ^ 2 - 4 * n' = d * k)
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (2 * x.im) ^ 2 = (k : ℚ) := by
  have hmk : ((a' ^ 2 - 4 * n' : ℤ) : ℚ) = (d : ℚ) * k := by
    exact_mod_cast hk
  calc
    (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) :=
      double_im_sq_eq_ratio d hd0Q ha'trace hn'norm
    _ = ((d : ℚ) * k) / (d : ℚ) := by simp [hmk]
    _ = (k : ℚ) := by field_simp [hd0Q]

/-- Turning an integral doubled imaginary part into an integer witness. -/
private lemma exists_int_of_isIntegral_rat {q : ℚ} (hq : IsIntegral ℤ q) :
    ∃ b' : ℤ, (b' : ℚ) = q := by
  obtain ⟨b', hb'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  exact ⟨b', by simpa using hb'⟩

/-- Rewriting from `2 * x.im = b'` to the half-integer form of the imaginary part. -/
private lemma im_eq_half_of_double_im_eq {d : ℤ} {x : Qsqrtd (d : ℚ)} {b' : ℤ}
    (hb' : (b' : ℚ) = 2 * x.im) :
    x.im = (b' : ℚ) / 2 := by
  nlinarith [hb']

/-- For an integral element of `Q(√d)`, the doubled imaginary part is an integer. -/
lemma exists_int_double_im
    (d : ℤ) (hd_sf : Squarefree d) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    ∃ b' : ℤ, x.im = (b' : ℚ) / 2 := by
  have hd0 : d ≠ 0 := hd_sf.ne_zero
  have hd0Q : (d : ℚ) ≠ 0 := by
    exact_mod_cast hd0
  rcases dvd_trace_norm_delta d hd0 hd_sf hd0Q ha'trace hn'norm with ⟨k, hk⟩
  rcases exists_int_of_isIntegral_rat
      (isIntegral_of_sq_int (double_im_sq_eq_int d hd0Q hk ha'trace hn'norm)) with
    ⟨b', hb'⟩
  exact ⟨b', im_eq_half_of_double_im_eq hb'⟩

/-- If the half-integer norm is already an integer, then the numerator is divisible by `4`. -/
lemma dvd_four_sub_sq_of_norm_eq_int
    (a' b' d n' : ℤ)
    (hnorm :
      (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ))) :
    (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) := by
  exact (Rat.den_div_intCast_eq_one_iff (a' ^ 2 - d * b' ^ 2) 4 (by norm_num)).1 <| by
    rw [← hnorm]
    simp

end TraceNorm
end RingOfIntegers
end QuadraticNumberFields
