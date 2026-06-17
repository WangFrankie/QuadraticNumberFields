/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Forms.ClassGroup.ClassNumber
import QuadraticNumberFields.Examples.Sqrt17.Invariants
import QuadraticNumberFields.RingOfIntegers.Norm

/-!
# The Class Number of `ℚ(√17)` Is One

Hand computation of the class number of `ℚ(√17)`.

Since `17 ≡ 1 (mod 4)`, the ring of integers is `𝓞(ℚ(√17)) = ℤ[(1+√17)/2]`
(`Examples.Sqrt17.ringOfIntegersEquiv`). The Minkowski bound for this real
quadratic field is `(1/2)·√17 < 3` (`Examples.Sqrt17.minkowskiBound_lt_three`),
so every ideal class contains a non-zero ideal `I` of absolute norm `< 3`,
i.e. `absNorm I ∈ {1, 2}`.

* `absNorm I = 1` forces `I = ⊤`, which is principal.
* `absNorm I = 2` forces `I` to be prime and to divide `(2)` in `𝓞(ℚ(√17))`.

The prime factorization of `(2)` is `(2) = (x)·(x̄)` where `x = (5 + √17)/2`
and `x̄ = (5 - √17)/2` are conjugate elements of norm `2`. Concretely, in the
model `ℤ[(1+√17)/2] = ZOnePlusSqrtdOverTwo 4` (with `ω = (1 + √17)/2`,
`ω² = ω + 4`) these are `2 + ω = ⟨2, 1⟩` and `3 - ω = ⟨3, -1⟩`, embedded into
`𝓞(ℚ(√17))` by the canonical map `ZOnePlusSqrtdOverTwo.toQsqrtdHom`. Both
`(x)` and `(x̄)` are norm-`2` prime ideals, so every norm-`2` prime is
principal. Together with `I = ⊤` for the norm-`1` case, this shows every ideal
class is trivial, i.e. `classNumberQsqrtd 17 = 1`.

This hand computation places `ℚ(√17)` in the class-number-one list right after
the nine Heegner fields, illustrating the split-prime dichotomy on a real
quadratic example: here `2` splits, so genuine norm-`2` primes exist, yet they
are principal.
-/

open scoped NumberField

open Ideal

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields.Examples.Sqrt17

/-! ## The norm-2 elements `x = (5 + √17)/2` and `x̄ = (5 - √17)/2`

In `ZOnePlusSqrtdOverTwo 4` (with `ω = (1 + √17)/2` satisfying `ω² = ω + 4`):

* `x = (5 + √17)/2 = 2 + ω`, i.e. the element `⟨2, 1⟩`, of norm
  `2² + 2·1 - 4·1² = 2`;
* `x̄ = (5 - √17)/2 = 3 - ω` (using `ω̄ = 1 - ω`), i.e. the element `⟨3, -1⟩`,
  of norm `3² + 3·(-1) - 4·1² = 2`;
* `(2 + ω)(3 - ω) = 2`, giving `(2) = (x)(x̄)` in `𝓞(ℚ(√17))`. -/

/-- The element `2 + ω` in `ZOnePlusSqrtdOverTwo 4`, i.e. `(5 + √17)/2`. -/
private def xZ : ZOnePlusSqrtdOverTwo 4 := ⟨2, 1⟩

/-- The element `3 - ω` in `ZOnePlusSqrtdOverTwo 4`, i.e. `(5 - √17)/2`. -/
private def xConjZ : ZOnePlusSqrtdOverTwo 4 := ⟨3, -1⟩

/-- `ZOnePlusSqrtdOverTwo.normHom 4 xZ = 2`. -/
private theorem norm_xZ : ZOnePlusSqrtdOverTwo.normHom 4 xZ = 2 := by
  rw [xZ, ZOnePlusSqrtdOverTwo.normHom_apply, ZOnePlusSqrtdOverTwo.norm_mk]
  norm_num

/-- `ZOnePlusSqrtdOverTwo.normHom 4 xConjZ = 2`. -/
private theorem norm_xConjZ : ZOnePlusSqrtdOverTwo.normHom 4 xConjZ = 2 := by
  rw [xConjZ, ZOnePlusSqrtdOverTwo.normHom_apply, ZOnePlusSqrtdOverTwo.norm_mk]
  norm_num

/-- The product `(2 + ω)(3 - ω) = 2` in `ZOnePlusSqrtdOverTwo 4`. -/
private theorem xZ_mul_xConjZ : xZ * xConjZ = (2 : ZOnePlusSqrtdOverTwo 4) := by
  rw [xZ, xConjZ]
  ext <;>
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    ring

/-- The algebraic integer `x = (5 + √17)/2 = 2 + ω` in `𝓞(ℚ(√17))`, defined as
the image of `⟨2, 1⟩ ∈ ℤ[(1+√17)/2]` under the canonical embedding
`ZOnePlusSqrtdOverTwo.toQsqrtdHom`. -/
noncomputable def x : 𝓞 (Qsqrtd ((17 : ℤ) : ℚ)) :=
  ⟨ZOnePlusSqrtdOverTwo.toQsqrtdHom 4 xZ,
    RingOfIntegers.isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo 4 xZ⟩

/-- The conjugate `x̄ = (5 - √17)/2 = 3 - ω` of `x` in `𝓞(ℚ(√17))`. -/
noncomputable def xConj : 𝓞 (Qsqrtd ((17 : ℤ) : ℚ)) :=
  ⟨ZOnePlusSqrtdOverTwo.toQsqrtdHom 4 xConjZ,
    RingOfIntegers.isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo 4 xConjZ⟩

/-! ### Norms of `x` and `x̄`

The integer norm `Algebra.norm ℤ` equals the integer lift of the field norm
(`Algebra.coe_norm_int`), which equals the coordinate norm
(`algebraNorm_ratAlgebra_eq_qsqrtdNorm`); the latter is computed in the
`ℤ[(1+√17)/2]` model by `RingOfIntegers.norm_zOnePlusSqrtOverTwo_toQsqrtd`. -/

/-- `Algebra.norm ℤ x = 2`. -/
theorem norm_x_eq_two : Algebra.norm ℤ x = 2 := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int (K := Qsqrtd ((17 : ℤ) : ℚ)),
    Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
  change Qsqrtd.norm (ZOnePlusSqrtdOverTwo.toQsqrtdHom 4 xZ) = ((2 : ℤ) : ℚ)
  rw [RingOfIntegers.norm_zOnePlusSqrtOverTwo_toQsqrtd, ← ZOnePlusSqrtdOverTwo.normHom_apply,
    norm_xZ]

/-- `Algebra.norm ℤ xConj = 2`. -/
theorem norm_xConj_eq_two : Algebra.norm ℤ xConj = 2 := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int (K := Qsqrtd ((17 : ℤ) : ℚ)),
    Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
  change Qsqrtd.norm (ZOnePlusSqrtdOverTwo.toQsqrtdHom 4 xConjZ) = ((2 : ℤ) : ℚ)
  rw [RingOfIntegers.norm_zOnePlusSqrtOverTwo_toQsqrtd, ← ZOnePlusSqrtdOverTwo.normHom_apply,
    norm_xConjZ]

/-! ## `x · x̄ = 2` and the prime factorization of `(2)` -/

/-- The product `x · x̄ = 2` in `𝓞(ℚ(√17))`. -/
theorem x_mul_xConj : x * xConj = (2 : 𝓞 (Qsqrtd ((17 : ℤ) : ℚ))) := by
  apply Subtype.ext
  change ZOnePlusSqrtdOverTwo.toQsqrtdHom 4 xZ * ZOnePlusSqrtdOverTwo.toQsqrtdHom 4 xConjZ
    = ((2 : 𝓞 (Qsqrtd ((17 : ℤ) : ℚ))) : Qsqrtd ((17 : ℤ) : ℚ))
  rw [← map_mul, xZ_mul_xConjZ, map_ofNat]
  rfl

/-- The product `(x)(x̄) = (2)` in `𝓞(ℚ(√17))`. -/
theorem span_x_mul_span_xConj :
    (Ideal.span {x} : Ideal (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))) *
      Ideal.span {xConj} = Ideal.span {(2 : 𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))} := by
  rw [Ideal.span_singleton_mul_span_singleton, x_mul_xConj]

/-! ## `absNorm (span {x}) = 2` and primality -/

/-- `absNorm (span {x}) = 2`. -/
theorem absNorm_span_x :
    Ideal.absNorm (Ideal.span {x} : Ideal (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))) = 2 := by
  rw [Ideal.absNorm_span_singleton, norm_x_eq_two]
  rfl

/-- `absNorm (span {xConj}) = 2`. -/
theorem absNorm_span_xConj :
    Ideal.absNorm (Ideal.span {xConj} : Ideal (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))) = 2 := by
  rw [Ideal.absNorm_span_singleton, norm_xConj_eq_two]
  rfl

/-- `(x)` is a prime ideal: it has irreducible absolute norm `2`. -/
theorem isPrime_span_x :
    (Ideal.span {x} : Ideal (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))).IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm
    (by rw [absNorm_span_x]; exact irreducible_two_nat)

/-- `(x̄)` is a prime ideal. -/
theorem isPrime_span_xConj :
    (Ideal.span {xConj} : Ideal (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))).IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm
    (by rw [absNorm_span_xConj]; exact irreducible_two_nat)

/-! ## Norm-2 ideals are principal, and `ℚ(√17)` has class number one

A norm-`2` ideal `I` is prime and contains `2`, hence divides `(2) = (x)(x̄)`;
being prime it equals one of the prime factors `(x)` or `(x̄)` (both maximal),
and is therefore principal. Combined with the norm-`1` (i.e. `⊤`) case and the
Minkowski representative bound, every ideal class is trivial. -/

/-- Every ideal of absolute norm `2` in `𝓞(ℚ(√17))` is principal: it is a prime
dividing `(2) = (x)(x̄)`, hence equals the maximal ideal `(x)` or `(x̄)`. -/
theorem isPrincipal_of_absNorm_eq_two
    {I : Ideal (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))} (hI : Ideal.absNorm I = 2) :
    I.IsPrincipal := by
  have hIprime : I.IsPrime := Ideal.isPrime_of_absNorm_eq_two hI
  have hIbot : I ≠ ⊥ := by rw [Ne, ← Ideal.absNorm_eq_zero_iff, hI]; norm_num
  have hItop : I ≠ ⊤ := by intro h; rw [h, Ideal.absNorm_top] at hI; norm_num at hI
  have h2mem : (2 : 𝓞 (Qsqrtd ((17 : ℤ) : ℚ))) ∈ I := by
    have hm := Ideal.absNorm_mem I; rw [hI] at hm; exact_mod_cast hm
  have hdvd2 : I ∣ Ideal.span {(2 : 𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact h2mem
  rw [← span_x_mul_span_xConj] at hdvd2
  have hIprimeElem : Prime I := (Ideal.prime_iff_isPrime hIbot).mpr hIprime
  have hxbot : Ideal.span {x} ≠ ⊥ := by
    rw [Ne, ← Ideal.absNorm_eq_zero_iff, absNorm_span_x]; norm_num
  have hxcbot : Ideal.span {xConj} ≠ ⊥ := by
    rw [Ne, ← Ideal.absNorm_eq_zero_iff, absNorm_span_xConj]; norm_num
  rcases hIprimeElem.dvd_mul.mp hdvd2 with hx | hxc
  · have hmax : (Ideal.span {x}).IsMaximal := isPrime_span_x.isMaximal hxbot
    have heq : Ideal.span {x} = I := hmax.eq_of_le hItop (Ideal.le_of_dvd hx)
    rw [← heq]; exact ⟨x, rfl⟩
  · have hmax : (Ideal.span {xConj}).IsMaximal := isPrime_span_xConj.isMaximal hxcbot
    have heq : Ideal.span {xConj} = I := hmax.eq_of_le hItop (Ideal.le_of_dvd hxc)
    rw [← heq]; exact ⟨xConj, rfl⟩

/-- Every ideal class of `ℚ(√17)` is trivial. -/
theorem classGroup_eq_one (C : ClassGroup (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))) : C = 1 := by
  exact classGroup_eq_one_of_exists_ideal_norm_lt_three
    exists_ideal_in_class_of_norm_le (fun hI => isPrincipal_of_absNorm_eq_two hI) C

/-- **`ℚ(√17)` has class number one.** -/
theorem classNumber_eq_one :
    NumberField.classNumber (Qsqrtd ((17 : ℤ) : ℚ)) = 1 := by
  exact NumberField.classNumber_eq_one_of_forall_classGroup_eq_one classGroup_eq_one

/-- `classNumberQsqrtd 17 = 1`, the unified-interface form. -/
theorem classNumberQsqrtd_seventeen : classNumberQsqrtd 17 = 1 :=
  classNumber_eq_one

end QuadraticNumberFields.Examples.Sqrt17
