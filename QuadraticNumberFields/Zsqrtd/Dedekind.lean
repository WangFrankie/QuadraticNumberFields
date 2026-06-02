/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification

/-!
# When is the project model `ℤ[√d]` a Dedekind domain?

This module collects the Dedekind-domain facts about the project-owned model
`Zsqrtd d = QuadraticAlgebra ℤ d 0`. They are a direct application of the
ring-of-integers classification (`RingOfIntegers.Classification`): since `𝓞 K`
is always Dedekind for a number field `K`, and Dedekind-ness transfers across
ring isomorphisms, `ℤ[√d]` is Dedekind precisely when it coincides with the
full ring of integers — i.e. when `d ≢ 1 (mod 4)`.

The mathlib `ℤ√d` counterparts (transported across `equivMathlib`) live in
`Zsqrtd.MathlibInstances`.

## Main Results

* `Zsqrtd.isDedekindDomain_of_mod_four_ne_one`: `ℤ[√d]` is Dedekind when
  `d % 4 ≠ 1`.
* `Zsqrtd.not_isDedekindDomain_of_mod_four_eq_one`: `ℤ[√d]` is not Dedekind when
  `d % 4 = 1`.
* `Zsqrtd.isDedekindDomain_iff_mod_four_ne_one`: `ℤ[√d]` is Dedekind iff
  `d % 4 ≠ 1`.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace Zsqrtd

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- If `d % 4 ≠ 1`, then `ℤ[√d]` is a Dedekind domain — it is the full ring of
integers of `ℚ(√d)`, and Dedekind-ness transfers from `𝓞(ℚ(√d))` via the ring
isomorphism.

**mathlib target: `Mathlib.NumberTheory.Zsqrtd.DedekindDomain`** -/
theorem isDedekindDomain_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    IsDedekindDomain (Zsqrtd d) :=
  RingEquiv.isDedekindDomain
    (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4)

/-- `ℚ(√d)` is the fraction field of the project model `ℤ[√d]`, via the canonical
embedding `toQsqrtdHom`. The witness clears denominators coordinate-wise: for
`z = r + s√d`, the rational integer `z.re.den * z.im.den` scales `z` into `ℤ[√d]`.

**mathlib target: `Mathlib.NumberTheory.Zsqrtd.Basic`** -/
theorem isFractionRing_qsqrtd :
    letI : Algebra (Zsqrtd d) (Qsqrtd (d : ℚ)) := (Zsqrtd.toQsqrtdHom d).toAlgebra
    IsFractionRing (Zsqrtd d) (Qsqrtd (d : ℚ)) := by
  letI : Algebra (Zsqrtd d) (Qsqrtd (d : ℚ)) := (Zsqrtd.toQsqrtdHom d).toAlgebra
  letI : FaithfulSMul (Zsqrtd d) (Qsqrtd (d : ℚ)) :=
    (faithfulSMul_iff_algebraMap_injective (Zsqrtd d) (Qsqrtd (d : ℚ))).mpr
      (Zsqrtd.toQsqrtdHom_injective d)
  refine IsFractionRing.of_field (R := Zsqrtd d) (K := Qsqrtd (d : ℚ)) ?_
  intro z
  refine ⟨⟨(z.re.num : ℤ) * z.im.den, (z.im.num : ℤ) * z.re.den⟩,
      ((z.re.den * z.im.den : ℕ) : Zsqrtd d), ?_⟩
  refine (eq_div_iff ?_).2 ?_
  · norm_num
  · ext
    · simp only [Nat.cast_mul, map_mul, map_natCast, QuadraticAlgebra.re_mul,
         QuadraticAlgebra.im_natCast, mul_zero, add_zero,
        QuadraticAlgebra.im_mul, zero_mul]
      calc
        z.re * (↑z.re.den * ↑z.im.den) = z.re * (z.re.den : ℚ) * z.im.den := by ring
        _ = ((z.re.num : ℤ) : ℚ) * z.im.den := by rw [Rat.mul_den_eq_num]
        _ = (((z.re.num : ℤ) * z.im.den : ℤ) : ℚ) := by norm_num
    · simp only [Nat.cast_mul, map_mul, map_natCast, QuadraticAlgebra.im_mul,
         QuadraticAlgebra.im_natCast, mul_zero, zero_mul,
        add_zero, QuadraticAlgebra.re_mul, zero_add]
      calc
        z.im * (↑z.re.den * ↑z.im.den) = z.im * (z.im.den : ℚ) * z.re.den := by ring
        _ = ((z.im.num : ℤ) : ℚ) * z.re.den := by rw [Rat.mul_den_eq_num]
        _ = (((z.im.num : ℤ) * z.re.den : ℤ) : ℚ) := by norm_num

/-- If `d % 4 = 1`, then `ℤ[√d]` is **not** a Dedekind domain.

The obstruction is that `ℤ[√d]` is not integrally closed in its fraction field
`ℚ(√d)`: the element `ω = (1 + √d)/2` satisfies `ω² − ω − k = 0` (where
`d = 1 + 4k`), so it is integral over `ℤ`, but its half-integer coordinates
`(1, 1)` are both odd, hence `ω ∉ ℤ[√d]`. Since every Dedekind domain is
integrally closed, `ℤ[√d]` cannot be Dedekind.

The proof requires `ℚ(√d)` to be the fraction field of `ℤ[√d]`, which is
established by a clearing-denominators argument: for `z = r + s√d` with
`r = p/q, s = u/v`, the product `qv · z` lies in `ℤ[√d]`.

**mathlib target: `Mathlib.NumberTheory.Zsqrtd.DedekindDomain`** — the fraction
field construction `IsFractionRing (ℤ√d) (ℚ√d)` would also be useful as a
standalone result in `Mathlib.NumberTheory.Zsqrtd.Basic`. -/
theorem not_isDedekindDomain_of_mod_four_eq_one
    (hd4 : d % 4 = 1) :
    ¬ IsDedekindDomain (Zsqrtd d) := by
  -- `ℚ(√d) = Frac(ℤ[√d])` via the canonical embedding.
  letI : Algebra (Zsqrtd d) (Qsqrtd (d : ℚ)) := (Zsqrtd.toQsqrtdHom d).toAlgebra
  have hFrac : IsFractionRing (Zsqrtd d) (Qsqrtd (d : ℚ)) := isFractionRing_qsqrtd d
  intro _
  -- A Dedekind domain is integrally closed in its fraction field.
  -- Write `d = 1 + 4k` and consider `ω = (1 + √d)/2`.
  rcases RingOfIntegers.exists_k_of_mod_four_eq_one (d := d) hd4 with ⟨k, hk⟩
  subst hk
  let x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ)) := RingOfIntegers.halfInt (1 + 4 * k) 1 1
  -- Show `ω` is integral: it lies in `ℤ[(1+√d)/2]`, which is an integral extension.
  have hx_def :
      x = _root_.ZOnePlusSqrtOverTwo.toQsqrtdFun k (⟨0, 1⟩ : _root_.ZOnePlusSqrtOverTwo k) := by
    ext <;> simp [x, RingOfIntegers.halfInt, _root_.ZOnePlusSqrtOverTwo.toQsqrtdFun]
  have hx_integral_Z : IsIntegral ℤ x := by
    rw [hx_def]
    exact RingOfIntegers.isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k
      (z := (⟨0, 1⟩ : _root_.ZOnePlusSqrtOverTwo k))
  have hx_integral : IsIntegral (Zsqrtd (1 + 4 * k)) x := hx_integral_Z.tower_top
  rcases (isIntegrallyClosed_iff (Qsqrtd (((1 + 4 * k : ℤ) : ℚ)))).mp
      IsDedekindRing.toIsIntegralClosure hx_integral with
    ⟨z, hz⟩
  -- If `ω ∈ ℤ[√d]`, the half-integer criterion would force the numerators
  -- `(1, 1)` to both be even — a contradiction.
  have h_even : 2 ∣ (1 : ℤ) ∧ 2 ∣ (1 : ℤ) :=
    (Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even (1 + 4 * k) 1 1).mp
      ⟨z, by
        simpa [x, RingOfIntegers.halfInt, RingHom.toAlgebra] using hz⟩
  omega

/-- For a squarefree `d ≠ 1`, `ℤ[√d]` is a Dedekind domain if and only if
`d ≢ 1 (mod 4)` — equivalently, if and only if `ℤ[√d]` is the full ring of
integers of `ℚ(√d)`.

This characterizes exactly when the order `ℤ[√d]` coincides with the maximal
order `𝓞(ℚ(√d))`.

**mathlib target: `Mathlib.NumberTheory.Zsqrtd.DedekindDomain`** -/
theorem isDedekindDomain_iff_mod_four_ne_one :
    IsDedekindDomain (Zsqrtd d) ↔ d % 4 ≠ 1 := by
  constructor
  · intro hDed hd4
    exact not_isDedekindDomain_of_mod_four_eq_one d hd4 hDed
  · exact isDedekindDomain_of_mod_four_ne_one d

end SquarefreeIntegerParameter

end Zsqrtd
end QuadraticNumberFields
