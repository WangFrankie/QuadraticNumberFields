/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.CommonInstances
import QuadraticNumberFields.RingOfIntegers.Integrality
import QuadraticNumberFields.RingOfIntegers.ModFour
import QuadraticNumberFields.ZOnePlusSqrtOverTwo.Basic
import QuadraticNumberFields.Mathlib.RingTheory.DedekindDomain.Basic
import QuadraticNumberFields.Instances

/-!
# Classification of the Ring of Integers of Quadratic Fields

This file proves the classical **ring of integers classification theorem** for
quadratic number fields `ℚ(√d)`, where `d` is a squarefree integer with `d ≠ 1`.

The result is a staple of algebraic number theory (see e.g.
[Marcus, *Number Fields*, Theorem 2.16], [Neukirch, *Algebraic Number Theory*, I.2],
[Boxer, *Algebraic Number Theory Notes*, Example 2.8]):

> **Theorem.** Let `d` be a squarefree integer, `d ≠ 1`. Then
>
> * if `d ≢ 1 (mod 4)`, the ring of integers of `ℚ(√d)` is `ℤ[√d]`;
> * if `d ≡ 1 (mod 4)`, writing `d = 1 + 4k`, it is `ℤ[(1 + √d)/2]`.

## Proof Strategy

An element `x ∈ ℚ(√d)` is integral over `ℤ` iff its trace `Tr(x) = 2·re(x)` and
norm `N(x) = re(x)² − d·im(x)²` are both integers. Writing `x = (a' + b'√d)/2`
in half-integer normal form (see `Integrality.lean`), integrality becomes the
divisibility condition `4 ∣ (a'² − d·b'²)`. The mod-4 arithmetic in `ModFour.lean`
then splits into the two branches above.

## Main Results

* `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`:
  `d % 4 ≠ 1 → 𝓞(ℚ(√d)) ≃+* ℤ[√d]`.
  **mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`**

* `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`:
  `d % 4 = 1 → 𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.
  **mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`**

* `ringOfIntegers_classification`: The combined classification disjunction.
  **mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`**

## Design

Integrality ingredients (`IsIntegralClosure` constructions, half-integer normal form,
etc.) live in `Integrality.lean`. This file assembles those tools into the final
`𝓞 ≃+* R` isomorphisms and the top-level classification.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-! ## The `d % 4 ≠ 1` Branch: `𝓞(ℚ(√d)) = ℤ[√d]`

When `d` is squarefree and `d ≢ 1 (mod 4)`, every integral element of `ℚ(√d)` has
integer coordinates in the `{1, √d}` basis. In the half-integer normal form
`(a' + b'√d)/2`, the condition `4 ∣ (a'² − d·b'²)` forces both `a'` and `b'` to be
even (see `dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four`), so the element already
lies in `ℤ[√d]`. -/

/-- If `d % 4 ≠ 1`, then `𝓞(ℚ(√d)) ≃+* ℤ[√d]`.

**mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`** -/
noncomputable def ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d :=
  let hd_sf : Squarefree d := Fact.out
  let hd_ne : d ≠ 1 := Fact.out
  ringOfIntegers_equiv_of_embedding (Qsqrtd (d : ℚ)) (Zsqrtd d)
    (Zsqrtd.toQsqrtdHom d)
    (Zsqrtd.toQsqrtdHom_injective d)
    (fun _ hx => exists_zsqrtd_of_isIntegral_of_ne_one_mod_four d hd_sf hd_ne hd4 hx)
    (fun z => isIntegral_toQsqrtd d z)

/-! ## The `d % 4 = 1` Branch: `𝓞(ℚ(√d)) = ℤ[(1+√d)/2]`

When `d ≡ 1 (mod 4)`, the half-integer `ω = (1 + √d)/2` satisfies
`ω² = ω + k` (where `d = 1 + 4k`), so it is integral. The condition
`4 ∣ (a'² − d·b'²)` now allows `a', b'` to be both odd (same parity),
enlarging the integral closure from `ℤ[√d]` to `ℤ[ω]`.

The ring `ℤ[ω]` is modeled as `QuadraticAlgebra ℤ k 1` (the relation `ω² = ω + k`),
which we call `ZOnePlusSqrtOverTwo k`. -/

/-- Data-level equivalence in the `d = 1 + 4k` branch, with the parameter `k`
supplied explicitly.

This is the actual workhorse of the `d % 4 = 1` branch:
`ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one` is a thin wrapper
that picks `k := d / 4`. -/
noncomputable def ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq
    (k : ℤ) (hk : d = 1 + 4 * k) :
    𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtOverTwo k := by
  have hd_sf : Squarefree d := Fact.out
  have hd_ne : d ≠ 1 := Fact.out
  subst hk
  have hd_ne' : (1 + 4 * k) ≠ 1 := hd_ne
  exact ringOfIntegers_equiv_of_embedding
    (Qsqrtd (((1 + 4 * k : ℤ) : ℚ))) (ZOnePlusSqrtOverTwo k)
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k)
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom_injective k)
    (fun _ hx => exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four k hd_sf hd_ne' hx)
    (fun z => isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k z)

/-- If `d % 4 = 1`, writing `d = 1 + 4k`, then `𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.

The result packages the witness `k` together with the equiv as data
(via `PSigma`), so the equiv is computable in principle (it is `noncomputable`
due to `NumberField.RingOfIntegers.equiv`, but no `Classical.choice` on `Nonempty`
is involved). Use `.fst`, `.snd.fst`, `.snd.snd` to project out `k`, the equality,
and the equiv respectively.

**mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`** -/
noncomputable def ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (hd4 : d % 4 = 1) :
    Σ' k : ℤ, PLift (d = 1 + 4 * k) ×'
      (𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtOverTwo k) :=
  ⟨d / 4, ⟨PLift.up (by omega),
    ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d (d / 4) (by omega)⟩⟩

/-! ## Combined Classification -/

/-- **Classification of the ring of integers of `ℚ(√d)`.**

For squarefree `d ≠ 1`, exactly one of the following holds:
* If `d ≢ 1 (mod 4)`, then `𝓞(ℚ(√d)) ≃+* ℤ[√d]`.
* If `d ≡ 1 (mod 4)`, then writing `d = 1 + 4k`, `𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.

This is the classical result found in [Marcus, Theorem 2.16],
[Neukirch, I.2], [Stewart–Tall, Theorem 4.6].

**mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`** -/
theorem ringOfIntegers_classification :
    (d % 4 ≠ 1 ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtOverTwo k)) := by
  by_cases hd4 : d % 4 = 1
  · let ex := ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
    exact Or.inr ⟨ex.fst, ex.snd.fst.down, ⟨ex.snd.snd⟩⟩
  · exact Or.inl ⟨hd4, ⟨ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4⟩⟩

/-! ## Concrete Examples

### Example 2.8 (Boxer Notes): Gaussian and Eisenstein Integers

The Gaussian integers `ℤ[i]` and Eisenstein integers `ℤ[ω₃]` are the two
most classical examples. Since `-1 % 4 = 3 ≠ 1` the Gaussian integers fall
in the first branch, while `-3 % 4 = 1` places the Eisenstein integers in
the second. -/

/-- **Gaussian integers**: `𝓞(ℚ(√(-1))) ≃+* ℤ[i]`.

Since `-1 ≡ 3 (mod 4)`, the ring of integers is `ℤ[√(-1)] = ℤ[i]`. -/
noncomputable example : 𝓞 (Qsqrtd ((-1 : ℤ) : ℚ)) ≃+* Zsqrtd (-1) :=
  ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (-1) (by decide)

/-- **Eisenstein integers**: `𝓞(ℚ(√(-3))) ≃+* ℤ[(1+√(-3))/2]`.

Since `-3 ≡ 1 (mod 4)`, the ring of integers is `ℤ[ω]` where `ω = (1+√(-3))/2`
is a primitive cube root of unity. Here `-3 = 1 + 4 * (-1)`, so `k = -1`. -/
noncomputable example : 𝓞 (Qsqrtd ((-3 : ℤ) : ℚ)) ≃+* ZOnePlusSqrtOverTwo (-1) :=
  ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq (-3) (-1) (by decide)

end SquarefreeIntegerParameter

end RingOfIntegers
end QuadraticNumberFields
