/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.CommonInstances
import QuadraticNumberFields.RingOfIntegers.Integrality
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.Transport

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

/-- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one` commutes with the embedding back
into `ℚ(√d)`: applied to `e α`, the embedding recovers `(α : ℚ(√d))`. -/
lemma ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply (hd4 : d % 4 ≠ 1)
    (α : 𝓞 (Qsqrtd (d : ℚ))) :
    Zsqrtd.toQsqrtdHom d (ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4 α)
      = (α : Qsqrtd (d : ℚ)) :=
  ringOfIntegers_equiv_of_embedding_apply (Zsqrtd.toQsqrtdHom d)
    (Zsqrtd.toQsqrtdHom_injective d)
    (fun _ hx => exists_zsqrtd_of_isIntegral_of_ne_one_mod_four d Fact.out Fact.out hd4 hx)
    (fun z => isIntegral_toQsqrtd d z) α

/-! ## The `d % 4 = 1` Branch: `𝓞(ℚ(√d)) = ℤ[(1+√d)/2]`

When `d ≡ 1 (mod 4)`, the half-integer `ω = (1 + √d)/2` satisfies
`ω² = ω + k` (where `d = 1 + 4k`), so it is integral. The condition
`4 ∣ (a'² − d·b'²)` now allows `a', b'` to be both odd (same parity),
enlarging the integral closure from `ℤ[√d]` to `ℤ[ω]`.

The ring `ℤ[ω]` is modeled as `QuadraticAlgebra ℤ k 1` (the relation `ω² = ω + k`),
which we call `ZOnePlusSqrtdOverTwo k`. -/

/-- Data-level equivalence in the `d = 1 + 4k` branch, with the parameter `k`
supplied explicitly.

This is the actual workhorse of the `d % 4 = 1` branch:
`ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one` is a thin wrapper
that picks `k := d / 4`. -/
noncomputable def ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq
    (k : ℤ) (hk : d = 1 + 4 * k) :
    𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtdOverTwo k := by
  have hd_sf : Squarefree d := Fact.out
  have hd_ne : d ≠ 1 := Fact.out
  subst hk
  have hd_ne' : (1 + 4 * k) ≠ 1 := hd_ne
  exact ringOfIntegers_equiv_of_embedding
    (Qsqrtd (((1 + 4 * k : ℤ) : ℚ))) (ZOnePlusSqrtdOverTwo k)
    (_root_.ZOnePlusSqrtdOverTwo.toQsqrtdHom k)
    (_root_.ZOnePlusSqrtdOverTwo.toQsqrtdHom_injective k)
    (fun _ hx => exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four k hd_sf hd_ne' hx)
    (fun z => isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k z)

/-- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq` commutes with the embedding
back into `ℚ(√(1 + 4k))`: applied to `e α`, the embedding recovers
`(α : ℚ(√(1 + 4k)))`. -/
lemma ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_apply
    (k : ℤ) [Fact (Squarefree (1 + 4 * k))] [Fact ((1 + 4 * k) ≠ 1)]
    (α : 𝓞 (Qsqrtd (((1 + 4 * k : ℤ) : ℚ)))) :
    ZOnePlusSqrtdOverTwo.toQsqrtdHom k
        (ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq (1 + 4 * k) k rfl α) =
      (α : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))) := by
  unfold ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq
  rw [ringOfIntegers_equiv_of_embedding_apply]

/-- The `re` coordinate of `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq`. -/
theorem ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_re
    (k : ℤ) (hk : d = 1 + 4 * k) (α : 𝓞 (Qsqrtd (d : ℚ))) :
    let e := ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d k hk
    ((e α).re : ℚ) + ((e α).im : ℚ) / 2 = (α : Qsqrtd (d : ℚ)).re := by
  subst hk
  simpa using congrArg QuadraticAlgebra.re
    (ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_apply k α)

/-- The `im` coordinate of `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq`. -/
theorem ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_im
    (k : ℤ) (hk : d = 1 + 4 * k) (α : 𝓞 (Qsqrtd (d : ℚ))) :
    let e := ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d k hk
    ((e α).im : ℚ) / 2 = (α : Qsqrtd (d : ℚ)).im := by
  subst hk
  simpa using congrArg QuadraticAlgebra.im
    (ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_apply k α)

/-- If `d % 4 = 1`, then `𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`, using the canonical witness
`k := d / 4` (so `d = 1 + 4 * (d / 4)`).  This is a thin wrapper over the
explicit-parameter `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq`.

**mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`** -/
noncomputable def ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (hd4 : d % 4 = 1) :
    𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtdOverTwo (d / 4) :=
  ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d (d / 4) (by omega)

/-- The `re` coordinate of the `d % 4 = 1` ring-of-integers equivalence. -/
theorem ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_re
    (hd4 : d % 4 = 1) (α : 𝓞 (Qsqrtd (d : ℚ))) :
    let e := ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
    ((e α).re : ℚ) + ((e α).im : ℚ) / 2 = (α : Qsqrtd (d : ℚ)).re := by
  exact ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_re d (d / 4) (by omega) α

/-- The `im` coordinate of the `d % 4 = 1` ring-of-integers equivalence. -/
theorem ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_im
    (hd4 : d % 4 = 1) (α : 𝓞 (Qsqrtd (d : ℚ))) :
    let e := ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
    ((e α).im : ℚ) / 2 = (α : Qsqrtd (d : ℚ)).im := by
  exact ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_im d (d / 4) (by omega) α

/-! ## Combined Classification -/

/-- **Classification of the ring of integers of `ℚ(√d)`.**

For squarefree `d ≠ 1`, exactly one of the following holds:
* If `d ≢ 1 (mod 4)`, then `𝓞(ℚ(√d)) ≃+* ℤ[√d]`.
* If `d ≡ 1 (mod 4)`, then writing `d = 1 + 4k`, `𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`. -/
theorem ringOfIntegers_classification :
    (d % 4 ≠ 1 ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtdOverTwo k)) := by
  by_cases hd4 : d % 4 = 1
  · exact Or.inr ⟨d / 4, by omega,
      ⟨ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4⟩⟩
  · exact Or.inl ⟨hd4, ⟨ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4⟩⟩

/-- Transport the ring-of-integers classification from `Qsqrtd d` back to an
abstract field ring-equivalent to it. -/
theorem ringOfIntegers_classification_of_ringEquiv_qsqrtd
    {K : Type*} [Field K] (e : K ≃+* Qsqrtd (d : ℚ)) :
    (d % 4 ≠ 1 ∧ Nonempty (𝓞 K ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧ Nonempty (𝓞 K ≃+* ZOnePlusSqrtdOverTwo k)) := by
  let e𝓞 : 𝓞 K ≃+* 𝓞 (Qsqrtd (d : ℚ)) :=
    e.ringOfIntegers
  rcases ringOfIntegers_classification d with h | h
  · exact Or.inl ⟨h.1, h.2.map (fun f => e𝓞.trans f)⟩
  · rcases h with ⟨k, hk, hnonempty⟩
    exact Or.inr ⟨k, hk, hnonempty.map (fun f => e𝓞.trans f)⟩

/-- Every abstract quadratic field has a standard squarefree parameter for which
the transported ring-of-integers classification holds. -/
theorem exists_ringOfIntegers_classification_of_quadraticField
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧
      ((d % 4 ≠ 1 ∧ Nonempty (𝓞 K ≃+* Zsqrtd d)) ∨
      (∃ k : ℤ, d = 1 + 4 * k ∧ Nonempty (𝓞 K ≃+* ZOnePlusSqrtdOverTwo k))) := by
  obtain ⟨d, hd_sf, hd_ne, ⟨e⟩⟩ := exists_ringEquiv_qsqrtd K
  letI : Fact (Squarefree d) := ⟨hd_sf⟩
  letI : Fact (d ≠ 1) := ⟨hd_ne⟩
  exact ⟨d, hd_sf, hd_ne, ringOfIntegers_classification_of_ringEquiv_qsqrtd d e⟩

end SquarefreeIntegerParameter

end RingOfIntegers
end QuadraticNumberFields
