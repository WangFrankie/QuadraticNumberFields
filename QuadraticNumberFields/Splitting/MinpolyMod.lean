/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Monogenic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Minimal Polynomial mod p

This file classifies the factorization of `X² - d` modulo a prime `p`
and connects it to the Legendre symbol.

## Main Results

### Polynomial lemmas (over any field)

* `sq_sub_C_splits_iff_isSquare`: `(X² - a)` splits ↔ `IsSquare a`
* `sq_sub_C_irreducible_iff_not_isSquare`: `(X² - a)` irreducible
  ↔ `¬ IsSquare a`
* `sq_sub_C_separable_iff`: `(X² - a)` separable ↔ `a ≠ 0`
  (when `char ≠ 2`)

### Connection to the Legendre symbol (over `ZMod p`)

* `sq_sub_splits_mod_iff`: `(X² - d)` splits mod `p`
  ↔ `legendreSym p d = 1`
* `sq_sub_irreducible_mod_iff`: `(X² - d)` irreducible mod `p`
  ↔ `legendreSym p d = -1`
* `legendreSym_eq_zero_iff_dvd`: `legendreSym p d = 0` ↔ `p ∣ d`
* `sq_sub_not_separable_mod`: `p ∣ d` → `(X² - d)` not separable
  mod `p` (for odd `p`)

### Minimal polynomials (TODO)

* `minpoly_generator_mod_four_ne_one`: `minpoly ℤ θ = X² - d`
  when `d % 4 ≠ 1`
* `minpoly_generator_mod_four_eq_one`: `minpoly ℤ θ = X² - X - (d-1)/4`
  when `d % 4 = 1`

### Special case: p = 2 (TODO)

* Case analysis on `d mod 4` and `d mod 8`
-/

open Polynomial

namespace QuadraticNumberFields
namespace Splitting

/-! ## General polynomial lemmas for `X² - C a` -/

section PolynomialLemmas

variable {F : Type*} [Field F]

/-- `X² - C a` splits over a field iff `a` is a square. -/
theorem sq_sub_C_splits_iff_isSquare (a : F) :
    (X ^ 2 - C a : F[X]).Splits ↔ IsSquare a := by
  constructor
  · intro hs
    by_contra hna
    have hroots : (X ^ 2 - C a : F[X]).roots = 0 :=
      nthRoots_two_eq_zero_iff.mpr hna
    have h := hs.natDegree_eq_card_roots
    rw [natDegree_X_pow_sub_C, hroots, Multiset.card_zero] at h
    exact absurd h (by norm_num)
  · intro ha
    obtain ⟨r, rfl⟩ := ha
    have hev : eval r (X ^ 2 - C (r * r) : F[X]) = 0 := by
      simp [eval_sub, eval_C, sq]
    exact Splits.of_natDegree_eq_two natDegree_X_pow_sub_C hev

/-- `X² - C a` is irreducible over a field iff `a` is not a square. -/
theorem sq_sub_C_irreducible_iff_not_isSquare (a : F) :
    Irreducible (X ^ 2 - C a : F[X]) ↔ ¬ IsSquare a := by
  have hm := monic_X_pow_sub_C a two_ne_zero (R := F)
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three
      natDegree_X_pow_sub_C.ge
      (natDegree_X_pow_sub_C.le.trans (by norm_num))]
  exact nthRoots_two_eq_zero_iff

/-- `X² - C a` is separable iff `a ≠ 0` (when `char ≠ 2`). -/
theorem sq_sub_C_separable_iff (hchar : (2 : F) ≠ 0) (a : F) :
    (X ^ 2 - C a : F[X]).Separable ↔ a ≠ 0 := by
  constructor
  · intro h ha
    rw [ha, map_zero, sub_zero] at h
    exact not_isUnit_X (h.squarefree _ ⟨1, by ring⟩)
  · intro ha
    exact separable_X_pow_sub_C a (by exact_mod_cast hchar) ha

end PolynomialLemmas

/-! ## Factorization mod p via Legendre symbol -/

section LegendreSymbol

variable (d : ℤ) (p : ℕ) [Fact p.Prime]

/-- `X² - d` splits mod `p` iff `legendreSym p d = 1` (when `p ∤ d`). -/
theorem sq_sub_splits_mod_iff (hpd : (d : ZMod p) ≠ 0) :
    (X ^ 2 - C (d : ZMod p) : (ZMod p)[X]).Splits ↔
      legendreSym p d = 1 := by
  rw [sq_sub_C_splits_iff_isSquare, legendreSym.eq_one_iff p hpd]

/-- `X² - d` is irreducible mod `p` iff `legendreSym p d = -1`. -/
theorem sq_sub_irreducible_mod_iff :
    Irreducible (X ^ 2 - C (d : ZMod p) : (ZMod p)[X]) ↔
      legendreSym p d = -1 := by
  rw [sq_sub_C_irreducible_iff_not_isSquare,
      legendreSym.eq_neg_one_iff]

/-- `legendreSym p d = 0` iff `p ∣ d`. -/
theorem legendreSym_eq_zero_iff_dvd :
    legendreSym p d = 0 ↔ (p : ℤ) ∣ d := by
  rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- When `p ∣ d` (odd `p`), `X² - d` is not separable mod `p`. -/
theorem sq_sub_not_separable_mod (hp2 : p ≠ 2)
    (hpd : (p : ℤ) ∣ d) :
    ¬ (X ^ 2 - C (d : ZMod p) : (ZMod p)[X]).Separable := by
  have hd0 : (d : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hpd
  have hchar : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h)
      (Fact.out : Nat.Prime p).two_le)
  rw [sq_sub_C_separable_iff hchar, not_not]
  exact hd0

end LegendreSymbol

/-! ## Minimal polynomials

The minimal polynomial of the ring-of-integers generator `θ` depends
on `d mod 4`:
- `d % 4 ≠ 1`: `θ = √d`, minpoly = `X² - d`
- `d % 4 = 1`: `θ = (1 + √d)/2`, minpoly = `X² - X - (d-1)/4`

These are proved once `ringOfIntegersGenerator` is defined in
`Monogenic.lean`.
-/

-- TODO: compute minpoly of θ in each case
-- theorem minpoly_generator_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
--     minpoly ℤ (ringOfIntegersGenerator d) = X ^ 2 - C d := ...

-- theorem minpoly_generator_mod_four_eq_one (hd4 : d % 4 = 1) :
--     minpoly ℤ (ringOfIntegersGenerator d) =
--       X ^ 2 - X - C ((d - 1) / 4) := ...

/-! ## Special case: p = 2

For p = 2 the Legendre symbol is not defined (p must be odd).
Instead we use direct case analysis on d mod 4 and d mod 8:

  d ≡ 2, 3 mod 4:  X² - d ≡ X² mod 2  (double root)  → ramified
  d ≡ 1 mod 8:     X² - X - (d-1)/4 ≡ X(X-1) mod 2   → split
  d ≡ 5 mod 8:     X² - X - (d-1)/4 ≡ X²+X+1 mod 2   → inert
-/

-- TODO: case analysis for p = 2
-- theorem splitting_at_two_ramified (hd4 : d % 4 ≠ 1) :
--     ... 1 < ramificationIdxIn (Ideal.span {(2 : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) := ...

-- theorem splitting_at_two_split (hd8 : d % 8 = 1) :
--     ... ramificationIdxIn (Ideal.span {(2 : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
--       inertiaDegIn (Ideal.span {(2 : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 := ...

-- theorem splitting_at_two_inert (hd8 : d % 8 = 5) :
--     ... (primesOver (Ideal.span {(2 : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard = 1 ∧
--       ramificationIdxIn (Ideal.span {(2 : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 := ...

end Splitting
end QuadraticNumberFields
