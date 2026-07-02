/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Quadratic Polynomials mod p

This file classifies the factorization of `X² - d` modulo a prime `p`
and of `X² - X - k` via the quadratic discriminant, connecting both to the
Legendre symbol over `ZMod p`.

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
* `sq_sub_not_separable_mod`: `p ∣ d` → `(X² - d)` not separable mod `p`
  (for odd `p`)
-/

open Polynomial
open UniqueFactorizationMonoid

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

/-- If `p ≠ 2`, then `(2 : ZMod p)` is nonzero. -/
theorem zmod_two_ne_zero_of_prime_ne_two (hp : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hp (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) (Fact.out : Nat.Prime p).two_le)

/-- The normalized factor set of `X² - r²` over `ZMod p` has two factors when
`r ≠ 0` and `2 ≠ 0`. -/
theorem normalizedFactors_X_sq_sub_C_sq_card_eq_two
    {r : ZMod p} (hr : r ≠ 0) (hp2 : (2 : ZMod p) ≠ 0) :
    ((normalizedFactors ((X ^ 2 - C (r * r)) : (ZMod p)[X])).toFinset.card = 2) := by
  have hfac : (X ^ 2 - C (r * r) : (ZMod p)[X]) = (X - C r) * (X + C r) := by
    rw [show r * r = r ^ 2 by rw [pow_two], map_pow]
    ring
  rw [hfac, normalizedFactors_mul]
  · rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C r)]
    rw [show (X + C r : (ZMod p)[X]) = X - C (-r) by simp]
    rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C (-r : ZMod p))]
    simp only [(Polynomial.monic_X_sub_C r).normalize_eq_self,
      (Polynomial.monic_X_sub_C (-r : ZMod p)).normalize_eq_self,
      Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]
      intro h
      have hcoeff := congrArg (fun q : (ZMod p)[X] => q.coeff 0) h
      have hcoeff' : -r = r := by simpa using hcoeff
      have hzero : (2 : ZMod p) * r = 0 := by
        have : r + r = 0 := by
          nth_rw 1 [← hcoeff']
          simp
        simpa [two_mul] using this
      exact hr ((mul_eq_zero.mp hzero).resolve_left hp2)
  · exact (Polynomial.monic_X_sub_C r).ne_zero
  · rw [show (X + C r : (ZMod p)[X]) = X - C (-r) by simp]
    exact (Polynomial.monic_X_sub_C (-r : ZMod p)).ne_zero

/-- If `legendreSym p d = 1`, then `X² - d` has two normalized factors mod `p`
away from `p ∣ d` and `p = 2`. -/
theorem normalizedFactors_X_sq_sub_C_card_eq_two_of_legendre_eq_one
    (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) (hleg : legendreSym p d = 1) :
    ((normalizedFactors ((X ^ 2 - C (d : ZMod p)) : (ZMod p)[X])).toFinset.card = 2) := by
  have hpd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    exact hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd)
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hpd0).mp hleg
  have hr0 : r ≠ 0 := by
    intro hrz
    exact hpd0 (by simpa [hrz] using hr)
  rw [hr]
  exact normalizedFactors_X_sq_sub_C_sq_card_eq_two p hr0
    (zmod_two_ne_zero_of_prime_ne_two p hp)

/-- If `legendreSym p d ≠ 1`, then `X² - d` has one normalized factor mod `p`
away from `p ∣ d`. -/
theorem normalizedFactors_X_sq_sub_C_card_eq_one_of_legendre_ne_one
    (hpd : ¬ (p : ℤ) ∣ d) (hleg : legendreSym p d ≠ 1) :
    ((normalizedFactors ((X ^ 2 - C (d : ZMod p)) : (ZMod p)[X])).toFinset.card = 1) := by
  have hpd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    exact hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd)
  have hnsq : ¬ IsSquare (d : ZMod p) := by
    intro hs
    exact hleg ((legendreSym.eq_one_iff p hpd0).mpr hs)
  rw [normalizedFactors_irreducible]
  · simp
  · exact (sq_sub_C_irreducible_iff_not_isSquare (F := ZMod p) (d : ZMod p)).mpr hnsq

/-- If the discriminant `1 + 4k` is a nonzero square and `2 ≠ 0`, then
`X² - X - k` has two normalized factors. -/
theorem normalizedFactors_X_sq_sub_X_sub_C_card_eq_two_of_square_discr
    {k r : ZMod p} (hr0 : r ≠ 0) (hp2 : (2 : ZMod p) ≠ 0)
    (hr : (1 : ZMod p) + 4 * k = r * r) :
    ((normalizedFactors ((X ^ 2 - X - C k) : (ZMod p)[X])).toFinset.card = 2) := by
  have hfac : (X ^ 2 - X - C k : (ZMod p)[X]) =
      (X - C ((1 + r) / 2)) * (X - C ((1 - r) / 2)) := by
    let a : ZMod p := (1 + r) / 2
    let b : ZMod p := (1 - r) / 2
    have hsum : a + b = 1 := by
      dsimp [a, b]
      field_simp [hp2]
      ring
    have hprod : a * b = -k := by
      dsimp [a, b]
      field_simp [hp2]
      linear_combination hr
    calc
      (X ^ 2 - X - C k : (ZMod p)[X]) = X ^ 2 - C (a + b) * X + C (a * b) := by
        rw [hsum, hprod]
        simp [sub_eq_add_neg]
      _ = (X - C a) * (X - C b) := by
        rw [map_add, map_mul]
        ring_nf
      _ = (X - C ((1 + r) / 2)) * (X - C ((1 - r) / 2)) := by rfl
  rw [hfac, normalizedFactors_mul]
  · rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C ((1 + r) / 2))]
    rw [normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C ((1 - r) / 2))]
    simp only [(Polynomial.monic_X_sub_C ((1 + r) / 2 : ZMod p)).normalize_eq_self,
      (Polynomial.monic_X_sub_C ((1 - r) / 2 : ZMod p)).normalize_eq_self,
      Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]
      intro h
      have hcoeff := congrArg (fun q : (ZMod p)[X] => q.coeff 0) h
      have halpha : ((1 + r) / 2 : ZMod p) = (1 - r) / 2 := by simpa using hcoeff
      have hmul :
          (2 : ZMod p) * ((1 + r) / 2) = (2 : ZMod p) * ((1 - r) / 2) := by
        rw [halpha]
      field_simp [hp2] at hmul
      have htwo : (2 : ZMod p) * r = 0 := by linear_combination hmul
      exact hr0 ((mul_eq_zero.mp htwo).resolve_left hp2)
  · exact (Polynomial.monic_X_sub_C ((1 + r) / 2 : ZMod p)).ne_zero
  · exact (Polynomial.monic_X_sub_C ((1 - r) / 2 : ZMod p)).ne_zero

/-- If the discriminant `1 + 4k` is not a square, then `X² - X - k` is irreducible. -/
theorem irreducible_X_sq_sub_X_sub_C_of_not_square_discr
    {k : ZMod p} (hnsq : ¬ IsSquare ((1 : ZMod p) + 4 * k)) :
    Irreducible (X ^ 2 - X - C k : (ZMod p)[X]) := by
  have hmon : (X ^ 2 - X - C k : (ZMod p)[X]).Monic := by
    simpa [sub_eq_add_neg, one_mul] using
      (Polynomial.isMonicOfDegree_sub_add_two (R := ZMod p) (1 : ZMod p) (-k)).monic
  have hmd : Polynomial.IsMonicOfDegree (X ^ 2 - X - C k : (ZMod p)[X]) 2 := by
    simpa [sub_eq_add_neg, one_mul] using
      (Polynomial.isMonicOfDegree_sub_add_two (R := ZMod p) (1 : ZMod p) (-k))
  rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three hmd.natDegree_eq.ge
    (by rw [hmd.natDegree_eq]; norm_num)]
  · apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hev : (X ^ 2 - X - C k : (ZMod p)[X]).eval x = 0 :=
      (mem_roots hmon.ne_zero).mp hx
    have hquad' : x * x - x - k = 0 := by
      simpa [eval_sub, eval_pow, pow_two] using hev
    have hquad : (1 : ZMod p) * (x * x) + (-1 : ZMod p) * x + (-k) = 0 := by
      linear_combination hquad'
    have hdisc :=
      discrim_eq_sq_of_quadratic_eq_zero (a := (1 : ZMod p)) (b := (-1 : ZMod p))
        (c := -k) hquad
    apply hnsq
    use (2 : ZMod p) * 1 * x + (-1 : ZMod p)
    simpa [discrim, pow_two] using hdisc

/-- If `legendreSym p d = 1` and `d = 1 + 4k`, then `X² - X - k` has two
normalized factors mod `p`, away from `p ∣ d` and `p = 2`. -/
theorem normalizedFactors_X_sq_sub_X_sub_C_card_eq_two_of_legendre_eq_one
    (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) {k : ℤ}
    (hk : d = 1 + 4 * k) (hleg : legendreSym p d = 1) :
    ((normalizedFactors ((X ^ 2 - X - C (k : ZMod p)) : (ZMod p)[X])).toFinset.card = 2) := by
  have hpd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    exact hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd)
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hpd0).mp hleg
  have hr0 : r ≠ 0 := by
    intro hrz
    exact hpd0 (by simpa [hrz] using hr)
  have hdisc : (1 : ZMod p) + 4 * (k : ZMod p) = r * r := by
    rw [← hr]
    norm_num [hk]
  exact normalizedFactors_X_sq_sub_X_sub_C_card_eq_two_of_square_discr p hr0
    (zmod_two_ne_zero_of_prime_ne_two p hp) hdisc

/-- If `legendreSym p d ≠ 1` and `d = 1 + 4k`, then `X² - X - k` has one
normalized factor mod `p`, away from `p ∣ d`. -/
theorem normalizedFactors_X_sq_sub_X_sub_C_card_eq_one_of_legendre_ne_one
    (hpd : ¬ (p : ℤ) ∣ d) {k : ℤ} (hk : d = 1 + 4 * k)
    (hleg : legendreSym p d ≠ 1) :
    ((normalizedFactors ((X ^ 2 - X - C (k : ZMod p)) : (ZMod p)[X])).toFinset.card = 1) := by
  have hpd0 : (d : ZMod p) ≠ 0 := by
    intro hd
    exact hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd)
  have hnsq : ¬ IsSquare ((1 : ZMod p) + 4 * (k : ZMod p)) := by
    intro hs
    have hdsq : IsSquare (d : ZMod p) := by
      simpa [hk] using hs
    exact hleg ((legendreSym.eq_one_iff p hpd0).mpr hdsq)
  rw [normalizedFactors_irreducible]
  · simp
  · exact irreducible_X_sq_sub_X_sub_C_of_not_square_discr p hnsq

end LegendreSymbol

end Splitting
end QuadraticNumberFields
