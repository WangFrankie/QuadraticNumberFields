/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Qsqrtd.KummerDedekind
import QuadraticNumberFields.Splitting.MinpolyMod

/-!
# Splitting of the Prime `2` in `Qsqrtd`

This file proves the `p = 2` part of the splitting classification for
`𝓞(ℚ(√d))`.

## Main Results

* `isSplit_two_of_mod_eight_eq_one`
* `isInert_two_of_mod_eight_eq_five`
* `isRamified_two_of_mod_four_ne_one`

## Proof Strategy

```
Classification.lean (𝓞 = ℤ[θ])
         |
Monogenic.lean (exponent θ = 1)
         |
primesOverSpanEquivMonicFactorsMod   ← Kummer-Dedekind from mathlib
         |
monicFactorsMod θ p
= irreducible factors of minpoly ℤ θ mod p
         |
MinpolyMod.lean (X² - d mod p)
         |
case analysis on `d mod 4` and `d mod 8`
```

## Reference

K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Chapter 13, §1, Proposition 13.1.4: `d ≡ 1 (mod 8)` splits, `d ≡ 5 (mod 8)`
is inert, and `d ≡ 2, 3 (mod 4)` ramifies.
-/
attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal
open Polynomial
open UniqueFactorizationMonoid

namespace QuadraticNumberFields

namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- `𝔭(p)` is shared from `Splitting.Defs`; `𝓞(d)` and `θ(d)` are shared from
-- `Splitting.Qsqrtd.Monogenic`.
-- The numerical invariants `e/f/g` and the monic-factor set `M` are file-local specialisations.
local notation3 "e(" p ")" => ramificationIdxIn (𝔭(p)) 𝓞(d)
local notation3 "f(" p ")" => inertiaDegIn (𝔭(p)) 𝓞(d)
local notation3 "g(" p ")" => (primesOver (𝔭(p)) 𝓞(d)).ncard
local notation3 "M(" p ")" => RingOfIntegers.monicFactorsMod θ(d) p

/-! ## The prime `p = 2`

The Legendre symbol is undefined at `2`, so we factor `minpoly ℤ θ` mod `2` by hand.
Everything reduces to computing `M(2)` as a concrete `Finset` over `𝔽₂`, then feeding it to
the same generic plumbing as the odd case:

* `d % 4 ≠ 1`  : `minpoly ≡ (X - d̄)²` (Frobenius)  ⟹ `M(2) = {linear}`     ⟹ ramified
* `d % 8 = 1`  : `minpoly ≡ X(X+1)`                 ⟹ `M(2).card = 2`        ⟹ split
* `d % 8 = 5`  : `minpoly ≡ X² + X + 1` irreducible ⟹ `M(2) = {quadratic}`  ⟹ inert

Key obstruction vs. the odd case: over `𝔽₂` you cannot divide by `2`, so the
`normalizedFactors_X_sq_sub_X_sub_C_*` lemmas (which use `(1 ± r)/2`) do **not** apply.
Use the Frobenius identity `X² - C a = (X - C a)²` (since `ā² = ā` and `2 = 0`) instead.

Reference: Ireland & Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Proposition 13.1.4. -/

/-- **(ramified, `d % 4 ≠ 1`)** `minpoly ≡ (X - d̄)²` mod `2`, a single linear factor. -/
private lemma monicFactorsMod_two_eq_singleton_linear (hd4 : d % 4 ≠ 1) :
    ∃ poly : (ZMod 2)[X], M(2) = {poly} ∧ poly.natDegree = 1 := by
  refine ⟨X - C (d : ZMod 2), ?_, ?_⟩
  · -- M(2)={X-d̄}
    have hmin :
        M(2) = (normalizedFactors ((X ^ 2 - C (d : ZMod 2)) : (ZMod 2)[X])).toFinset := by
      simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).1 hd4]
    have hfrobenius : (X ^ 2 - C (d : ZMod 2) : (ZMod 2)[X]) = (X - C (d : ZMod 2)) ^ 2 := by
        rw [sub_eq_add_neg X,add_pow_char,sub_eq_add_neg,add_left_cancel_iff]
        simp only [← C_pow,ZMod.pow_card,ZModModule.neg_eq_self]
    have hirr := irreducible_X_sub_C (d : ZMod 2)
    rw [hmin, hfrobenius, normalizedFactors_pow]
    rw [normalizedFactors_irreducible hirr, (monic_X_sub_C _).normalize_eq_self]
    simp
  · exact natDegree_X_sub_C _

/-- **(inert, `d % 8 = 5`)** `minpoly ≡ X² + X + 1` mod `2`, irreducible of degree `2`. -/
private lemma monicFactorsMod_two_eq_singleton_quadratic (hd8 : d % 8 = 5) :
    ∃ poly : (ZMod 2)[X], M(2) = {poly} ∧ poly.natDegree = 2 := by
  have : ((X ^ 2 + X + 1 : (ZMod 2)[X]) = (C 1 * X ^ 2 + C 1 * X + C 1:(ZMod 2)[X])) := by
      -- rw [Polynomial.C_mul', Polynomial.C_mul', Polynomial.C_1]
      simp only [Polynomial.C_1, one_mul]
  have deg_eq_two : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by
    exact this ▸ Polynomial.natDegree_quadratic (one_ne_zero : (1 : ZMod 2) ≠ 0)
  refine ⟨X ^ 2 + X + 1, ?_, deg_eq_two⟩
  have hd4: d % 4 = 1 := by omega
    -- d=8*k+5 for some k, so d/4 = 2k + 1 is odd, so (d/4 : ZMod 2) = 1.
  have hmin :
        M(2) =
          (normalizedFactors
            ((X ^ 2 - X - C ((d / 4 : ℤ) : ZMod 2)) : (ZMod 2)[X])).toFinset := by
      simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).2 hd4]
  have hd4_odd : ((d / 4 : ℤ) : ZMod 2) = 1 := by
      have : (d / 4 : ℤ) % 2 = 1 := by omega
      rw [Odd.intCast_zmod_two]
      exact Int.odd_iff.mpr this
  rw [hd4_odd] at hmin
  simp only [sub_eq_add_neg, ZModModule.neg_eq_self, Polynomial.C_1] at hmin
  have hmon : (X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by
    simpa [sub_eq_add_neg, ZModModule.neg_eq_self, Polynomial.C_1, one_mul] using
      (Polynomial.isMonicOfDegree_sub_add_two
        (R := ZMod 2) (1 : ZMod 2) (1 : ZMod 2)).monic
  have hmd : Polynomial.IsMonicOfDegree (X ^ 2 + X + 1 : (ZMod 2)[X]) 2 := by
    simpa [sub_eq_add_neg, ZModModule.neg_eq_self, Polynomial.C_1, one_mul] using
      (Polynomial.isMonicOfDegree_sub_add_two
        (R := ZMod 2) (1 : ZMod 2) (1 : ZMod 2))
  have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three hmd.natDegree_eq.ge
      (by rw [hmd.natDegree_eq]; norm_num)]
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hxroot : (X ^ 2 + X + 1 : (ZMod 2)[X]).eval x = 0 :=
      (mem_roots hmon.ne_zero).mp hx
    fin_cases x <;> norm_num at hxroot <;> contradiction
  rw [hmin, normalizedFactors_irreducible hirr, hmon.normalize_eq_self,
    Multiset.toFinset_singleton]
/-- **(split, `d % 8 = 1`)** `minpoly ≡ X(X+1)` mod `2`, two distinct linear factors. -/
private lemma monicFactorsMod_two_card_eq_two (hd8 : d % 8 = 1) :
    (M(2)).card = 2 := by
  have hd4 : d % 4 = 1 := by omega
  have hmin :
        M(2) =
          (normalizedFactors
            ((X ^ 2 - X - C ((d / 4 : ℤ) : ZMod 2)) : (ZMod 2)[X])).toFinset := by
      simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).2 hd4]
  have hd4_even : ((d / 4 : ℤ) : ZMod 2) = 0 := by
    have : (d / 4 : ℤ) % 2 = 0 := by omega
    exact (Int.even_iff.mpr this).intCast_zmod_two
  rw [hd4_even] at hmin
  simp only [Polynomial.C_0, sub_zero] at hmin
  have hfac : (X ^ 2 - X : (ZMod 2)[X]) = X * (X + 1) := by
    rw [sub_eq_add_neg, ZModModule.neg_eq_self]
    ring
  rw [hmin, hfac, normalizedFactors_mul]
  · have hXirr : Irreducible (X : (ZMod 2)[X]) := by
      simpa using Polynomial.irreducible_X_sub_C (0 : ZMod 2)
    have hXaddOne :
        (X + 1 : (ZMod 2)[X]) = X - C (1 : ZMod 2) := by
      simp [sub_eq_add_neg, ZModModule.neg_eq_self]
    have hXaddOneIrr : Irreducible (X + 1 : (ZMod 2)[X]) := by
      rw [hXaddOne]
      exact Polynomial.irreducible_X_sub_C (1 : ZMod 2)
    have hXaddOneMonic : (X + 1 : (ZMod 2)[X]).Monic := by
      rw [hXaddOne]
      exact Polynomial.monic_X_sub_C (1 : ZMod 2)
    rw [normalizedFactors_irreducible hXirr, normalizedFactors_irreducible hXaddOneIrr]
    simp only [Polynomial.monic_X.normalize_eq_self, hXaddOneMonic.normalize_eq_self,
      Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]
      intro h
      have hcoeff := congrArg (fun q : (ZMod 2)[X] => q.coeff 0) h
      norm_num at hcoeff
  · rw [show (X : (ZMod 2)[X]) = X - C (0 : ZMod 2) by simp]
    exact (Polynomial.monic_X_sub_C (0 : ZMod 2)).ne_zero
  · rw [show (X + 1 : (ZMod 2)[X]) = X - C (1 : ZMod 2) by
      simp [sub_eq_add_neg, ZModModule.neg_eq_self]]
    exact (Polynomial.monic_X_sub_C (1 : ZMod 2)).ne_zero

/-- `(2)` ramifies in `𝓞(ℚ(√d))` when `d ≢ 1 (mod 4)`. -/
theorem isRamified_two_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    Ideal.IsRamifiedIn (𝔭(2)) 𝓞(d) := by
  obtain ⟨poly, hM, hdeg⟩ := monicFactorsMod_two_eq_singleton_linear d hd4
  have hf1 : f((2 : ℕ)) = 1 := by
    rw [inertiaDegIn_eq_natDegree_of_monicFactorsMod_eq_singleton d (2 : ℕ) hM, hdeg]
  have hg1 : g((2 : ℕ)) = 1 := by
    rw [primesOver_ncard_eq_monicFactorsMod_card d (2 : ℕ), hM]
    simp
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭((2 : ℕ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  haveI : (𝔭((2 : ℕ))).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime 2)).irreducible)
  rcases Ideal.efg_trichotomy (𝔭((2 : ℕ))) 𝓞(d) hchar hbot with
    ⟨hg, _, _⟩ | ⟨_, _, hf⟩ | hram
  · omega
  · omega
  · exact (Ideal.one_lt_ramificationIdxIn_iff_efg (𝔭((2 : ℕ))) 𝓞(d) hchar hbot).mpr hram

/-- `(2)` is inert in `𝓞(ℚ(√d))` when `d ≡ 5 (mod 8)`. -/
theorem isInert_two_of_mod_eight_eq_five (hd8 : d % 8 = 5) :
    Ideal.IsInertIn (𝔭(2)) 𝓞(d) := by
  obtain ⟨poly, hM, hdeg⟩ := monicFactorsMod_two_eq_singleton_quadratic d hd8
  have hf2 : f((2 : ℕ)) = 2 := by
    rw [inertiaDegIn_eq_natDegree_of_monicFactorsMod_eq_singleton d (2 : ℕ) hM, hdeg]
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭((2 : ℕ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  haveI : (𝔭((2 : ℕ))).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime 2)).irreducible)
  rcases Ideal.efg_trichotomy (𝔭((2 : ℕ))) 𝓞(d) hchar hbot with
    ⟨_, _, hf⟩ | ⟨hg, he, _⟩ | ⟨_, _, hf⟩
  · omega
  · exact ⟨hg, he⟩
  · omega

/-- `(2)` splits in `𝓞(ℚ(√d))` when `d ≡ 1 (mod 8)`. -/
theorem isSplit_two_of_mod_eight_eq_one (hd8 : d % 8 = 1) :
    Ideal.IsSplitIn (𝔭(2)) 𝓞(d) :=
  isSplitIn_of_monicFactorsMod_card_eq_two d 2 (monicFactorsMod_two_card_eq_two d hd8)

end Splitting
end QuadraticNumberFields
