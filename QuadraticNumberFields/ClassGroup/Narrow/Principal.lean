/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.QuadraticField.Conj
import QuadraticNumberFields.RingOfIntegers.Norm
import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Principal Narrow Class Group Results for Quadratic Fields

This file specializes the positive-principal exact sequence to `𝓞(ℚ(√d))`.
-/

open scoped NumberField nonZeroDivisors

-- Use the canonical `QuadraticAlgebra` algebra structure on standard `Qsqrtd`
-- models in the real-positive Hilbert 90 wrapper.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields

namespace Qsqrtd

open _root_.Qsqrtd

open scoped QuadraticNumberFields.ClassGroup

section PositivePrincipal

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞 (Qsqrtd (d : ℚ))

/-- The totally positive unit subgroup `𝓞(ℚ(√d))ˣ⁺`. -/
noncomputable abbrev positiveUnits : Subgroup OKˣ :=
  NarrowClassGroup.totallyPositiveRingUnits OK (FractionRing OK)

/-- The inclusion `𝓞(ℚ(√d))ˣ⁺ → (Frac 𝓞(ℚ(√d)))ˣ⁺`. -/
noncomputable abbrev positiveUnitsToFractionRing :
    positiveUnits d →* NarrowClassGroup.totallyPositiveUnits (FractionRing OK) :=
  NarrowClassGroup.totallyPositiveRingUnitsToField OK (FractionRing OK)

/-- The positive principal fractional ideals `P_K⁺` for `K = ℚ(√d)`. -/
noncomputable abbrev positivePrincipalIdeals :
    Subgroup ((FractionalIdeal OK⁰ (FractionRing OK))ˣ) :=
  NarrowClassGroup.narrowPrincipalIdeals OK (FractionRing OK)

/-- The map `(Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺`. -/
noncomputable abbrev toPositivePrincipalIdeals :
    NarrowClassGroup.totallyPositiveUnits (FractionRing OK) →* positivePrincipalIdeals d :=
  NarrowClassGroup.toPositivePrincipalIdeals OK (FractionRing OK)

/-- The map `(Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺` is surjective. -/
theorem toPositivePrincipalIdeals_surjective :
    Function.Surjective (toPositivePrincipalIdeals d) :=
  NarrowClassGroup.toPositivePrincipalIdeals_surjective OK (FractionRing OK)

/-- Exactness at `(Frac 𝓞(ℚ(√d)))ˣ⁺` in
`1 → 𝓞(ℚ(√d))ˣ⁺ → (Frac 𝓞(ℚ(√d)))ˣ⁺ → P_K⁺ → 1`. -/
theorem positiveUnitsToFractionRing_mulExact_toPositivePrincipalIdeals :
    Function.MulExact (positiveUnitsToFractionRing d) (toPositivePrincipalIdeals d) :=
  NarrowClassGroup.totallyPositiveRingUnitsToField_mulExact_toPositivePrincipalIdeals
    OK (FractionRing OK)

/-- Principal-layer positive Hilbert 90 for `𝓞(ℚ(√d))`.

If a totally positive fraction-field unit is norm-one for an involution `τ`, then its
positive principal ideal is a positive principal coboundary. This is the concrete
`H¹(G, P_K⁺) = 1` interface used by the strict principal layer. -/
theorem toPositivePrincipalIdeals_coboundary_of_mul_apply_eq_one
    [Nonempty (FractionRing OK →+* ℝ)] (τ : FractionRing OK ≃+* FractionRing OK)
    (hτpos : ∀ x : FractionRing OK,
      NarrowClassGroup.IsTotallyPositive x → NarrowClassGroup.IsTotallyPositive (τ x))
    {a : NarrowClassGroup.totallyPositiveUnits (FractionRing OK)}
    (ha_norm : (a : (FractionRing OK)ˣ) *
      Units.map τ.toMonoidHom (a : (FractionRing OK)ˣ) = 1) :
    ∃ b : NarrowClassGroup.totallyPositiveUnits (FractionRing OK),
      toPositivePrincipalIdeals d a =
        toPositivePrincipalIdeals d b /
          toPositivePrincipalIdeals d
            ⟨Units.map τ.toMonoidHom (b : (FractionRing OK)ˣ),
              hτpos (((b : (FractionRing OK)ˣ) : FractionRing OK)) b.2⟩ :=
  NarrowClassGroup.toPositivePrincipalIdeals_coboundary_of_mul_apply_eq_one
    OK (FractionRing OK) τ hτpos ha_norm

end PositivePrincipal

namespace Real

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "OK" => 𝓞 K

/-- Fixed totally positive ring units in a real quadratic standard model are trivial.

This is the concrete fixed-unit form of the `H²(<σ>, (O_Lˣ)⁺) = 1` input in
Emerton's item 10. If a totally positive unit of `𝓞(ℚ(√d))` is fixed by
conjugation, then it is the positive rational algebraic-integer unit `1`. -/
theorem fixed_totallyPositiveRingUnit_eq_one (hd : 0 < d)
    {u : OKˣ}
    (hu_pos : NarrowClassGroup.IsTotallyPositive (((u : OKˣ) : OK) : K))
    (hfix : star (((u : OKˣ) : OK) : K) = (((u : OKˣ) : OK) : K)) :
    u = 1 := by
  let x : K := (((u : OKˣ) : OK) : K)
  have hx_rat : x = algebraMap ℚ K x.re :=
    (eq_re_smul_one_of_star_self (by simpa [x] using hfix)).trans
      (Algebra.algebraMap_eq_smul_one x.re).symm
  have hnorm_int : Algebra.norm ℤ (u : OK) = 1 ∨ Algebra.norm ℤ (u : OK) = -1 := by
    have hunit : IsUnit (Algebra.norm ℤ (u : OK)) := by
      exact (Units.map (Algebra.norm ℤ : OK →* ℤ) u).isUnit
    simpa using (Int.isUnit_iff.mp hunit)
  have hq_sq : x.re ^ 2 = 1 := by
    have hnorm : x.re ^ 2 = (Algebra.norm ℤ (u : OK) : ℚ) := by
      calc
        x.re ^ 2 = Qsqrtd.norm x := by
          rw [hx_rat]
          exact (QuadraticAlgebra.norm_algebraMap
            (R := ℚ) (a := (d : ℚ)) (b := 0) x.re).symm
        _ = (Algebra.norm ℤ (u : OK) : ℚ) := by
          change Qsqrtd.norm (((u : OKˣ) : OK) : K) =
            (Algebra.norm ℤ (u : OK) : ℚ)
          rw [← QuadraticNumberFields.Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
          exact (Algebra.coe_norm_int (u : OK)).symm
    rcases hnorm_int with h | h
    · simpa [h] using hnorm
    · have hnorm_neg : x.re ^ 2 = -1 := by
        simpa [h] using hnorm
      nlinarith [hnorm_neg, sq_nonneg x.re]
  have hdR : 0 ≤ (d : ℝ) := by
    exact_mod_cast le_of_lt hd
  have hq_pos : 0 < x.re := by
    have hpos := hu_pos (Qsqrtd.realEmbeddingPos d hdR).toRingHom
    rw [show (((u : OKˣ) : OK) : K) = x from rfl] at hpos
    rw [hx_rat] at hpos
    have hposR : (0 : ℝ) < x.re := by
      simpa using hpos
    exact_mod_cast hposR
  have hq : x.re = 1 := by
    rcases sq_eq_one_iff.mp hq_sq with h | h
    · exact h
    · linarith
  have hx_one : x = 1 := by
    rw [hx_rat, hq]
    simp
  apply NumberField.Units.coe_injective K
  simpa [x] using hx_one

/-- Subgroup version of `fixed_totallyPositiveRingUnit_eq_one`.

This states the same fixed-unit triviality directly for the group
`(𝓞(ℚ(√d))ˣ)⁺`. -/
theorem fixed_totallyPositiveRingUnits_eq_one
    (hd : 0 < d)
    {u : NarrowClassGroup.totallyPositiveRingUnits OK K}
    (hfix :
      star ((((u : NarrowClassGroup.totallyPositiveRingUnits OK K) : OKˣ) : OK) : K) =
        ((((u : NarrowClassGroup.totallyPositiveRingUnits OK K) : OKˣ) : OK) : K)) :
    u = 1 := by
  apply Subtype.ext
  exact fixed_totallyPositiveRingUnit_eq_one d hd (u := (u : OKˣ)) (by
    exact u.2) hfix

/-- Concrete positive Hilbert 90 for the real quadratic standard model.

This is the `H¹(G, (Lˣ)⁺) = 1` part of Emerton's item 10, written without a
group-cohomology wrapper: if `a` is totally positive and satisfies
`a * conjugate a = 1`, then `a = b / conjugate b` for a totally positive unit
`b`. The proof is the explicit choice `b = 1 + a`. -/
theorem exists_positive_coboundary_of_mul_star_eq_one
    (hd : 0 < d)
    {a : (Qsqrtd (d : ℚ))ˣ}
    (ha_pos : NarrowClassGroup.IsTotallyPositive (a : Qsqrtd (d : ℚ)))
    (ha_norm : (a : Qsqrtd (d : ℚ)) * star (a : Qsqrtd (d : ℚ)) = 1) :
    ∃ b : (Qsqrtd (d : ℚ))ˣ,
      NarrowClassGroup.IsTotallyPositive (b : Qsqrtd (d : ℚ)) ∧
        (a : Qsqrtd (d : ℚ)) = (b : Qsqrtd (d : ℚ)) / star (b : Qsqrtd (d : ℚ)) := by
  have hdR : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  letI : Nonempty (Qsqrtd (d : ℚ) →+* ℝ) :=
    ⟨(realEmbeddingPos d hdR).toRingHom⟩
  simpa [Qsqrtd.starAlgEquiv_apply] using
    (NarrowClassGroup.exists_positive_coboundary_of_mul_apply_eq_one
      (τ := (starAlgEquiv (d : ℚ)).toRingEquiv)
      (a := a) ha_pos (by simpa [Qsqrtd.starAlgEquiv_apply] using ha_norm))

end Real

end Qsqrtd

end QuadraticNumberFields
