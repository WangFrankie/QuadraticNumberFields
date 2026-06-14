/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import QuadraticNumberFields.Zsqrtd.Basic
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic
import QuadraticNumberFields.RingOfIntegers.Classification

open scoped NumberField

/-!
# Standard Integral Bases for Quadratic Rings of Integers

The ring of integers of `ℚ(√d)` has a standard ℤ-basis:
* `{1, √d}` when `d % 4 ≠ 1`;
* `{1, (1+√d)/2}` when `d % 4 = 1`.

This file transports these bases from the project-owned `Zsqrtd` and
`ZOnePlusSqrtdOverTwo` models via the ring-of-integers classification
equivalences, and provides coordinate representation lemmas in the
`Qsqrtd` model.

Material destined for mathlib.
-/

namespace QuadraticNumberFields.RingOfIntegers

open Module

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- Any ring equivalence between two `ℤ`-algebras is a `ℤ`-algebra equivalence,
because integers are preserved. -/
def ringEquivToIntAlgEquiv {R S : Type*} [CommRing R] [Algebra ℤ R]
    [CommRing S] [Algebra ℤ S] (e : R ≃+* S) : R ≃ₐ[ℤ] S :=
  AlgEquiv.ofRingEquiv (f := e) fun n => by
    simp only [eq_intCast, map_intCast]

/-- The standard integral basis of `𝓞 (Qsqrtd d)` in the `d % 4 ≠ 1` branch,
transported from the project-owned `ℤ[√d]` model. -/
noncomputable def ringOfIntegersBasisOfModFourNeOne (hd4 : d % 4 ≠ 1) :
    Basis (Fin 2) ℤ (𝓞 (Qsqrtd (d : ℚ))) := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let f : Zsqrtd d ≃ₐ[ℤ] (𝓞 (Qsqrtd (d : ℚ))) := ringEquivToIntAlgEquiv e.symm
  exact (QuadraticAlgebra.basis d 0).map f.toLinearEquiv

/-- The standard integral basis of `𝓞 (Qsqrtd d)` in the `d % 4 = 1` branch,
transported from the project-owned `ℤ[(1+√d)/2]` model. -/
noncomputable def ringOfIntegersBasisOfModFourEqOne (hd4 : d % 4 = 1) :
    Basis (Fin 2) ℤ (𝓞 (Qsqrtd (d : ℚ))) := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let f : ZOnePlusSqrtdOverTwo (d / 4) ≃ₐ[ℤ] (𝓞 (Qsqrtd (d : ℚ))) :=
    ringEquivToIntAlgEquiv e.symm
  exact (QuadraticAlgebra.basis (d / 4) 1).map f.toLinearEquiv

/-- The standard integral basis of `𝓞 (Qsqrtd d)` when an explicit witness
`d = 1 + 4k` is available. -/
noncomputable def ringOfIntegersBasisOfEq (k : ℤ) (hk : d = 1 + 4 * k) :
    Basis (Fin 2) ℤ (𝓞 (Qsqrtd (d : ℚ))) := by
  subst hk
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq
    (1 + 4 * k) k rfl
  let f : ZOnePlusSqrtdOverTwo k ≃ₐ[ℤ] (𝓞 (Qsqrtd (((1 + 4 * k : ℤ) : ℚ)))) :=
    ringEquivToIntAlgEquiv e.symm
  exact (QuadraticAlgebra.basis k 1).map f.toLinearEquiv

section Repr

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- In the `d % 4 ≠ 1` branch, the first coordinate in the transported integral
basis is the `re` coordinate in `Qsqrtd`. -/
theorem ringOfIntegersBasisOfModFourNeOne_repr_zero (hd4 : d % 4 ≠ 1) (x : 𝓞K) :
    ((ringOfIntegersBasisOfModFourNeOne hd4).repr x 0 : ℚ) = (x : K).re := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  have h := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply d hd4 x
  have hre : ((e x).re : ℚ) = (x : K).re := by
    simpa [Zsqrtd.toQsqrtdHom, Zsqrtd.toQsqrtd] using congrArg QuadraticAlgebra.re h
  change (((QuadraticAlgebra.basis d 0).repr (e x) 0 : ℤ) : ℚ) = (x : K).re
  simpa [QuadraticAlgebra.basis] using hre

/-- In the `d % 4 ≠ 1` branch, the second coordinate in the transported integral
basis is the `im` coordinate in `Qsqrtd`. -/
theorem ringOfIntegersBasisOfModFourNeOne_repr_one (hd4 : d % 4 ≠ 1) (x : 𝓞K) :
    ((ringOfIntegersBasisOfModFourNeOne hd4).repr x 1 : ℚ) = (x : K).im := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  have h := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply d hd4 x
  have him : ((e x).im : ℚ) = (x : K).im := by
    simpa [Zsqrtd.toQsqrtdHom, Zsqrtd.toQsqrtd] using congrArg QuadraticAlgebra.im h
  change (((QuadraticAlgebra.basis d 0).repr (e x) 1 : ℤ) : ℚ) = (x : K).im
  simpa [QuadraticAlgebra.basis] using him

/-- In the `d = 1 + 4k` branch, the first coordinate in the transported integral
basis is `re - im` in `Qsqrtd`. -/
theorem ringOfIntegersBasisOfEq_repr_zero (k : ℤ) (hk : d = 1 + 4 * k) (x : 𝓞K) :
    ((ringOfIntegersBasisOfEq k hk).repr x 0 : ℚ) = (x : K).re - (x : K).im := by
  subst hk
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq
    (1 + 4 * k) k rfl
  have h := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_apply k x
  have hre :
      ((e x).re : ℚ) + ((e x).im : ℚ) / 2 =
        (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).re := by
    simpa [e, ZOnePlusSqrtdOverTwo.toQsqrtdHom, ZOnePlusSqrtdOverTwo.toQsqrtdFun]
      using congrArg QuadraticAlgebra.re h
  have him :
      ((e x).im : ℚ) / 2 = (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).im := by
    simpa [e, ZOnePlusSqrtdOverTwo.toQsqrtdHom, ZOnePlusSqrtdOverTwo.toQsqrtdFun]
      using congrArg QuadraticAlgebra.im h
  have hcoord : ((e x).re : ℚ) =
      (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).re -
        (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).im := by
    nlinarith
  change (((QuadraticAlgebra.basis k 1).repr (e x) 0 : ℤ) : ℚ) =
    (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).re -
      (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).im
  simpa [QuadraticAlgebra.basis] using hcoord

/-- In the `d = 1 + 4k` branch, the second coordinate in the transported integral
basis is `2 * im` in `Qsqrtd`. -/
theorem ringOfIntegersBasisOfEq_repr_one (k : ℤ) (hk : d = 1 + 4 * k) (x : 𝓞K) :
    ((ringOfIntegersBasisOfEq k hk).repr x 1 : ℚ) = 2 * (x : K).im := by
  subst hk
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq
    (1 + 4 * k) k rfl
  have h := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_apply k x
  have him :
      ((e x).im : ℚ) / 2 = (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).im := by
    simpa [e, ZOnePlusSqrtdOverTwo.toQsqrtdHom, ZOnePlusSqrtdOverTwo.toQsqrtdFun]
      using congrArg QuadraticAlgebra.im h
  have hcoord : ((e x).im : ℚ) =
      2 * (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).im := by
    nlinarith
  change (((QuadraticAlgebra.basis k 1).repr (e x) 1 : ℤ) : ℚ) =
    2 * (x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))).im
  simpa [QuadraticAlgebra.basis] using hcoord

end Repr

end QuadraticNumberFields.RingOfIntegers
