/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Bridge
import QuadraticNumberFields.Qsqrtd.TraceNorm
import QuadraticNumberFields.RingOfIntegers.Discriminant
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # Inverse of the Cox 7.7 form-class ↔ ideal-class bridge

This file constructs the inverse direction of Cox Theorem 7.7 for imaginary
quadratic fields. Given an ideal class in `𝓞 (Qsqrtd (d : ℚ))`, we choose an
oriented `ℤ`-basis `(α, β)` of a representative integral ideal and attach the
primitive positive definite binary quadratic form

```
Q(x, y) = N_{K/ℚ}(x α + y β) / N(I).
```

The orientation condition `(α β' - α' β) / √d > 0` picks the proper-equivalence
class; changing the oriented basis by `SL₂(ℤ)` yields a properly equivalent form.
The resulting map `ClassGroup (𝓞 K) → FormClass (fieldDiscriminant d)` is inverse
to the forward Cox map defined in `QuadraticNumberFields.Forms.Bridge`.

We work almost entirely with integral ideals, using `ClassGroup.mk0_surjective` to
reduce from fractional ideal classes.
-/

open scoped NumberField nonZeroDivisors
open Module

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section InverseCox

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K
local notation "√dK" => (⟨0, 1⟩ : K)

/-- The absolute field discriminant of `K = Qsqrtd (d : ℚ)` equals the
`fieldDiscriminant` used by the binary-quadratic-form layer. -/
theorem fieldDiscriminant_eq_numberField_discr :
    fieldDiscriminant d = NumberField.discr K := by
  rw [RingOfIntegers.discr_formula d]
  unfold fieldDiscriminant RingOfIntegers.discrFormula
  split_ifs <;> rfl

/-- Any ring equivalence between two `ℤ`-algebras is a `ℤ`-algebra equivalence,
because integers are preserved. -/
private def ringEquivToIntAlgEquiv {R S : Type*} [CommRing R] [Algebra ℤ R]
    [CommRing S] [Algebra ℤ S] (e : R ≃+* S) : R ≃ₐ[ℤ] S :=
  AlgEquiv.ofRingEquiv (f := e) fun n => by
    simp only [eq_intCast, map_intCast]

/-- The coefficient of the canonical generator `√d` in `x : K`, viewed as a
rational number. This extracts the "imaginary part" of `x`. -/
noncomputable def imPartRatio (x : K) : ℚ :=
  (QuadraticAlgebra.basis (d : ℚ) 0).repr x (1 : Fin 2)

/-- If `x : K` is negated by conjugation, then it is a rational multiple of `√d`,
and that multiple is exactly `imPartRatio x`. -/
theorem eq_imPartRatio_smul_sqrt_of_star_neg {x : K} (hx : star x = -x) :
    x = (imPartRatio x : ℚ) • √dK := by
  have hre : x.re = 0 := by
    have hre_star : (star x).re = x.re := by
      simp [QuadraticAlgebra.re_star]
    have hre_neg : (-x).re = -x.re := by simp
    rw [hx] at hre_star
    rw [hre_neg] at hre_star
    linarith
  have him : (imPartRatio x : ℚ) = x.im := by
    simp [imPartRatio, QuadraticAlgebra.basis]
  simpa [hre, him] using (QuadraticAlgebra.mk_eta x).symm

/-- For a nonzero integral ideal `I` of `𝓞K`, an oriented `ℤ`-basis is a basis
`(α, β)` whose orientation ratio `(α β' - α' β) / √d` is positive. This picks a
proper-equivalence class of binary quadratic forms. -/
structure OrientedBasis (I : Ideal 𝓞K) where
  basis : Basis (Fin 2) ℤ I
  oriented : imPartRatio (((basis 0 : 𝓞K) : K) * star ((basis 1 : 𝓞K) : K) -
    ((basis 1 : 𝓞K) : K) * star ((basis 0 : 𝓞K) : K)) > 0

/-- Nonzero ideals of `𝓞K` are free `ℤ`-modules of rank 2, so they admit bases. -/
noncomputable instance (I : Ideal 𝓞K) (hI : I ≠ 0) : Module.Free ℤ I := by
  have hfin : Module.Finite ℤ I := inferInstance
  have htors : IsTorsionFree ℤ I := inferInstance
  exact Module.free_of_finite_type_torsion_free' (R := ℤ) (M := I)

/-- Every nonzero integral ideal admits an oriented `ℤ`-basis. -/
noncomputable def idealFin2Basis' (I : Ideal 𝓞K) (hI : I ≠ 0) : Basis (Fin 2) ℤ (Submodule.restrictScalars ℤ I) := by
  have hfinrank_OK : Module.finrank ℤ 𝓞K = 2 := by
    by_cases hd4 : d % 4 = 1
    · obtain ⟨k, hk⟩ := RingOfIntegers.exists_k_of_mod_four_eq_one hd4
      subst hk
      let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq (1 + 4 * k) k rfl
      let f : ZOnePlusSqrtdOverTwo k ≃ₗ[ℤ] 𝓞 (Qsqrtd (((1 + 4 * k : ℤ) : ℚ))) :=
        (ringEquivToIntAlgEquiv e.symm).toLinearEquiv
      rw [Module.finrank_eq_card_basis ((QuadraticAlgebra.basis k 1).map f)]
      simp [Fintype.card_fin]
    · let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d (by omega)
      let f : Zsqrtd d ≃ₗ[ℤ] 𝓞 (Qsqrtd (d : ℚ)) :=
        (ringEquivToIntAlgEquiv e.symm).toLinearEquiv
      rw [Module.finrank_eq_card_basis ((QuadraticAlgebra.basis d 0).map f)]
      simp [Fintype.card_fin]
  have hfinrank : Module.finrank ℤ (Submodule.restrictScalars ℤ I) = 2 := by
    rw [← hfinrank_OK]
    apply (Submodule.finiteQuotient_iff (M := 𝓞K) (N := Submodule.restrictScalars ℤ I)).mp
    exact (Ideal.absNorm_ne_zero_iff (I : Ideal 𝓞K)).mp
      (Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (Submodule.restrictScalars ℤ I)) = 2 := by
    rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ (Submodule.restrictScalars ℤ I))]
    exact hfinrank
  exact (Module.Free.chooseBasis ℤ (Submodule.restrictScalars ℤ I)).reindex
    (Fintype.equivFinOfCardEq hcard)

/-- Every nonzero integral ideal admits an oriented `ℤ`-basis. -/
noncomputable def orientedBasisOfNeZero (I : Ideal 𝓞K) (hI : I ≠ 0) :
    OrientedBasis I := by
  let b := idealFin2Basis' I hI
  let orient (c : Basis (Fin 2) ℤ (Submodule.restrictScalars ℤ I)) : ℚ :=
    imPartRatio (((c 0 : 𝓞K) : K) * star ((c 1 : 𝓞K) : K) -
      ((c 1 : 𝓞K) : K) * star ((c 0 : 𝓞K) : K))
  by_cases horiented : orient b > 0
  · exact ⟨b, horiented⟩
  · let b' := Basis.reindex b (Equiv.swap 0 1)
    have himPartRatio_sub (x y : K) : imPartRatio (x - y) = imPartRatio x - imPartRatio y := by
      unfold imPartRatio; simp
    have himPartRatio_neg (x : K) : imPartRatio (-x) = -imPartRatio x := by
      unfold imPartRatio; simp
    have horiented' : orient b' > 0 := by
      have hswap : orient b' = -orient b := by
        have hindex0 : ((Equiv.swap (0 : Fin 2) 1).symm 0 : Fin 2) = 1 := by decide
        have hindex1 : ((Equiv.swap (0 : Fin 2) 1).symm 1 : Fin 2) = 0 := by decide
        have h0 : (b' 0 : 𝓞K) = (b 1 : 𝓞K) := by
          dsimp [b']; rw [Basis.reindex_apply, hindex0]
        have h1 : (b' 1 : 𝓞K) = (b 0 : 𝓞K) := by
          dsimp [b']; rw [Basis.reindex_apply, hindex1]
        unfold orient
        simp [h0, h1, himPartRatio_sub, himPartRatio_neg]
      rw [hswap]
      have hle : orient b ≤ 0 := le_of_not_gt horiented
      have hlt : orient b < 0 := by
        by_cases hzero : orient b = 0
        · sorry
        · exact lt_of_le_of_ne hle hzero
      linarith
    exact ⟨b', horiented'⟩

/-- The integer-valued field norm of `x : 𝓞K`, lifted to a rational. This
definition deliberately avoids any `Algebra ℚ K` instance so it sidesteps the
`DivisionRing.toRatAlgebra` / `QuadraticAlgebra.instAlgebra` diamond on `K =
Qsqrtd (d : ℚ) = QuadraticAlgebra ℚ d 0`: by lifting from the integral norm
`Algebra.norm ℤ x : ℤ`, we get a single canonical value rather than two
non-defeq rational candidates. -/
noncomputable def fieldNormOfInteger (x : 𝓞K) : ℚ :=
  (Algebra.norm ℤ x : ℚ)

/-- The field trace of `x : 𝓞K`, as a rational number. With the file-level
`attribute [-instance] DivisionRing.toRatAlgebra` in force, the
`Algebra ℚ K` instance is uniquely `QuadraticAlgebra.instAlgebra`, so this
trace is canonical. -/
noncomputable def fieldTraceOfInteger (x : 𝓞K) : ℚ :=
  Algebra.trace ℚ K (x : K)

/-- For `x ∈ I`, the ideal norm `N(I)` divides the integer norm `N(x)`. -/
theorem absNorm_dvd_norm_of_mem_ideal {I : Ideal 𝓞K} {x : 𝓞K} (hx : x ∈ I) :
    ↑(Ideal.absNorm I) ∣ Algebra.norm ℤ x :=
  Ideal.absNorm_dvd_norm_of_mem hx

/-- For `x ∈ I`, the ideal norm divides the rational norm of `x`. -/
theorem absNorm_dvd_fieldNorm_of_mem {I : Ideal 𝓞K} {x : 𝓞K} (hx : x ∈ I) :
    ↑(Ideal.absNorm I) ∣ fieldNormOfInteger x := by
  unfold fieldNormOfInteger
  exact Int.cast_dvd_cast (Ideal.absNorm I : ℤ) (Algebra.norm ℤ x)
    (Ideal.absNorm_dvd_norm_of_mem hx)

/-- The norm form attached to an oriented basis `(α, β)` of a nonzero ideal `I`:
`Q(x, y) = N(x α + y β) / N(I)`. -/
noncomputable def normFormOfBasis {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I) :
    BinaryQuadraticForm :=
  let α := (b.basis 0 : 𝓞K)
  let β := (b.basis 1 : 𝓞K)
  let αK := (α : K)
  let βK := (β : K)
  let N := Ideal.absNorm I
  let aQ := fieldNormOfInteger α / N
  let bQ := Algebra.trace ℚ K (αK * star βK) / N
  let cQ := fieldNormOfInteger β / N
  sorry

end InverseCox
end BinaryQuadraticForm
end QuadraticNumberFields