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

/-- If `x : K` is fixed by conjugation, then it is the rational scalar `x.re`,
viewed in `K` via `x.re • (1 : K)`. This is the conjugation-fixed (real) analogue
of `eq_imPartRatio_smul_sqrt_of_star_neg`. -/
theorem eq_re_smul_one_of_star_self {x : K} (hx : star x = x) :
    x = (x.re : ℚ) • (1 : K) := by
  have him : x.im = 0 := by
    have him_star : (star x).im = -x.im := by simp [QuadraticAlgebra.im_star]
    rw [hx] at him_star
    linarith
  apply QuadraticAlgebra.ext
  · simp [QuadraticAlgebra.re_one]
  · simp [him, QuadraticAlgebra.im_one]

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

/-- The images in `K` of a `ℤ`-basis of a nonzero ideal are `ℚ`-linearly
independent: a `ℤ`-basis of a full-rank submodule stays independent after
extending scalars to the fraction field `ℚ`. -/
theorem linearIndependent_coeK {I : Ideal 𝓞K}
    (b : Basis (Fin 2) ℤ (Submodule.restrictScalars ℤ I)) :
    LinearIndependent ℚ (fun i => ((b i : 𝓞K) : K)) := by
  set f : (Submodule.restrictScalars ℤ I) →ₗ[ℤ] K :=
    (Algebra.linearMap 𝓞K K).restrictScalars ℤ ∘ₗ
      (Submodule.restrictScalars ℤ I).subtype with hf
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact Subtype.ext (IsFractionRing.injective 𝓞K K hxy)
  have hLIz : LinearIndependent ℤ (fun i => ((b i : 𝓞K) : K)) :=
    b.linearIndependent.map' f hker
  exact hLIz.localization ℚ (nonZeroDivisors ℤ)

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
        simp [h0, h1, himPartRatio_sub]
      rw [hswap]
      have hle : orient b ≤ 0 := le_of_not_gt horiented
      have hlt : orient b < 0 := by
        by_cases hzero : orient b = 0
        · exfalso
          -- The element `α·star β - β·star α` is anti-self-conjugate, so
          -- (via `eq_imPartRatio_smul_sqrt_of_star_neg`) it equals
          -- `(imPartRatio (α·star β - β·star α)) • √dK = 0 • √dK = 0`.
          have hstar :
              star ((b 0 : 𝓞K) * star ((b 1 : 𝓞K) : K) -
                (b 1 : 𝓞K) * star ((b 0 : 𝓞K) : K)) =
                -((b 0 : 𝓞K) * star ((b 1 : 𝓞K) : K) -
                  (b 1 : 𝓞K) * star ((b 0 : 𝓞K) : K)) := by
            have hkey (x y : K) :
                star (x * star y - y * star x) = -(x * star y - y * star x) := by
              rw [sub_eq_add_neg, star_add, star_neg, star_mul, star_mul,
                star_star, star_star]
              ring
            exact hkey _ _
          have hx :
              (b 0 : 𝓞K) * star ((b 1 : 𝓞K) : K) -
                (b 1 : 𝓞K) * star ((b 0 : 𝓞K) : K) = 0 := by
            rw [eq_imPartRatio_smul_sqrt_of_star_neg hstar]
            change orient b • √dK = 0
            rw [hzero, zero_smul]
          -- `hx` says `α · star β = β · star α`, i.e. `α / β` is fixed by
          -- conjugation, hence a rational scalar. So `α` and `β = (b 0, b 1 : K)`
          -- are `ℚ`-linearly dependent, contradicting `linearIndependent_coeK`.
          -- Concretely, `g 0 • α + g 1 • β = 0` with `g 0 = N(β) ≠ 0`, where
          -- `N(β) = (β · star β).re` and `g 1 = -(α · star β).re`.
          set α := ((b 0 : 𝓞K) : K) with hαdef
          set β := ((b 1 : 𝓞K) : K) with hβdef
          have hLI := linearIndependent_coeK b
          have hβ_ne : β ≠ 0 := hLI.ne_zero 1
          have hxsymm : α * star β = β * star α := sub_eq_zero.mp hx
          have hββ : β * star β = ((β * star β).re : ℚ) • (1 : K) :=
            eq_re_smul_one_of_star_self (by rw [star_mul, star_star])
          have hαβ' : α * star β = ((α * star β).re : ℚ) • (1 : K) :=
            eq_re_smul_one_of_star_self (by rw [star_mul, star_star]; exact hxsymm.symm)
          have e0 : β * star β * α = (β * star β).re • α := by
            conv_lhs => rw [hββ]
            rw [smul_one_mul]
          have e1 : α * star β * β = (α * star β).re • β := by
            conv_lhs => rw [hαβ']
            rw [smul_one_mul]
          set g : Fin 2 → ℚ := ![(β * star β).re, -(α * star β).re] with hgdef
          have hsum : ∑ i, g i • ((b i : 𝓞K) : K) = 0 := by
            rw [Fin.sum_univ_two]
            change (β * star β).re • α + (-(α * star β).re) • β = 0
            rw [neg_smul, ← e0, ← e1]; ring
          have hg0 : g 0 = 0 := Fintype.linearIndependent_iff.mp hLI g hsum 0
          have hg0_ne : g 0 ≠ 0 := by
            change (β * star β).re ≠ 0
            intro hc
            have hz : β * star β = 0 := by rw [hββ, hc]; simp
            exact mul_ne_zero hβ_ne (star_ne_zero.mpr hβ_ne) hz
          exact hg0_ne hg0
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
`Q(x, y) = N(x α + y β) / N(I)`. Expanding the norm gives integer coefficients
`a = N(α)/N(I)`, `b = Tr(α β̄)/N(I)`, `c = N(β)/N(I)`. The middle coefficient is
expressed through the polarization identity `Tr(α β̄) = N(α + β) − N(α) − N(β)`,
which keeps every coefficient a difference of integer norms of elements of `𝓞K`
and avoids needing a conjugation on `𝓞K`. -/
noncomputable def normFormOfBasis {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I) :
    BinaryQuadraticForm :=
  let α := (b.basis 0 : 𝓞K)
  let β := (b.basis 1 : 𝓞K)
  let N : ℤ := Ideal.absNorm I
  { a := Algebra.norm ℤ α / N
    b := (Algebra.norm ℤ (α + β) - Algebra.norm ℤ α - Algebra.norm ℤ β) / N
    c := Algebra.norm ℤ β / N }

end InverseCox
end BinaryQuadraticForm
end QuadraticNumberFields
