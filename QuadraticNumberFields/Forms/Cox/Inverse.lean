/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Cox.Bridge
import QuadraticNumberFields.Qsqrtd.TraceNorm
import QuadraticNumberFields.RingOfIntegers.Basis
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.RingOfIntegers.Norm
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
to the forward Cox map defined in `QuadraticNumberFields.Forms.Cox.Bridge`.

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

/-- For a nonzero integral ideal `I` of `𝓞K`, an oriented `ℤ`-basis is a basis
`(α, β)` whose orientation ratio `(α β' - α' β) / √d` is positive. This picks a
proper-equivalence class of binary quadratic forms. -/
structure OrientedBasis (I : Ideal 𝓞K) where
  basis : Basis (Fin 2) ℤ I
  oriented : imPartRatio (((basis 0 : 𝓞K) : K) * star ((basis 1 : 𝓞K) : K) -
    ((basis 1 : 𝓞K) : K) * star ((basis 0 : 𝓞K) : K)) > 0

/-- The determinant of an oriented ideal basis relative to the `d % 4 ≠ 1`
standard integral basis has absolute value `N(I)`. -/
theorem OrientedBasis.det_ne_one_natAbs_eq_absNorm {I : Ideal 𝓞K}
    (hd4 : d % 4 ≠ 1) (b : OrientedBasis I) :
    ((RingOfIntegers.ringOfIntegersBasisOfModFourNeOne hd4).det ((↑) ∘ b.basis)).natAbs =
      Ideal.absNorm I :=
  Ideal.natAbs_det_basis_change (RingOfIntegers.ringOfIntegersBasisOfModFourNeOne hd4) I b.basis

/-- The determinant of an oriented ideal basis relative to the `d % 4 = 1`
standard integral basis has absolute value `N(I)`. -/
theorem OrientedBasis.det_eq_one_natAbs_eq_absNorm {I : Ideal 𝓞K}
    (hd4 : d % 4 = 1) (b : OrientedBasis I) :
    ((RingOfIntegers.ringOfIntegersBasisOfModFourEqOne hd4).det ((↑) ∘ b.basis)).natAbs =
      Ideal.absNorm I :=
  Ideal.natAbs_det_basis_change (RingOfIntegers.ringOfIntegersBasisOfModFourEqOne hd4) I b.basis

/-- The determinant of an oriented ideal basis relative to the explicit
`d = 1 + 4k` integral basis has absolute value `N(I)`. -/
theorem OrientedBasis.det_eq_natAbs_eq_absNorm {I : Ideal 𝓞K}
    (k : ℤ) (hk : d = 1 + 4 * k) (b : OrientedBasis I) :
    ((RingOfIntegers.ringOfIntegersBasisOfEq k hk).det ((↑) ∘ b.basis)).natAbs = Ideal.absNorm I :=
  Ideal.natAbs_det_basis_change (RingOfIntegers.ringOfIntegersBasisOfEq k hk) I b.basis

/-- Nonzero ideals of `𝓞K` are free `ℤ`-modules of rank 2, so they have bases. -/
noncomputable instance (I : Ideal 𝓞K) (_hI : I ≠ 0) : Module.Free ℤ I := by
  have hfin : Module.Finite ℤ I := inferInstance
  have htors : IsTorsionFree ℤ I := inferInstance
  exact Module.free_of_finite_type_torsion_free' (R := ℤ) (M := I)

/-- Every nonzero integral ideal admits an oriented `ℤ`-basis. -/
noncomputable def idealFin2Basis' (I : Ideal 𝓞K) (hI : I ≠ 0) :
    Basis (Fin 2) ℤ (Submodule.restrictScalars ℤ I) := by
  have hfinrank_OK : Module.finrank ℤ 𝓞K = 2 := by
    by_cases hd4 : d % 4 = 1
    · obtain ⟨k, hk⟩ := RingOfIntegers.exists_k_of_mod_four_eq_one hd4
      subst hk
      let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq (1 + 4 * k) k rfl
      let f : ZOnePlusSqrtdOverTwo k ≃ₗ[ℤ] 𝓞 (Qsqrtd (((1 + 4 * k : ℤ) : ℚ))) :=
        (RingOfIntegers.ringEquivToIntAlgEquiv e.symm).toLinearEquiv
      rw [Module.finrank_eq_card_basis ((QuadraticAlgebra.basis k 1).map f)]
      simp [Fintype.card_fin]
    · let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
      let f : Zsqrtd d ≃ₗ[ℤ] 𝓞 (Qsqrtd (d : ℚ)) :=
        (RingOfIntegers.ringEquivToIntAlgEquiv e.symm).toLinearEquiv
      rw [Module.finrank_eq_card_basis ((QuadraticAlgebra.basis d 0).map f)]
      simp [Fintype.card_fin]
  have hfinrank : Module.finrank ℤ (Submodule.restrictScalars ℤ I) = 2 := by
    rw [← hfinrank_OK]
    apply (Submodule.finiteQuotient_iff (M := 𝓞K) (N := Submodule.restrictScalars ℤ I)).mp
    exact (Ideal.absNorm_ne_zero_iff (I : Ideal 𝓞K)).mp
      (Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩)
  have hcard :
      Fintype.card (Module.Free.ChooseBasisIndex ℤ (Submodule.restrictScalars ℤ I)) = 2 := by
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
noncomputable def normFormOfBasis {I : Ideal 𝓞K} (_hI : I ≠ 0) (b : OrientedBasis I) :
    BinaryQuadraticForm :=
  let α := (b.basis 0 : 𝓞K)
  let β := (b.basis 1 : 𝓞K)
  let N : ℤ := Ideal.absNorm I
  { a := Algebra.norm ℤ α / N
    b := (Algebra.norm ℤ (α + β) - Algebra.norm ℤ α - Algebra.norm ℤ β) / N
    c := Algebra.norm ℤ β / N }

/-- The ideal norm divides the integral norm of each basis vector and of their
sum, so every coefficient of `normFormOfBasis` is an exact integer quotient. -/
theorem absNorm_dvd_norm_basis {I : Ideal 𝓞K} (b : OrientedBasis I) (i : Fin 2) :
    (Ideal.absNorm I : ℤ) ∣ Algebra.norm ℤ (b.basis i : 𝓞K) :=
  absNorm_dvd_norm_of_mem_ideal (b.basis i).2

/-- `N(I)` times the leading coefficient of `normFormOfBasis` recovers `N(α)`. -/
theorem normFormOfBasis_a_mul_absNorm {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I) :
    (normFormOfBasis hI b).a * (Ideal.absNorm I : ℤ) = Algebra.norm ℤ (b.basis 0 : 𝓞K) :=
  Int.ediv_mul_cancel (absNorm_dvd_norm_basis b 0)

/-- `N(I)` times the last coefficient of `normFormOfBasis` recovers `N(β)`. -/
theorem normFormOfBasis_c_mul_absNorm {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I) :
    (normFormOfBasis hI b).c * (Ideal.absNorm I : ℤ) = Algebra.norm ℤ (b.basis 1 : 𝓞K) :=
  Int.ediv_mul_cancel (absNorm_dvd_norm_basis b 1)

/-- `N(I)` times the middle coefficient of `normFormOfBasis` recovers the
polarized norm `N(α + β) - N(α) - N(β) = Tr(α · conj β)`. -/
theorem normFormOfBasis_b_mul_absNorm {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I) :
    (normFormOfBasis hI b).b * (Ideal.absNorm I : ℤ) =
      Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
        Algebra.norm ℤ (b.basis 0 : 𝓞K) - Algebra.norm ℤ (b.basis 1 : 𝓞K) := by
  refine Int.ediv_mul_cancel ?_
  have hsum : ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) ∈ I :=
    Ideal.add_mem I (b.basis 0).2 (b.basis 1).2
  exact dvd_sub (dvd_sub (absNorm_dvd_norm_of_mem_ideal hsum) (absNorm_dvd_norm_basis b 0))
    (absNorm_dvd_norm_basis b 1)

/-- Coefficient-matching criterion for the norm form, independent of the `d % 4`
branch.  If the ideal norm equals the nonzero target leading coefficient `Q.a`,
and the integral norms of the two basis vectors and of their sum match `Q.a²`,
`Q.a · Q.c`, and `Q.a² + Q.a·Q.b + Q.a·Q.c`, then the norm form attached to the
oriented basis is exactly `Q`.

Each branch supplies these four integer identities from its own Cox basis (the
`α = (a, 0)`, `β = (b/2, -1)` coordinates for `d % 4 ≠ 1`; the
`β = (b/2, -1/2)` coordinates for `d % 4 = 1`).  The norms collapse to the same
shape in both cases, so the `Q.a = N(I)` cancellation is shared here. -/
theorem normFormOfBasis_eq_of_norms {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I)
    {Q : BinaryQuadraticForm} (ha : Q.a ≠ 0)
    (hN : (Ideal.absNorm I : ℤ) = Q.a)
    (hn0 : Algebra.norm ℤ (b.basis 0 : 𝓞K) = Q.a ^ 2)
    (hn1 : Algebra.norm ℤ (b.basis 1 : 𝓞K) = Q.a * Q.c)
    (hns : Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) =
      Q.a ^ 2 + Q.a * Q.b + Q.a * Q.c) :
    normFormOfBasis hI b = Q := by
  ext
  · apply mul_right_cancel₀ ha
    rw [← hN, normFormOfBasis_a_mul_absNorm hI b, hn0, hN]
    ring
  · apply mul_right_cancel₀ ha
    rw [← hN, normFormOfBasis_b_mul_absNorm hI b, hns, hn0, hn1, hN]
    ring
  · apply mul_right_cancel₀ ha
    rw [← hN, normFormOfBasis_c_mul_absNorm hI b, hn1, hN]
    ring

/-- The integral norm of `x : 𝓞K`, viewed in `ℚ`, is the quadratic form
`re² − d · im²` of its coordinates in `K`. This bridges `Algebra.norm ℤ` to the
explicit `Qsqrtd` norm formula, threading past the `Algebra ℚ K` diamond exactly
as in `RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one`. -/
theorem fieldNorm_int_eq (x : 𝓞K) :
    (Algebra.norm ℤ x : ℚ) = ((x : K).re) ^ 2 - (d : ℚ) * ((x : K).im) ^ 2 := by
  rw [Algebra.coe_norm_int, Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm,
    RingOfIntegers.TraceNorm.norm_eq_sqr_minus_d_sqr]

/-- Evaluating `normFormOfBasis` at an integral linear combination of the
oriented basis recovers the field norm after multiplying by the ideal norm. -/
theorem normFormOfBasis_eval_mul_absNorm {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) (x y : ℤ) :
    (normFormOfBasis hI b).eval x y * (Ideal.absNorm I : ℤ) =
      Algebra.norm ℤ (x • (b.basis 0 : 𝓞K) + y • (b.basis 1 : 𝓞K)) := by
  let α : 𝓞K := b.basis 0
  let β : 𝓞K := b.basis 1
  have ha := normFormOfBasis_a_mul_absNorm (d := d) hI b
  have hb := normFormOfBasis_b_mul_absNorm (d := d) hI b
  have hc := normFormOfBasis_c_mul_absNorm (d := d) hI b
  have haQ :
      ((normFormOfBasis hI b).a * (Ideal.absNorm I : ℤ) : ℚ) =
        (Algebra.norm ℤ α : ℚ) := by
    simpa [α] using congrArg (fun z : ℤ => (z : ℚ)) ha
  have hbQ :
      ((normFormOfBasis hI b).b * (Ideal.absNorm I : ℤ) : ℚ) =
        (Algebra.norm ℤ (α + β) : ℚ) - Algebra.norm ℤ α - Algebra.norm ℤ β := by
    simpa [α, β] using congrArg (fun z : ℤ => (z : ℚ)) hb
  have hcQ :
      ((normFormOfBasis hI b).c * (Ideal.absNorm I : ℤ) : ℚ) =
        (Algebra.norm ℤ β : ℚ) := by
    simpa [β] using congrArg (fun z : ℤ => (z : ℚ)) hc
  have hnorm_quad :
      (Algebra.norm ℤ (x • α + y • β) : ℚ) =
        (x : ℚ) ^ 2 * (Algebra.norm ℤ α : ℚ) +
          (x : ℚ) * (y : ℚ) *
            ((Algebra.norm ℤ (α + β) : ℚ) - Algebra.norm ℤ α - Algebra.norm ℤ β) +
          (y : ℚ) ^ 2 * (Algebra.norm ℤ β : ℚ) := by
    simp only [fieldNorm_int_eq]
    push_cast
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    simp
    ring
  have hcast :
      ((normFormOfBasis hI b).eval x y * (Ideal.absNorm I : ℤ) : ℚ) =
        (Algebra.norm ℤ (x • (b.basis 0 : 𝓞K) + y • (b.basis 1 : 𝓞K)) : ℚ) := by
    rw [hnorm_quad]
    simp only [α, β]
    rw [← hbQ, ← haQ, ← hcQ]
    simp [BinaryQuadraticForm.eval]
    ring
  exact_mod_cast hcast

/-- The norm form evaluates to the exact integer quotient
`N(xα + yβ) / N(I)`. -/
theorem normFormOfBasis_eval_eq_norm_ediv_absNorm {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) (x y : ℤ) :
    (normFormOfBasis hI b).eval x y =
      Algebra.norm ℤ (x • (b.basis 0 : 𝓞K) + y • (b.basis 1 : 𝓞K)) /
        (Ideal.absNorm I : ℤ) := by
  have hN : (Ideal.absNorm I : ℤ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  rw [← normFormOfBasis_eval_mul_absNorm hI b x y]
  exact (Int.mul_ediv_cancel ((normFormOfBasis hI b).eval x y) hN).symm

/-- For an imaginary field (`d < 0`), the integral norm of a nonzero algebraic
integer is strictly positive: `N(x) = re² + |d|·im² > 0`. -/
theorem norm_int_pos (hdneg : d < 0) {x : 𝓞K} (hx : x ≠ 0) :
    0 < Algebra.norm ℤ x := by
  have hxK : (x : K) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝓞K K) (IsFractionRing.injective 𝓞K K)).mpr hx
  have hcoord : (x : K).re ≠ 0 ∨ (x : K).im ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    exact hxK (QuadraticAlgebra.ext h.1 (by simp [h.2]))
  have hd' : (d : ℚ) < 0 := by exact_mod_cast hdneg
  have hpos : (0 : ℚ) < (Algebra.norm ℤ x : ℚ) := by
    rw [fieldNorm_int_eq]
    rcases hcoord with hre | him
    · have : 0 < ((x : K).re) ^ 2 := by positivity
      nlinarith [mul_nonneg (neg_nonneg.mpr hd'.le) (sq_nonneg ((x : K).im))]
    · have : 0 < ((x : K).im) ^ 2 := by positivity
      nlinarith [sq_nonneg ((x : K).re), mul_pos (neg_pos.mpr hd') this]
  exact_mod_cast hpos

/-- The ideal norm of a nonzero ideal is a strictly positive integer. -/
theorem absNorm_pos {I : Ideal 𝓞K} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℤ) := by
  have h0 : Ideal.absNorm I ≠ 0 :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  exact_mod_cast Nat.pos_of_ne_zero h0

/-- For an imaginary field, the norm form attached to an oriented ideal basis is
strictly positive on nonzero integer coordinate vectors. -/
theorem normFormOfBasis_eval_pos_of_ne_zero (hdneg : d < 0) {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < (normFormOfBasis hI b).eval x y := by
  have hlin : x • (b.basis 0 : 𝓞K) + y • (b.basis 1 : 𝓞K) ≠ 0 := by
    intro hzero
    have hsumI : x • b.basis 0 + y • b.basis 1 = 0 := by
      apply Subtype.ext
      simpa using hzero
    have hLI := b.basis.linearIndependent
    let coeff : Fin 2 → ℤ := ![x, y]
    have hsum : ∑ i : Fin 2, coeff i • b.basis i = 0 := by
      simp [coeff, Fin.sum_univ_two, hsumI]
    have hcoeff := Fintype.linearIndependent_iff.mp hLI coeff hsum
    have hx0 : x = 0 := by simpa [coeff] using hcoeff 0
    have hy0 : y = 0 := by simpa [coeff] using hcoeff 1
    exact hxy.elim (fun hx => hx hx0) (fun hy => hy hy0)
  have heval := normFormOfBasis_eval_mul_absNorm hI b x y
  have hN : 0 < (Ideal.absNorm I : ℤ) := absNorm_pos hI
  have hnorm : 0 < Algebra.norm ℤ (x • (b.basis 0 : 𝓞K) + y • (b.basis 1 : 𝓞K)) :=
    norm_int_pos hdneg hlin
  nlinarith

/-- In an imaginary field, the norm form attached to an oriented ideal basis
vanishes only at the zero coordinate vector. -/
theorem normFormOfBasis_eval_eq_zero_iff (hdneg : d < 0) {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) (x y : ℤ) :
    (normFormOfBasis hI b).eval x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    by_contra hxy0
    have hxy : x ≠ 0 ∨ y ≠ 0 := not_and_or.mp hxy0
    have hpos := normFormOfBasis_eval_pos_of_ne_zero hdneg hI b hxy
    exact (ne_of_gt hpos) h
  · rintro ⟨rfl, rfl⟩
    simp [BinaryQuadraticForm.eval]

/-- The leading coefficient of `normFormOfBasis` is positive when `d < 0`: it is
`N(α)/N(I)` with both norms positive. -/
theorem normFormOfBasis_a_pos (hdneg : d < 0) {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) : 0 < (normFormOfBasis hI b).a := by
  have hN : 0 < (Ideal.absNorm I : ℤ) := absNorm_pos hI
  have hα0 : (b.basis 0 : 𝓞K) ≠ 0 := by
    simpa using b.basis.ne_zero 0
  have hnorm : 0 < Algebra.norm ℤ (b.basis 0 : 𝓞K) := norm_int_pos hdneg hα0
  have heq := normFormOfBasis_a_mul_absNorm hI b
  nlinarith [heq, hN, hnorm]

/-- Multiplying the discriminant of `normFormOfBasis` by `N(I)^2` recovers the
polarized discriminant of the two basis vectors. -/
theorem normFormOfBasis_disc_mul_absNorm_sq {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) :
    (normFormOfBasis hI b).disc * (Ideal.absNorm I : ℤ) ^ 2 =
      (Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
        Algebra.norm ℤ (b.basis 0 : 𝓞K) - Algebra.norm ℤ (b.basis 1 : 𝓞K)) ^ 2 -
        4 * Algebra.norm ℤ (b.basis 0 : 𝓞K) * Algebra.norm ℤ (b.basis 1 : 𝓞K) := by
  have ha := normFormOfBasis_a_mul_absNorm hI b
  have hb := normFormOfBasis_b_mul_absNorm hI b
  have hc := normFormOfBasis_c_mul_absNorm hI b
  simp only [BinaryQuadraticForm.disc]
  rw [← hb, ← ha, ← hc]
  ring

/-- The determinant of an oriented ideal basis in the coordinate basis
`(1, √d)`. -/
noncomputable def OrientedBasis.detCoord {I : Ideal 𝓞K} (b : OrientedBasis I) : ℚ :=
  ((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).im -
    ((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).re

/-- In the `d % 4 ≠ 1` branch, the determinant relative to the transported
integral basis is the coordinate determinant. -/
theorem OrientedBasis.det_ne_one_cast_eq_detCoord {I : Ideal 𝓞K}
    (hd4 : d % 4 ≠ 1) (b : OrientedBasis I) :
    (((RingOfIntegers.ringOfIntegersBasisOfModFourNeOne hd4).det ((↑) ∘ b.basis) : ℤ) : ℚ) =
      b.detCoord := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp only [Basis.toMatrix_apply, Function.comp_apply]
  push_cast
  rw [RingOfIntegers.ringOfIntegersBasisOfModFourNeOne_repr_zero hd4 (b.basis 0 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfModFourNeOne_repr_one hd4 (b.basis 1 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfModFourNeOne_repr_zero hd4 (b.basis 1 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfModFourNeOne_repr_one hd4 (b.basis 0 : 𝓞K)]
  unfold OrientedBasis.detCoord
  ring

/-- In the `d = 1 + 4k` branch, the determinant relative to the transported
integral basis is twice the coordinate determinant. -/
theorem OrientedBasis.det_eq_cast_eq_two_detCoord {I : Ideal 𝓞K}
    (k : ℤ) (hk : d = 1 + 4 * k) (b : OrientedBasis I) :
    (((RingOfIntegers.ringOfIntegersBasisOfEq k hk).det ((↑) ∘ b.basis) : ℤ) : ℚ) =
      2 * b.detCoord := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp only [Basis.toMatrix_apply, Function.comp_apply]
  push_cast
  rw [RingOfIntegers.ringOfIntegersBasisOfEq_repr_zero k hk (b.basis 0 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfEq_repr_one k hk (b.basis 1 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfEq_repr_zero k hk (b.basis 1 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfEq_repr_one k hk (b.basis 0 : 𝓞K)]
  unfold OrientedBasis.detCoord
  ring

/-- In the `d % 4 = 1` branch, the determinant relative to the transported
integral basis is twice the coordinate determinant. -/
theorem OrientedBasis.det_eq_one_cast_eq_two_detCoord {I : Ideal 𝓞K}
    (hd4 : d % 4 = 1) (b : OrientedBasis I) :
    (((RingOfIntegers.ringOfIntegersBasisOfModFourEqOne hd4).det ((↑) ∘ b.basis) : ℤ) : ℚ) =
      2 * b.detCoord := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp only [Basis.toMatrix_apply, Function.comp_apply]
  push_cast
  rw [RingOfIntegers.ringOfIntegersBasisOfModFourEqOne_repr_zero hd4 (b.basis 0 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfModFourEqOne_repr_one hd4 (b.basis 1 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfModFourEqOne_repr_zero hd4 (b.basis 1 : 𝓞K),
    RingOfIntegers.ringOfIntegersBasisOfModFourEqOne_repr_one hd4 (b.basis 0 : 𝓞K)]
  unfold OrientedBasis.detCoord
  ring

/-- The polarized discriminant of the two norm values is `4 * d` times the
square of the coordinate determinant of the basis vectors. -/
theorem normFormOfBasis_polarized_disc_eq_det_sq {I : Ideal 𝓞K} (b : OrientedBasis I) :
    ((Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
        Algebra.norm ℤ (b.basis 0 : 𝓞K) - Algebra.norm ℤ (b.basis 1 : 𝓞K)) ^ 2 -
        4 * Algebra.norm ℤ (b.basis 0 : 𝓞K) *
          Algebra.norm ℤ (b.basis 1 : 𝓞K) : ℚ) =
      4 * (d : ℚ) * b.detCoord ^ 2 := by
  have hcoe : (((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K) : 𝓞K) : K) =
      ((b.basis 0 : 𝓞K) : K) + ((b.basis 1 : 𝓞K) : K) := by
    push_cast
    ring
  simp only [fieldNorm_int_eq, hcoe, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  unfold OrientedBasis.detCoord
  ring

/-- The orientation condition says that the coordinate determinant
`α.re * β.im - α.im * β.re` is negative. -/
theorem OrientedBasis.det_neg {I : Ideal 𝓞K} (b : OrientedBasis I) :
    b.detCoord < 0 := by
  have him0 : (((b.basis 0 : 𝓞K) : K) * star ((b.basis 1 : 𝓞K) : K)).im =
      ((b.basis 0 : 𝓞K) : K).re * (-((b.basis 1 : 𝓞K) : K).im) +
        ((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).re := by
    rw [QuadraticAlgebra.im_mul]
    simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  have him1 : (((b.basis 1 : 𝓞K) : K) * star ((b.basis 0 : 𝓞K) : K)).im =
      ((b.basis 1 : 𝓞K) : K).re * (-((b.basis 0 : 𝓞K) : K).im) +
        ((b.basis 1 : 𝓞K) : K).im * ((b.basis 0 : 𝓞K) : K).re := by
    rw [QuadraticAlgebra.im_mul]
    simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  have ho := b.oriented
  rw [imPartRatio_eq_im, QuadraticAlgebra.im_sub, him0, him1] at ho
  unfold OrientedBasis.detCoord
  nlinarith [ho]

/-- The coordinate determinant of an oriented basis has positive square. -/
theorem OrientedBasis.det_sq_pos {I : Ideal 𝓞K} (b : OrientedBasis I) :
    0 < b.detCoord ^ 2 := by
  rw [pow_two]
  exact mul_pos_of_neg_of_neg b.det_neg b.det_neg

/-- If an integral determinant has absolute value `N(I)` and casts to
`detCoord`, then the non-half-integral determinant square formula follows. -/
theorem OrientedBasis.detCoord_sq_eq_absNorm_sq_of_int_det {I : Ideal 𝓞K}
    (b : OrientedBasis I) {z : ℤ} (hzabs : z.natAbs = Ideal.absNorm I)
    (hz : (z : ℚ) = b.detCoord) :
    b.detCoord ^ 2 = (Ideal.absNorm I : ℚ) ^ 2 := by
  have hzsq : (z : ℚ) ^ 2 = (z.natAbs : ℚ) ^ 2 := by
    norm_num [sq, Int.natAbs_mul_self]
  rw [hz, hzabs] at hzsq
  exact hzsq

/-- In the `d % 4 ≠ 1` branch, the coordinate determinant has square `N(I)^2`. -/
theorem OrientedBasis.detCoord_sq_eq_absNorm_sq_of_mod_four_ne_one {I : Ideal 𝓞K}
    (hd4 : d % 4 ≠ 1) (b : OrientedBasis I) :
    b.detCoord ^ 2 = (Ideal.absNorm I : ℚ) ^ 2 :=
  b.detCoord_sq_eq_absNorm_sq_of_int_det (b.det_ne_one_natAbs_eq_absNorm hd4)
    (b.det_ne_one_cast_eq_detCoord hd4)

/-- In the `d % 4 ≠ 1` branch, orientation fixes the determinant sign:
`detCoord = -N(I)`. -/
theorem OrientedBasis.detCoord_eq_neg_absNorm_of_mod_four_ne_one {I : Ideal 𝓞K}
    (hI : I ≠ 0) (hd4 : d % 4 ≠ 1) (b : OrientedBasis I) :
    b.detCoord = -(Ideal.absNorm I : ℚ) := by
  have hsq := b.detCoord_sq_eq_absNorm_sq_of_mod_four_ne_one hd4
  have hdet_neg := b.det_neg
  have hN_pos : (0 : ℚ) < Ideal.absNorm I := by exact_mod_cast absNorm_pos hI
  nlinarith

/-- If an integral determinant has absolute value `N(I)` and casts to
`2 * detCoord`, then the half-integral determinant square formula follows. -/
theorem OrientedBasis.four_detCoord_sq_eq_absNorm_sq_of_int_det {I : Ideal 𝓞K}
    (b : OrientedBasis I) {z : ℤ} (hzabs : z.natAbs = Ideal.absNorm I)
    (hz : (z : ℚ) = 2 * b.detCoord) :
    4 * b.detCoord ^ 2 = (Ideal.absNorm I : ℚ) ^ 2 := by
  have hzsq : (z : ℚ) ^ 2 = (z.natAbs : ℚ) ^ 2 := by
    norm_num [sq, Int.natAbs_mul_self]
  rw [hz, hzabs] at hzsq
  nlinarith

/-- In the `d = 1 + 4k` branch, `4 * detCoord^2 = N(I)^2`. -/
theorem OrientedBasis.four_detCoord_sq_eq_absNorm_sq_of_eq {I : Ideal 𝓞K}
    (k : ℤ) (hk : d = 1 + 4 * k) (b : OrientedBasis I) :
    4 * b.detCoord ^ 2 = (Ideal.absNorm I : ℚ) ^ 2 :=
  b.four_detCoord_sq_eq_absNorm_sq_of_int_det (b.det_eq_natAbs_eq_absNorm k hk)
    (b.det_eq_cast_eq_two_detCoord k hk)

/-- In the `d % 4 = 1` branch, `4 * detCoord^2 = N(I)^2`. -/
theorem OrientedBasis.four_detCoord_sq_eq_absNorm_sq_of_mod_four_eq_one {I : Ideal 𝓞K}
    (hd4 : d % 4 = 1) (b : OrientedBasis I) :
    4 * b.detCoord ^ 2 = (Ideal.absNorm I : ℚ) ^ 2 := by
  obtain ⟨k, hk⟩ := RingOfIntegers.exists_k_of_mod_four_eq_one hd4
  exact b.four_detCoord_sq_eq_absNorm_sq_of_eq k hk

/-- In the `d % 4 = 1` branch, orientation fixes the determinant sign:
`detCoord = -N(I)/2`. -/
theorem OrientedBasis.detCoord_eq_neg_half_absNorm_of_mod_four_eq_one {I : Ideal 𝓞K}
    (hI : I ≠ 0) (hd4 : d % 4 = 1) (b : OrientedBasis I) :
    b.detCoord = -(Ideal.absNorm I : ℚ) / 2 := by
  have hsq := b.four_detCoord_sq_eq_absNorm_sq_of_mod_four_eq_one hd4
  have hdet_neg := b.det_neg
  have hN_pos : (0 : ℚ) < Ideal.absNorm I := by exact_mod_cast absNorm_pos hI
  nlinarith

/-- To prove that `normFormOfBasis` has the field discriminant, it is enough to
identify the square of the coordinate determinant with the ideal norm. -/
theorem normFormOfBasis_hasDiscriminant_of_det_sq {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I)
    (hdet : 4 * (d : ℚ) * b.detCoord ^ 2 =
      (fieldDiscriminant d : ℚ) * (Ideal.absNorm I : ℚ) ^ 2) :
    (normFormOfBasis hI b).HasDiscriminant (fieldDiscriminant d) := by
  have hdiscN := normFormOfBasis_disc_mul_absNorm_sq hI b
  have hdiscNQ := congrArg (fun z : ℤ => (z : ℚ)) hdiscN
  have hkey := normFormOfBasis_polarized_disc_eq_det_sq b
  push_cast at hdiscNQ
  rw [hkey, hdet] at hdiscNQ
  have hNsq_ne : (Ideal.absNorm I : ℚ) ^ 2 ≠ 0 := by
    have hNpos : (0 : ℚ) < (Ideal.absNorm I : ℚ) := by
      exact_mod_cast absNorm_pos hI
    positivity
  have hdiscQ : ((normFormOfBasis hI b).disc : ℚ) = fieldDiscriminant d :=
    mul_right_cancel₀ hNsq_ne hdiscNQ
  unfold HasDiscriminant
  exact_mod_cast hdiscQ

/-- In the `d % 4 ≠ 1` branch, the exact discriminant follows once the coordinate
determinant has square `N(I)^2`. -/
theorem normFormOfBasis_hasDiscriminant_of_det_sq_mod_four_ne_one {I : Ideal 𝓞K}
    (hI : I ≠ 0) (b : OrientedBasis I) (hd4 : d % 4 ≠ 1)
    (hdet : b.detCoord ^ 2 = (Ideal.absNorm I : ℚ) ^ 2) :
    (normFormOfBasis hI b).HasDiscriminant (fieldDiscriminant d) := by
  apply normFormOfBasis_hasDiscriminant_of_det_sq hI b
  rw [fieldDiscriminant_of_mod_four_ne_one hd4]
  push_cast
  rw [hdet]

/-- In the `d % 4 ≠ 1` branch, `normFormOfBasis` has discriminant
`fieldDiscriminant d`. -/
theorem normFormOfBasis_hasDiscriminant_mod_four_ne_one {I : Ideal 𝓞K}
    (hI : I ≠ 0) (b : OrientedBasis I) (hd4 : d % 4 ≠ 1) :
    (normFormOfBasis hI b).HasDiscriminant (fieldDiscriminant d) :=
  normFormOfBasis_hasDiscriminant_of_det_sq_mod_four_ne_one hI b hd4
    (b.detCoord_sq_eq_absNorm_sq_of_mod_four_ne_one hd4)

/-- In the `d % 4 = 1` branch, the coordinate determinant is half the determinant
relative to the integral basis, so the exact discriminant follows from
`4 * detCoord^2 = N(I)^2`. -/
theorem normFormOfBasis_hasDiscriminant_of_det_sq_mod_four_eq_one {I : Ideal 𝓞K}
    (hI : I ≠ 0) (b : OrientedBasis I) (hd4 : d % 4 = 1)
    (hdet : 4 * b.detCoord ^ 2 = (Ideal.absNorm I : ℚ) ^ 2) :
    (normFormOfBasis hI b).HasDiscriminant (fieldDiscriminant d) := by
  apply normFormOfBasis_hasDiscriminant_of_det_sq hI b
  rw [fieldDiscriminant_of_mod_four_eq_one hd4]
  calc
    4 * (d : ℚ) * b.detCoord ^ 2 = (d : ℚ) * (4 * b.detCoord ^ 2) := by ring
    _ = (d : ℚ) * (Ideal.absNorm I : ℚ) ^ 2 := by rw [hdet]

/-- In the `d % 4 = 1` branch, `normFormOfBasis` has discriminant
`fieldDiscriminant d`. -/
theorem normFormOfBasis_hasDiscriminant_mod_four_eq_one {I : Ideal 𝓞K}
    (hI : I ≠ 0) (b : OrientedBasis I) (hd4 : d % 4 = 1) :
    (normFormOfBasis hI b).HasDiscriminant (fieldDiscriminant d) :=
  normFormOfBasis_hasDiscriminant_of_det_sq_mod_four_eq_one hI b hd4
    (b.four_detCoord_sq_eq_absNorm_sq_of_mod_four_eq_one hd4)

/-- The norm form attached to an oriented ideal basis has discriminant equal to
the field discriminant. -/
theorem normFormOfBasis_hasDiscriminant {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) :
    (normFormOfBasis hI b).HasDiscriminant (fieldDiscriminant d) := by
  by_cases hd4 : d % 4 = 1
  · exact normFormOfBasis_hasDiscriminant_mod_four_eq_one hI b hd4
  · exact normFormOfBasis_hasDiscriminant_mod_four_ne_one hI b hd4

/-- The discriminant of `normFormOfBasis` is negative when `d < 0`. The key
identity is `disc(Q) · N(I)² = 4 d · (α.re·β.im − α.im·β.re)²`, whose sign is
forced by `d < 0` and the orientation `α.re·β.im − α.im·β.re < 0`. -/
theorem normFormOfBasis_disc_neg (hdneg : d < 0) {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) : (normFormOfBasis hI b).disc < 0 := by
  have hd' : (d : ℚ) < 0 := by exact_mod_cast hdneg
  have hdet_sq_pos := b.det_sq_pos
  -- Cast the polarized integer discriminant to `4 d · det²`.
  have key := normFormOfBasis_polarized_disc_eq_det_sq b
  -- Relate the integer discriminant to the polarized form via `N(I)²`.
  have hdiscN := normFormOfBasis_disc_mul_absNorm_sq hI b
  -- The polarized integer discriminant is negative.
  have hpol_neg : (Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
        Algebra.norm ℤ (b.basis 0 : 𝓞K) - Algebra.norm ℤ (b.basis 1 : 𝓞K)) ^ 2 -
        4 * Algebra.norm ℤ (b.basis 0 : 𝓞K) * Algebra.norm ℤ (b.basis 1 : 𝓞K) < 0 := by
    have hq : (((Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
          Algebra.norm ℤ (b.basis 0 : 𝓞K) - Algebra.norm ℤ (b.basis 1 : 𝓞K)) ^ 2 -
          4 * Algebra.norm ℤ (b.basis 0 : 𝓞K) * Algebra.norm ℤ (b.basis 1 : 𝓞K) : ℤ) : ℚ) < 0 := by
      push_cast
      rw [key]; nlinarith [hdet_sq_pos, hd']
    exact_mod_cast hq
  have hNsq : 0 < (Ideal.absNorm I : ℤ) ^ 2 := by have := absNorm_pos hI; positivity
  nlinarith [hdiscN, hpol_neg, hNsq]

/-- For an imaginary field (`d < 0`), the norm form of an oriented ideal basis is
positive definite: it has positive leading coefficient and negative
discriminant. -/
theorem normFormOfBasis_isPositiveDefinite (hdneg : d < 0) {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) : (normFormOfBasis hI b).IsPositiveDefinite :=
  ⟨normFormOfBasis_a_pos hdneg hI b, normFormOfBasis_disc_neg hdneg hI b⟩

/-- The norm form attached to an oriented ideal basis is primitive. -/
theorem normFormOfBasis_isPrimitive {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) : (normFormOfBasis hI b).IsPrimitive :=
  isPrimitive_of_hasDiscriminant_fieldDiscriminant (normFormOfBasis hI b)
    (normFormOfBasis_hasDiscriminant hI b)

/-- The primitive positive definite form attached to an oriented ideal basis. -/
noncomputable def primitivePositiveDefiniteNormFormOfBasis (hdneg : d < 0)
    {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I) :
    PrimitivePositiveDefiniteForm (fieldDiscriminant d) :=
  ⟨normFormOfBasis hI b,
    normFormOfBasis_hasDiscriminant hI b, normFormOfBasis_isPrimitive hI b,
    normFormOfBasis_isPositiveDefinite hdneg hI b⟩

/-- The form class attached to a nonzero integral ideal, using an arbitrary
oriented basis of that ideal. -/
noncomputable def formClassOfNonzeroIdeal (hdneg : d < 0) (I : (Ideal 𝓞K)⁰) :
    FormClass (fieldDiscriminant d) := by
  let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
  exact Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d))
    (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)

/-- The inverse-direction map from ideal classes to form classes, choosing a
nonzero integral ideal representative through `ClassGroup.mk0_surjective`. -/
noncomputable def classGroupToFormClass (hdneg : d < 0) :
    ClassGroup 𝓞K → FormClass (fieldDiscriminant d) := fun C =>
  formClassOfNonzeroIdeal hdneg (Classical.choose (ClassGroup.mk0_surjective C))

/-- The chosen inverse map is represented by a nonzero integral ideal in the
given ideal class. -/
theorem exists_mk0_eq_formClassOfNonzeroIdeal (hdneg : d < 0)
    (C : ClassGroup 𝓞K) :
    ∃ I : (Ideal 𝓞K)⁰,
      ClassGroup.mk0 I = C ∧ formClassOfNonzeroIdeal hdneg I = classGroupToFormClass hdneg C := by
  refine ⟨Classical.choose (ClassGroup.mk0_surjective C), ?_, ?_⟩
  · exact Classical.choose_spec (ClassGroup.mk0_surjective C)
  · rfl

end InverseCox
end BinaryQuadraticForm
end QuadraticNumberFields
