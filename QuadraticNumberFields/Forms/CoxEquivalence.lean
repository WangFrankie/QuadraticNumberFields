/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.FreeModule.PID
import QuadraticNumberFields.Forms.InverseCox
import QuadraticNumberFields.Forms.NormFormBasisChange
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Zsqrtd.Basic
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic

/-!
# Cox 7.7 Equivalence Assembly

This file is the assembly layer for the imaginary Cox 7.7 correspondence.  The
forward map from form classes to ideal classes lives in `Forms.Bridge`; the
inverse-direction map from ideal classes to form classes lives in
`Forms.InverseCox`, which imports `Forms.Bridge`.  Therefore the final
equivalence belongs here rather than in `Forms.Bridge`.

## Status

The scaffold lemmas in the `CoxEquivalence` section reduce the equivalence to
representative-level left and right inverse laws.  The `CoxLeftInverse` and
`CoxLeftInverseEqOne` sections prove the two forward-then-inverse branch laws.

The full assembled Cox equivalence still needs the branch-specific principal
ideal relation `(α) · J(Q_b) = (a_Q) · I` for the norm form attached to an
oriented ideal basis.  Once that relation is available, the lemmas in
`CoxAssembly` turn it into the right-inverse branch laws and assemble the
equivalence.
-/

open scoped NumberField nonZeroDivisors
open Module

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section CoxEquivalence

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- Assemble the Cox 7.7 equivalence once the forward and inverse maps have
been proved to be inverse to each other. -/
noncomputable def formClassEquivClassGroupOfInverseLaws (hdneg : d < 0)
    (hleft : ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C)
    (hright : ∀ C : ClassGroup 𝓞K,
      formClassToClassGroup d (classGroupToFormClass hdneg C) = C) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup 𝓞K where
  toFun := formClassToClassGroup d
  invFun := classGroupToFormClass hdneg
  left_inv := hleft
  right_inv := hright

/-- It is enough to prove the left inverse law on form representatives. -/
theorem formClassToClassGroup_leftInverse_of_representatives (hdneg : d < 0)
    (hrep : ∀ Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d),
      classGroupToFormClass hdneg
        (formClassToClassGroup d (Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q)) =
          Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q) :
    ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C := by
  intro C
  induction C using Quotient.inductionOn with
  | h Q => exact hrep Q

/-- It is enough to prove the right inverse law on nonzero integral ideal
representatives. -/
theorem formClassToClassGroup_rightInverse_of_ideal_representatives (hdneg : d < 0)
    (hrep : ∀ I : (Ideal 𝓞K)⁰,
      formClassToClassGroup d (formClassOfNonzeroIdeal hdneg I) = ClassGroup.mk0 I) :
    ∀ C : ClassGroup 𝓞K,
      formClassToClassGroup d (classGroupToFormClass hdneg C) = C := by
  intro C
  obtain ⟨I, hmk, hform⟩ := exists_mk0_eq_formClassOfNonzeroIdeal hdneg C
  rw [← hform, hrep I, hmk]

/-- In the `d % 4 ≠ 1` branch, applying the forward map to the inverse form of
an ideal computes to the Cox ideal class of the attached norm form. -/
theorem formClassToClassGroup_formClassOfNonzeroIdeal_eq_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰) :
    formClassToClassGroup d (formClassOfNonzeroIdeal hdneg I) =
      let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
      idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg hI b) := by
  unfold formClassOfNonzeroIdeal
  exact formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4 _

/-- In the `d % 4 = 1` branch, applying the forward map to the inverse form of
an ideal computes to the Cox ideal class of the attached norm form. -/
theorem formClassToClassGroup_formClassOfNonzeroIdeal_eq_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰) :
    formClassToClassGroup d (formClassOfNonzeroIdeal hdneg I) =
      let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
      idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg hI b) := by
  unfold formClassOfNonzeroIdeal
  exact formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4 _

/-- It is enough to prove the left inverse law separately for the two explicit
Cox ideal class constructors. -/
theorem formClassToClassGroup_leftInverse_of_branch_representatives (hdneg : d < 0)
    (hne : ∀ (hd4 : d % 4 ≠ 1) (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)),
      classGroupToFormClass hdneg (idealClassOfForm_of_mod_four_ne_one d hd4 Q) =
        Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q)
    (heq : ∀ (hd4 : d % 4 = 1) (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)),
      classGroupToFormClass hdneg (idealClassOfForm_of_mod_four_eq_one d hd4 Q) =
        Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q) :
    ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C := by
  apply formClassToClassGroup_leftInverse_of_representatives hdneg
  intro Q
  by_cases hd4 : d % 4 = 1
  · rw [formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4]
    exact heq hd4 Q
  · rw [formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4]
    exact hne hd4 Q

/-- It is enough to prove the right inverse law separately for the two explicit
Cox ideal class constructors attached to norm forms of ideal bases. -/
theorem formClassToClassGroup_rightInverse_of_branch_ideal_representatives (hdneg : d < 0)
    (hne : ∀ (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰),
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       idealClassOfForm_of_mod_four_ne_one d hd4
         (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I)
    (heq : ∀ (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰),
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       idealClassOfForm_of_mod_four_eq_one d hd4
         (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I) :
    ∀ C : ClassGroup 𝓞K,
      formClassToClassGroup d (classGroupToFormClass hdneg C) = C := by
  apply formClassToClassGroup_rightInverse_of_ideal_representatives hdneg
  intro I
  by_cases hd4 : d % 4 = 1
  · rw [formClassToClassGroup_formClassOfNonzeroIdeal_eq_of_mod_four_eq_one hdneg hd4]
    exact heq hd4 I
  · rw [formClassToClassGroup_formClassOfNonzeroIdeal_eq_of_mod_four_ne_one hdneg hd4]
    exact hne hd4 I

/-- Assemble the Cox 7.7 equivalence from representative-level compatibility
of the two maps. -/
noncomputable def formClassEquivClassGroupOfRepresentativeLaws (hdneg : d < 0)
    (hform : ∀ Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d),
      classGroupToFormClass hdneg
        (formClassToClassGroup d (Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q)) =
          Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q)
    (hideal : ∀ I : (Ideal 𝓞K)⁰,
      formClassToClassGroup d (formClassOfNonzeroIdeal hdneg I) = ClassGroup.mk0 I) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup 𝓞K :=
  formClassEquivClassGroupOfInverseLaws hdneg
    (formClassToClassGroup_leftInverse_of_representatives hdneg hform)
    (formClassToClassGroup_rightInverse_of_ideal_representatives hdneg hideal)

end CoxEquivalence

section CoxLeftInverse

/-! ## Left Inverse Round-Trip: `d % 4 ≠ 1` Branch

Goal: `classGroupToFormClass hdneg (idealClassOfForm_of_mod_four_ne_one d hd4 Q) = ⟦Q⟧`.
-/

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- Ring equivalence `𝓞K ≃+* Zsqrtd d` for `d % 4 ≠ 1`. -/
local notation "e" => RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d

/-! ### The Cox generator `β = (b/2) - √d` in `Zsqrtd d` -/

/-- `β = (b/2) - √d`, sign-flipped relative to the ideal generator `(-b/2)+√d`
for correct orientation. -/
def coxBetaZ (d b : ℤ) : Zsqrtd d :=
  (⟨b / 2, -1⟩ : QuadraticAlgebra ℤ d 0)

@[simp] theorem coxBetaZ_re (d b : ℤ) : (coxBetaZ d b).re = b / 2 := rfl
@[simp] theorem coxBetaZ_im (d b : ℤ) : (coxBetaZ d b).im = -1 := rfl

theorem zsqrtd_norm_coxBetaZ (d b : ℤ) : Zsqrtd.norm (coxBetaZ d b) = (b / 2) ^ 2 - d := by
  rw [Zsqrtd.norm_def]; simp; ring

/-- The Cox ideal `J = (a, ⟨-b/2, 1⟩)` in `Zsqrtd d`. -/
def coxIdeal (d a b : ℤ) : Ideal (Zsqrtd d) :=
  Ideal.span ({((a : Zsqrtd d)), (⟨-b / 2, 1⟩ : Zsqrtd d)} : Set (Zsqrtd d))

/-- Helper lemma: `coxBetaZ d b = -⟨-b/2, 1⟩` when `b` is even. -/
theorem coxBetaZ_eq_neg_of_even {d b : ℤ} (hb : Even b) :
    coxBetaZ d b = -(⟨-b / 2, 1⟩ : Zsqrtd d) := by
  obtain ⟨k, hk⟩ := hb
  have hk' : b / 2 = k := by rw [hk]; omega
  ext
  · simp only [coxBetaZ_re, hk']
    calc
      k = -(-k) := by ring
      _ = -((-b : ℤ) / 2) := by rw [hk]; omega
  · simp [coxBetaZ_im]

/-! ### The spanning lemma for the Cox ideal -/

/-- Every element of the Cox ideal `(a, ⟨-b/2, 1⟩)` in `Zsqrtd d` is a ℤ-linear
combination of `{a, coxBetaZ d b}`, provided `b` is even and `4ac = b² - 4d`.

The constructive proof: write `z = u·a + v·⟨-b/2, 1⟩`. Decompose
`u = u₁ + u₂√d`, `v = v₁ + v₂√d`. Then integer coefficients
`m = u₁ + u₂·(b/2) - v₂·c`, `n = -u₂·a - v₁ + v₂·(b/2)` satisfy
`m·a + n·coxBetaZ d b = z`. Integrality uses that `b` is even and `c ∈ ℤ`. -/
theorem mem_span_coxBetaZ_of_mem_ideal {d a b c : ℤ} (hb : Even b)
    (h_disc : 4 * a * c = b ^ 2 - 4 * d) (z : Zsqrtd d)
    (hz : z ∈ Ideal.span ({((a : Zsqrtd d)), (⟨-b / 2, 1⟩ : Zsqrtd d)} :
      Set (Zsqrtd d))) :
    z ∈ Submodule.span ℤ ({((a : Zsqrtd d)), coxBetaZ d b} : Set (Zsqrtd d)) := by
  rcases ((Ideal.mem_span_pair (x := (a : Zsqrtd d)) (y := (⟨-b / 2, 1⟩ : Zsqrtd d))).mp hz) with
    ⟨u, v, hz⟩
  rw [← hz]
  rcases hb with ⟨k, hk⟩
  have hk' : b / 2 = k := by rw [hk]; omega
  have h_ac : a * c = k ^ 2 - d := by
    rw [hk] at h_disc; nlinarith
  let u₁ := u.re; let u₂ := u.im; let v₁ := v.re; let v₂ := v.im
  have hu : u = (⟨u₁, u₂⟩ : Zsqrtd d) := by ext <;> simp [u₁, u₂]
  have hv : v = (⟨v₁, v₂⟩ : Zsqrtd d) := by ext <;> simp [v₁, v₂]
  rw [hu, hv]
  let m := u₁ + u₂ * k - v₂ * c
  let n := -u₂ * a - v₁ + v₂ * k
  have hsum : (m • ((a : Zsqrtd d)) + n • coxBetaZ d b) =
      (⟨u₁, u₂⟩ : Zsqrtd d) * ((a : Zsqrtd d)) +
      (⟨v₁, v₂⟩ : Zsqrtd d) * (⟨-b / 2, 1⟩ : Zsqrtd d) := by
    ext
    · -- real part
      simp only [m, n, zsmul_eq_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, Int.cast_eq, QuadraticAlgebra.im_intCast, mul_zero,
        add_zero, coxBetaZ_re, coxBetaZ_im, Int.reduceNeg, mul_neg, mul_one, neg_zero,
        QuadraticAlgebra.mk_mul_mk, zero_mul]
      rw [hk']
      have hneg : (-b : ℤ) / 2 = -k := by
        rw [show (-b : ℤ) / 2 = -(b / 2) by omega, hk']
      rw [hneg]
      calc
        (u₁ + u₂ * k - v₂ * c) * a + (-u₂ * a - v₁ + v₂ * k) * k
            = u₁ * a - v₁ * k + v₂ * (k * k - c * a) := by ring
        _ = u₁ * a - v₁ * k + v₂ * (k ^ 2 - a * c) := by
          rw [mul_comm c a]; ring
        _ = u₁ * a - v₁ * k + v₂ * d := by rw [h_ac]; ring
        _ = u₁ * a + (v₁ * (-k) + d * v₂) := by ring
    · -- imaginary part
      simp only [m, n, zsmul_eq_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_intCast, Int.cast_eq, QuadraticAlgebra.im_intCast, mul_zero,
        zero_mul, add_zero, coxBetaZ_im, Int.reduceNeg, mul_neg, mul_one, coxBetaZ_re,
        neg_zero, zero_add, QuadraticAlgebra.mk_mul_mk]
      have hneg' : v₂ * ((-b : ℤ) / 2) = -(v₂ * k) := by
        rw [show (-b : ℤ) / 2 = -(b / 2) by omega, hk']
        ring
      rw [hneg']
      ring
  rw [← hsum]
  refine Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-! ### Cox ℤ-basis and left inverse round-trip -/

/-- The ℤ-basis `{a, coxBetaZ d b}` of the Cox ideal. -/
noncomputable def coxIdealBasis {d a b c : ℤ} (ha : a ≠ 0) (hb : Even b)
    (h_disc : 4 * a * c = b ^ 2 - 4 * d) :
    Basis (Fin 2) ℤ (coxIdeal d a b) := by
  have ha_mem : (a : Zsqrtd d) ∈ coxIdeal d a b := by
    dsimp [coxIdeal]; exact Ideal.subset_span (by simp)
  have hbeta_mem : coxBetaZ d b ∈ coxIdeal d a b := by
    dsimp [coxIdeal]
    rw [coxBetaZ_eq_neg_of_even hb]
    exact Submodule.neg_mem _ (Ideal.subset_span (by simp))
  let v0 : coxIdeal d a b := ⟨(a : Zsqrtd d), ha_mem⟩
  let v1 : coxIdeal d a b := ⟨coxBetaZ d b, hbeta_mem⟩
  refine Basis.mk (v := ![v0, v1]) ?_ ?_
  · -- Linear independence (delegated to the generic core)
    rw [Fintype.linearIndependent_iff]
    intro g hsum
    have hzero : g 0 • ((a : Zsqrtd d)) + g 1 • coxBetaZ d b = 0 := by
      have hsum' := congrArg Subtype.val hsum
      simpa [v0, v1] using hsum'
    have him : (g 0 • ((a : Zsqrtd d)) + g 1 • coxBetaZ d b).im = 0 := by rw [hzero]; rfl
    have him_eq : -g 1 = 0 := by
      simpa [coxBetaZ_re, coxBetaZ_im] using him
    have hg1 : g 1 = 0 := by linarith
    have hre : (g 0 • ((a : Zsqrtd d)) + g 1 • coxBetaZ d b).re = 0 := by rw [hzero]; rfl
    rw [hg1] at hre
    have hmul : g 0 * a = 0 := by
      simpa using hre
    have hg0 : g 0 = 0 := by
      exact Or.resolve_right (Int.eq_zero_or_eq_zero_of_mul_eq_zero hmul) ha
    intro i; fin_cases i <;> assumption
  · -- Spanning (delegated to the refactored local lemma)
    intro x hx
    have hx_val : (x : Zsqrtd d) ∈ coxIdeal d a b := x.2
    dsimp [coxIdeal] at hx_val
    have h_span := mem_span_coxBetaZ_of_mem_ideal hb h_disc (x : Zsqrtd d) hx_val
    rcases Submodule.mem_span_insert.mp h_span with ⟨m, z, hz, hz_eq⟩
    rcases Submodule.mem_span_singleton.mp hz with ⟨n, hn⟩
    have h_val : (x : Zsqrtd d) = m • ((a : Zsqrtd d)) + n • coxBetaZ d b := by
      rw [hz_eq, hn]
    have h_sub_val : (m • v0 + n • v1 : coxIdeal d a b).val = (x : Zsqrtd d) := by
      simp [v0, v1, h_val]
    have h_eq : m • v0 + n • v1 = x := Subtype.ext h_sub_val
    rw [← h_eq]
    apply Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-! ### Transport the Cox basis to `𝓞K` -/

/-- The ℤ-algebra equivalence `Zsqrtd d ≃ₐ[ℤ] 𝓞K` (inverse of the ring equivalence). -/
noncomputable def toRingOfIntegersAlgEquiv (hd4 : d % 4 ≠ 1) : Zsqrtd d ≃ₐ[ℤ] 𝓞K :=
  AlgEquiv.ofRingEquiv
    (f := (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4).symm)
    fun n => by simp

/-- The Cox basis transported to `𝓞K` via the ring equivalence. -/
noncomputable def coxIdealBasisOK (hd4 : d % 4 ≠ 1) (_hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    Basis (Fin 2) ℤ (idealOfForm_of_mod_four_ne_one d hd4 Q) := by
  let J := coxIdeal d Q.1.a Q.1.b
  have hb_even : Even Q.1.b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
  have h_disc_eq : 4 * Q.1.a * Q.1.c = Q.1.b ^ 2 - 4 * d := by
    have hdisc_val : Q.1.disc = 4 * d :=
      calc
        Q.1.disc = fieldDiscriminant d := Q.2.1
        _ = 4 * d := fieldDiscriminant_of_mod_four_ne_one hd4
    unfold BinaryQuadraticForm.disc at hdisc_val
    linarith
  let b_J : Basis (Fin 2) ℤ J := coxIdealBasis (ne_of_gt Q.2.2.2.1) hb_even h_disc_eq
  -- Transport: J ≃ₗ[ℤ] idealOfForm Q via Submodule.equivMapOfInjective
  let f_alg : Zsqrtd d ≃ₐ[ℤ] 𝓞K := toRingOfIntegersAlgEquiv hd4
  let f_lin : Zsqrtd d →ₗ[ℤ] 𝓞K := f_alg.toLinearMap
  have h_inj : Function.Injective f_lin := f_alg.injective
  -- View J as ℤ-submodule
  let J_ℤ : Submodule ℤ (Zsqrtd d) :=
    Submodule.restrictScalars ℤ (J : Submodule (Zsqrtd d) (Zsqrtd d))
  -- The equiv we need: J_ℤ ≃ₗ[ℤ] Submodule.map f_lin J_ℤ
  let f_sub : J_ℤ ≃ₗ[ℤ] (Submodule.map f_lin J_ℤ) :=
    Submodule.equivMapOfInjective f_lin h_inj J_ℤ
  -- But we need the codomain to be idealOfForm Q.
  -- We prove: Submodule.map f_lin J_ℤ = idealOfForm Q as ℤ-submodules
  -- (Actually they differ by Submodule.restrictScalars, so we convert)
  let I_ℤ : Submodule ℤ 𝓞K := Submodule.restrictScalars ℤ
    (idealOfForm_of_mod_four_ne_one d hd4 Q)
  have h_map_sets : (Submodule.map f_lin J_ℤ : Set 𝓞K) = (I_ℤ : Set 𝓞K) := by
    ext x; constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, hy_eq⟩
      rw [← hy_eq]
      have hy_J : (y : Zsqrtd d) ∈ J := hy
      have hmem : f_lin y ∈ idealOfForm_of_mod_four_ne_one d hd4 Q := by
        rw [idealOfForm_of_mod_four_ne_one, Ideal.mem_comap]
        dsimp [f_lin, f_alg, toRingOfIntegersAlgEquiv]
        simpa using hy_J
      -- membership in restrictScalars = membership in original
      simpa [I_ℤ] using hmem
    · intro hx
      have hx_ideal : (x : 𝓞K) ∈ idealOfForm_of_mod_four_ne_one d hd4 Q := hx
      rw [idealOfForm_of_mod_four_ne_one, Ideal.mem_comap] at hx_ideal
      -- hx_ideal : e x ∈ J
      apply Submodule.mem_map.mpr
      let y_val : Zsqrtd d :=
        (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4) x
      have hy_J : y_val ∈ J := hx_ideal
      -- Construct y ∈ J_ℤ
      have hy_ℤ : y_val ∈ J_ℤ := hy_J
      let y : J_ℤ := ⟨y_val, hy_ℤ⟩
      -- Goal: ∃ y ∈ J_ℤ, f_lin y = x → refined to y ∈ J_ℤ ∧ f_lin y = x
      refine ⟨y, y.2, ?_⟩
      dsimp [y, y_val, f_lin, f_alg, toRingOfIntegersAlgEquiv]
      simp
  -- From set equality, deduce submodule equality
  have h_map : Submodule.map f_lin J_ℤ = I_ℤ :=
    Submodule.ext fun x => by
      rw [Set.ext_iff] at h_map_sets
      simpa using h_map_sets x
  -- Final equiv: J_ℤ ≃ₗ[ℤ] I_ℤ
  let f_final : J_ℤ ≃ₗ[ℤ] I_ℤ := f_sub.trans (LinearEquiv.ofEq _ _ h_map)
  -- Convert to idealOfForm Q (as ℤ-module)
  let id_tgt : I_ℤ ≃ₗ[ℤ] idealOfForm_of_mod_four_ne_one d hd4 Q :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  -- Convert b_J (Basis ℤ J) → Basis ℤ J_ℤ
  let id_src : J ≃ₗ[ℤ] J_ℤ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let b_J_ℤ : Basis (Fin 2) ℤ J_ℤ := b_J.map id_src
  let b_I_ℤ : Basis (Fin 2) ℤ I_ℤ := b_J_ℤ.map f_final
  exact b_I_ℤ.map id_tgt

/-- The first Cox basis element in `𝓞K` is `e.symm(Q.a)`. -/
theorem coxIdealBasisOK_val_0 (hd4 : d % 4 ≠ 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ((coxIdealBasisOK hd4 hdneg Q) 0 : 𝓞K) =
    (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4).symm
      (Q.1.a : Zsqrtd d) := by
  dsimp [coxIdealBasisOK]
  simp [coxIdealBasis, Basis.coe_mk,  toRingOfIntegersAlgEquiv]

/-- The second Cox basis element in `𝓞K` is `e.symm(coxBetaZ d Q.b)`. -/
theorem coxIdealBasisOK_val_1 (hd4 : d % 4 ≠ 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ((coxIdealBasisOK hd4 hdneg Q) 1 : 𝓞K) =
    (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4).symm
      (coxBetaZ d Q.1.b) := by
  dsimp [coxIdealBasisOK]
  simp [coxIdealBasis, Basis.coe_mk, toRingOfIntegersAlgEquiv]

/-- The K-coordinates of the Cox basis elements (via the ring embedding). -/
theorem coxIdealBasisOK_K_re_im (hd4 : d % 4 ≠ 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    (((coxIdealBasisOK hd4 hdneg Q) 0 : 𝓞K) : K).re = (Q.1.a : ℚ) ∧
    (((coxIdealBasisOK hd4 hdneg Q) 0 : 𝓞K) : K).im = 0 ∧
    (((coxIdealBasisOK hd4 hdneg Q) 1 : 𝓞K) : K).re = (Q.1.b / 2 : ℚ) ∧
    (((coxIdealBasisOK hd4 hdneg Q) 1 : 𝓞K) : K).im = (-1 : ℚ) := by
  have h0 := coxIdealBasisOK_val_0 hd4 hdneg Q
  have h1 := coxIdealBasisOK_val_1 hd4 hdneg Q
  -- h0 : b0 = e.symm(a), h1 : b1 = e.symm(coxBetaZ d Q.1.b)
  -- Ring embedding: (e.symm(z) : K) = Zsqrtd.toQsqrtdHom d z
  -- Coordinates: (a,0) and (b/2,-1)
  let e_equiv := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  have h_embed (x : 𝓞K) : ((x : 𝓞K) : K) = Zsqrtd.toQsqrtdHom d (e_equiv x) := by
    simpa [e_equiv] using
      (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply d hd4 x).symm
  rw [h0, h1, h_embed, h_embed]
  -- Need: Zsqrtd.toQsqrtdHom d a = (a:ℚ, 0) and Zsqrtd.toQsqrtdHom d coxBetaZ = (b/2, -1)
  -- b is even because d % 4 ≠ 1, so b/2 in ℤ equals b/2 in ℚ
  have hb_even : Even Q.1.b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
  obtain ⟨k, hk⟩ := hb_even
  have hk_ℚ : (Q.1.b : ℚ) / 2 = (k : ℚ) := by
    rw [show Q.1.b = (2 * k : ℤ) by omega]
    push_cast; ring
  simp [e_equiv, coxBetaZ_re, coxBetaZ_im, Zsqrtd.toQsqrtdHom,
    RingEquiv.apply_symm_apply, hk_ℚ]
  omega
theorem classGroupToFormClass_idealClassOfForm_leftInverse_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    classGroupToFormClass hdneg
      (idealClassOfForm_of_mod_four_ne_one d hd4 Q) =
      Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q := by
  -- Let I be the Cox ideal as a nonzero-ideal
  let I : (Ideal 𝓞K)⁰ := ⟨idealOfForm_of_mod_four_ne_one d hd4 Q,
    mem_nonZeroDivisors_iff_ne_zero.mpr (idealOfForm_of_mod_four_ne_one_ne_zero d hd4 Q)⟩
  have hI_ne_zero : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  -- Step 1: idealClassOfForm Q = ClassGroup.mk0 I
  have h_idealClass : idealClassOfForm_of_mod_four_ne_one d hd4 Q = ClassGroup.mk0 I := rfl
  rw [h_idealClass]
  -- Step 2: classGroupToFormClass hdneg (ClassGroup.mk0 I)
  -- = formClassOfNonzeroIdeal hdneg (Classical.choose (mk0_surjective (ClassGroup.mk0 I)))
  -- = formClassOfNonzeroIdeal hdneg I  [by L3]
  -- Let K := Classical.choose (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
  -- Then ClassGroup.mk0 K = ClassGroup.mk0 I, so by L3:
  -- formClassOfNonzeroIdeal hdneg K = formClassOfNonzeroIdeal hdneg I
  -- Therefore classGroupToFormClass hdneg (ClassGroup.mk0 I) = formClassOfNonzeroIdeal hdneg I
  have h_class_eq : classGroupToFormClass hdneg (ClassGroup.mk0 I) =
      formClassOfNonzeroIdeal hdneg I := by
    -- classGroupToFormClass C = formClassOfNonzeroIdeal hdneg (choose (mk0_surjective C))
    -- choose_spec gives: ClassGroup.mk0 (choose ...) = C
    -- So by formClassOfNonzeroIdeal_eq_of_mk0_eq, we can swap the representative
    dsimp [classGroupToFormClass]
    let J := Classical.choose (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
    have hJ_mk0 : ClassGroup.mk0 J = ClassGroup.mk0 I :=
      Classical.choose_spec (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
    -- Apply the descent-core lemma L3
    exact formClassOfNonzeroIdeal_eq_of_mk0_eq hdneg J I hJ_mk0
  rw [h_class_eq]
  -- Step 3: formClassOfNonzeroIdeal hdneg I = ⟦primitivePositiveDefiniteNormFormOfBasis ... b⟧
  rw [formClassOfNonzeroIdeal_eq_mk hdneg I
    (b := orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)]
  -- Step 4: ⟦normFormOfBasis hI b⟧ = ⟦Q⟧
  rcases coxIdealBasisOK_K_re_im hd4 hdneg Q with ⟨h0_re, h0_im, h1_re, h1_im⟩
  let b_cox := coxIdealBasisOK hd4 hdneg Q
  set α := ((b_cox 0 : 𝓞K) : K) with hα
  set β := ((b_cox 1 : 𝓞K) : K) with hβ
  -- Wedge: im = 2a > 0 → positive imPartRatio
  have h_wedge_im : (α * star β - β * star α).im = (Q.1.a : ℚ) * 2 := by
    simp [α, β, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul,
      h0_re, h0_im, h1_re, h1_im, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring
  have ha_pos : 0 < (Q.1.a : ℚ) := by exact_mod_cast Q.2.2.2.1
  have hpos : imPartRatio (d := d) (α * star β - β * star α) > 0 := by
    rw [imPartRatio_eq_im, h_wedge_im]; nlinarith
  let b_oriented : OrientedBasis (I : Ideal 𝓞K) :=
    { basis := b_cox, oriented := hpos }
  -- normFormOfBasis hI b_oriented = Q.1: match all three coefficients.
  have h_normform_eq : normFormOfBasis hI_ne_zero b_oriented = Q.1 := by
    -- The two oriented basis vectors are `α` and `β` in `K`.
    have hb0 : ((b_oriented.basis 0 : 𝓞K) : K) = α := hα.symm
    have hb1 : ((b_oriented.basis 1 : 𝓞K) : K) = β := hβ.symm
    have ha_pos_int : 0 < Q.1.a := Q.2.2.2.1
    have hane : Q.1.a ≠ 0 := ne_of_gt ha_pos_int
    -- The ideal norm equals the leading coefficient `a`, via the basis determinant.
    have hdetCoord : b_oriented.detCoord = -(Q.1.a : ℚ) := by
      unfold OrientedBasis.detCoord
      rw [hb0, hb1, h0_re, h0_im, h1_re, h1_im]; ring
    have hz_eq : ((RingOfIntegers.ringOfIntegersBasisOfModFourNeOne hd4).det
        ((↑) ∘ b_oriented.basis) : ℤ) = -Q.1.a := by
      have hz_cast : (((RingOfIntegers.ringOfIntegersBasisOfModFourNeOne hd4).det
          ((↑) ∘ b_oriented.basis) : ℤ) : ℚ) = -(Q.1.a : ℚ) := by
        rw [b_oriented.det_ne_one_cast_eq_detCoord hd4, hdetCoord]
      exact_mod_cast hz_cast
    have hN_eq : (Ideal.absNorm (I : Ideal 𝓞K) : ℤ) = Q.1.a := by
      have hz_abs := b_oriented.det_ne_one_natAbs_eq_absNorm hd4
      rw [hz_eq] at hz_abs
      simp only [Int.natAbs_neg] at hz_abs
      omega
    -- Discriminant relation over `ℚ`: `b² − 4ac = 4d`.
    have hdiscQ : (Q.1.b : ℚ) ^ 2 - 4 * (Q.1.a : ℚ) * (Q.1.c : ℚ) = 4 * (d : ℚ) := by
      have hz : Q.1.disc = 4 * d :=
        calc Q.1.disc = fieldDiscriminant d := Q.2.1
          _ = 4 * d := fieldDiscriminant_of_mod_four_ne_one hd4
      unfold BinaryQuadraticForm.disc at hz
      exact_mod_cast hz
    -- Integer norms of the basis vectors and their sum.
    have hnorm0 : Algebra.norm ℤ (b_oriented.basis 0 : 𝓞K) = Q.1.a ^ 2 := by
      have h : (Algebra.norm ℤ (b_oriented.basis 0 : 𝓞K) : ℚ) = (Q.1.a : ℚ) ^ 2 := by
        rw [fieldNorm_int_eq, hb0, h0_re, h0_im]; ring
      exact_mod_cast h
    have hnorm1 : Algebra.norm ℤ (b_oriented.basis 1 : 𝓞K) = Q.1.a * Q.1.c := by
      have h : (Algebra.norm ℤ (b_oriented.basis 1 : 𝓞K) : ℚ) = (Q.1.a : ℚ) * (Q.1.c : ℚ) := by
        rw [fieldNorm_int_eq, hb1, h1_re, h1_im]
        linear_combination (1 / 4 : ℚ) * hdiscQ
      exact_mod_cast h
    have hnormsum : Algebra.norm ℤ ((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K)) =
        Q.1.a ^ 2 + Q.1.a * Q.1.b + Q.1.a * Q.1.c := by
      have hsum_coe : (((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K) : 𝓞K) : K) =
          α + β := by
        have hpc : (((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K) : 𝓞K) : K) =
            ((b_oriented.basis 0 : 𝓞K) : K) + ((b_oriented.basis 1 : 𝓞K) : K) := by
          push_cast; ring
        rw [hpc, hb0, hb1]
      have h : (Algebra.norm ℤ ((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K)) : ℚ) =
          (Q.1.a : ℚ) ^ 2 + (Q.1.a : ℚ) * (Q.1.b : ℚ) + (Q.1.a : ℚ) * (Q.1.c : ℚ) := by
        rw [fieldNorm_int_eq, hsum_coe]
        simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
          h0_re, h0_im, h1_re, h1_im]
        linear_combination (1 / 4 : ℚ) * hdiscQ
      exact_mod_cast h
    -- The shared, branch-independent criterion finishes the three comparisons.
    exact normFormOfBasis_eq_of_norms hI_ne_zero b_oriented hane hN_eq hnorm0 hnorm1 hnormsum
  -- proper equivalence → equal classes
  have h_equiv : (normFormOfBasis hI_ne_zero
      (orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)).ProperEquivalent
      (normFormOfBasis hI_ne_zero b_oriented) :=
    (normFormOfBasis_properEquivalent hI_ne_zero _ _).symm
  have h_target : (normFormOfBasis hI_ne_zero
      (orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)).ProperEquivalent Q.1 :=
    h_equiv.trans (by rw [h_normform_eq]; exact BinaryQuadraticForm.ProperEquivalent.refl Q.1)
  dsimp [primitivePositiveDefiniteNormFormOfBasis]
  apply Quotient.sound
  simpa using h_target

end CoxLeftInverse

section CoxLeftInverseEqOne

/-! ## Left Inverse Round-Trip: `d % 4 = 1` Branch

Goal: `classGroupToFormClass hdneg (idealClassOfForm_of_mod_four_eq_one d hd4 Q) = ⟦Q⟧`.

The strategy mirrors the `d % 4 ≠ 1` branch (§CoxLeftInverse) but the
generic `CoxIdealRelation` core is instantiated at `bb = 1` (`ZOnePlusSqrtdOverTwo`).
Each of the four inputs to `normFormOfBasis_eq_of_norms` (ideal norm = a,
N(α) = a², N(β) = a·c, N(α+β) = a²+ab+ac) collapses to the same shape because
the K-coordinates of the second Cox basis vector are `(b/2, -1/2)` instead of
`(b/2, -1)`. -/

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- The ℤ-algebra equivalence `ZOnePlusSqrtdOverTwo (d/4) ≃ₐ[ℤ] 𝓞K` for `d % 4 = 1`. -/
noncomputable def toRingOfIntegersAlgEquivEqOne (hd4 : d % 4 = 1) :
    ZOnePlusSqrtdOverTwo (d / 4) ≃ₐ[ℤ] 𝓞K :=
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  AlgEquiv.ofRingEquiv (f := e.symm) fun _ => by simp

/-- The Cox basis transported to `𝓞K` via the `d % 4 = 1` ring equivalence. -/
noncomputable def coxIdealBasisOKEqOne (hd4 : d % 4 = 1) (_hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    Basis (Fin 2) ℤ (idealOfForm_of_mod_four_eq_one d hd4 Q) := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let DD : ℤ := d/4
  let bb : ℤ := 1
  let A : ℤ := Q.1.a
  let B : ℤ := Q.1.b
  let C : ℤ := Q.1.c
  let u : ℤ := -(B + 1) / 2
  have h_odd : Odd B := by
    dsimp [B]
    exact odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
  let k := h_odd.choose
  have hk : B = 2 * k + 1 := h_odd.choose_spec
  have hu : 2 * u = -(B + bb) := by
    dsimp [u, bb]; rw [hk]; omega
  have hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD := by
    have hdisc_val : Q.1.disc = d := by
      have hfield : fieldDiscriminant d = d := fieldDiscriminant_of_mod_four_eq_one hd4
      simpa [hfield] using Q.2.1
    unfold BinaryQuadraticForm.disc at hdisc_val
    dsimp [B] at *
    rw [hk] at hdisc_val
    have hd_eq : d = 4 * (d / 4) + 1 := by
      have := Int.mul_ediv_add_emod d 4
      rw [hd4] at this
      omega
    dsimp [A, B, C, DD, bb]
    rw [hk]
    rw [hdisc_val, hd_eq]
    omega
  let b_generic : Basis (Fin 2) ℤ (CoxIdealRelation.coxIdeal DD bb A u) :=
    CoxIdealRelation.coxIdealBasis (ne_of_gt Q.2.2.2.1) hu hdisc
  let e_symm_alg : ZOnePlusSqrtdOverTwo (d / 4) ≃ₐ[ℤ] 𝓞K :=
    toRingOfIntegersAlgEquivEqOne hd4
  let e_symm_lin : ZOnePlusSqrtdOverTwo (d / 4) →ₗ[ℤ] 𝓞K := e_symm_alg.toLinearMap
  have h_inj : Function.Injective e_symm_lin := e_symm_alg.injective
  let J := CoxIdealRelation.coxIdeal DD bb A u
  let J_ℤ : Submodule ℤ (ZOnePlusSqrtdOverTwo (d / 4)) :=
    Submodule.restrictScalars ℤ (J : Submodule (ZOnePlusSqrtdOverTwo (d / 4))
      (ZOnePlusSqrtdOverTwo (d / 4)))
  let I_ℤ : Submodule ℤ 𝓞K := Submodule.restrictScalars ℤ
    (idealOfForm_of_mod_four_eq_one d hd4 Q)
  have h_map_sets : (Submodule.map e_symm_lin J_ℤ : Set 𝓞K) = (I_ℤ : Set 𝓞K) := by
    ext x; constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, hy_eq⟩
      rw [← hy_eq]
      have hy_J : (y : ZOnePlusSqrtdOverTwo (d / 4)) ∈ J := hy
      have hmem : e_symm_lin y ∈ idealOfForm_of_mod_four_eq_one d hd4 Q := by
        rw [idealOfForm_of_mod_four_eq_one, Ideal.mem_comap]
        dsimp [e_symm_lin, e_symm_alg, toRingOfIntegersAlgEquivEqOne]
        simpa [J, CoxIdealRelation.coxIdeal, DD, bb, A, u] using hy_J
      simpa [I_ℤ] using hmem
    · intro hx
      have hx_ideal : (x : 𝓞K) ∈ idealOfForm_of_mod_four_eq_one d hd4 Q := hx
      rw [idealOfForm_of_mod_four_eq_one, Ideal.mem_comap] at hx_ideal
      apply Submodule.mem_map.mpr
      let y_val : ZOnePlusSqrtdOverTwo (d / 4) := e x
      have hy_J : y_val ∈ J := by
        dsimp [J, y_val, CoxIdealRelation.coxIdeal, DD, bb, A, u]
        simpa using hx_ideal
      have hy_ℤ : y_val ∈ J_ℤ := hy_J
      use y_val
      constructor
      · exact hy_ℤ
      · dsimp [e_symm_lin, y_val, e_symm_alg, toRingOfIntegersAlgEquivEqOne]
        exact e.symm_apply_apply x
  have h_map : Submodule.map e_symm_lin J_ℤ = I_ℤ :=
    Submodule.ext fun x => by
      rw [Set.ext_iff] at h_map_sets
      simpa using h_map_sets x
  let f_final : J_ℤ ≃ₗ[ℤ] I_ℤ :=
    (Submodule.equivMapOfInjective e_symm_lin h_inj J_ℤ).trans
      (LinearEquiv.ofEq _ _ h_map)
  let id_src : J ≃ₗ[ℤ] J_ℤ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let id_tgt : I_ℤ ≃ₗ[ℤ] idealOfForm_of_mod_four_eq_one d hd4 Q :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let b_J_ℤ : Basis (Fin 2) ℤ J_ℤ := b_generic.map id_src
  let b_I_ℤ : Basis (Fin 2) ℤ I_ℤ := b_J_ℤ.map f_final
  exact b_I_ℤ.map id_tgt

/-- The first Cox basis element in the `d % 4 = 1` branch is the transported scalar `a`. -/
theorem coxIdealBasisOKEqOne_val_0 (hd4 : d % 4 = 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ((coxIdealBasisOKEqOne hd4 hdneg Q) 0 : 𝓞K) =
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4).symm
      (Q.1.a : ZOnePlusSqrtdOverTwo (d / 4)) := by
  dsimp [coxIdealBasisOKEqOne]
  simp [CoxIdealRelation.coxIdealBasis, Basis.coe_mk, toRingOfIntegersAlgEquivEqOne]

/-- The second Cox basis element in the `d % 4 = 1` branch is the transported
generic Cox beta. -/
theorem coxIdealBasisOKEqOne_val_1 (hd4 : d % 4 = 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ((coxIdealBasisOKEqOne hd4 hdneg Q) 1 : 𝓞K) =
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4).symm
      (CoxIdealRelation.coxBeta (d / 4) 1 ((-1 + -Q.1.b) / 2)) := by
  dsimp [coxIdealBasisOKEqOne]
  simp [CoxIdealRelation.coxIdealBasis, Basis.coe_mk, toRingOfIntegersAlgEquivEqOne]

/-- The K-coordinates of the transported Cox basis elements (`d % 4 = 1` branch). -/
theorem coxIdealBasisOKEqOne_K_re_im (hd4 : d % 4 = 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    (((coxIdealBasisOKEqOne hd4 hdneg Q) 0 : 𝓞K) : K).re = (Q.1.a : ℚ) ∧
    (((coxIdealBasisOKEqOne hd4 hdneg Q) 0 : 𝓞K) : K).im = 0 ∧
    (((coxIdealBasisOKEqOne hd4 hdneg Q) 1 : 𝓞K) : K).re = (Q.1.b / 2 : ℚ) ∧
    (((coxIdealBasisOKEqOne hd4 hdneg Q) 1 : 𝓞K) : K).im = (-(1 : ℚ) / 2) := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let x0 : 𝓞K := (coxIdealBasisOKEqOne hd4 hdneg Q) 0
  let x1 : 𝓞K := (coxIdealBasisOKEqOne hd4 hdneg Q) 1
  have hx0 := coxIdealBasisOKEqOne_val_0 hd4 hdneg Q
  have hx1 := coxIdealBasisOKEqOne_val_1 hd4 hdneg Q
  have hex0 : e x0 = (Q.1.a : ZOnePlusSqrtdOverTwo (d / 4)) := by
    dsimp [x0] at hx0 ⊢
    rw [hx0, RingEquiv.apply_symm_apply]
  have hex1 : e x1 = CoxIdealRelation.coxBeta (d / 4) 1 ((-1 + -Q.1.b) / 2) := by
    dsimp [x1] at hx1 ⊢
    rw [hx1, RingEquiv.apply_symm_apply]
  have h0_re_eq :=
    RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_re
      d hd4 x0
  have h0_im_eq :=
    RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_im
      d hd4 x0
  have h1_re_eq :=
    RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_re
      d hd4 x1
  have h1_im_eq :=
    RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_im
      d hd4 x1
  dsimp at h0_re_eq h0_im_eq h1_re_eq h1_im_eq
  rw [hex0] at h0_re_eq h0_im_eq
  rw [hex1] at h1_re_eq h1_im_eq
  have h0_re : (x0 : K).re = (Q.1.a : ℚ) := by
    simpa [x0] using h0_re_eq.symm
  have h0_im : (x0 : K).im = 0 := by
    simpa [x0] using h0_im_eq.symm
  have h1_im : (x1 : K).im = (-(1 : ℚ) / 2) := by
    simpa [x1, CoxIdealRelation.coxBeta] using h1_im_eq.symm
  have hodd : Odd Q.1.b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
  obtain ⟨k, hk⟩ := hodd
  have hdiv : ((-1 + -Q.1.b) / 2 : ℤ) = -1 - k := by
    rw [hk]
    omega
  have h1_re : (x1 : K).re = (Q.1.b / 2 : ℚ) := by
    rw [← h1_re_eq]
    simp only [CoxIdealRelation.coxBeta_re, CoxIdealRelation.coxBeta_im,
      Int.cast_neg, Int.cast_one]
    rw [hdiv, hk]
    norm_num
    ring
  exact ⟨by simpa [x0] using h0_re, by simpa [x0] using h0_im,
    by simpa [x1] using h1_re, by simpa [x1] using h1_im⟩

/-- Left-inverse law for the `d % 4 = 1` branch. -/
theorem classGroupToFormClass_idealClassOfForm_leftInverse_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    classGroupToFormClass hdneg
      (idealClassOfForm_of_mod_four_eq_one d hd4 Q) =
      Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q := by
  let I : (Ideal 𝓞K)⁰ := ⟨idealOfForm_of_mod_four_eq_one d hd4 Q,
    mem_nonZeroDivisors_iff_ne_zero.mpr (idealOfForm_of_mod_four_eq_one_ne_zero d hd4 Q)⟩
  have hI_ne_zero : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have h_idealClass : idealClassOfForm_of_mod_four_eq_one d hd4 Q = ClassGroup.mk0 I := rfl
  rw [h_idealClass]
  have h_class_eq : classGroupToFormClass hdneg (ClassGroup.mk0 I) =
      formClassOfNonzeroIdeal hdneg I := by
    dsimp [classGroupToFormClass]
    let J := Classical.choose (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
    have hJ_mk0 : ClassGroup.mk0 J = ClassGroup.mk0 I :=
      Classical.choose_spec (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
    exact formClassOfNonzeroIdeal_eq_of_mk0_eq hdneg J I hJ_mk0
  rw [h_class_eq]
  rw [formClassOfNonzeroIdeal_eq_mk hdneg I
    (b := orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)]
  rcases coxIdealBasisOKEqOne_K_re_im hd4 hdneg Q with ⟨h0_re, h0_im, h1_re, h1_im⟩
  let b_cox := coxIdealBasisOKEqOne hd4 hdneg Q
  set α := ((b_cox 0 : 𝓞K) : K) with hα
  set β := ((b_cox 1 : 𝓞K) : K) with hβ
  have h_wedge_im : (α * star β - β * star α).im = (Q.1.a : ℚ) := by
    simp [α, β, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul,
      h0_re, h0_im, h1_re, h1_im, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring
  have ha_pos : 0 < (Q.1.a : ℚ) := by exact_mod_cast Q.2.2.2.1
  have hpos : imPartRatio (d := d) (α * star β - β * star α) > 0 := by
    rw [imPartRatio_eq_im, h_wedge_im]
    exact ha_pos
  let b_oriented : OrientedBasis (I : Ideal 𝓞K) :=
    { basis := b_cox, oriented := hpos }
  have h_normform_eq : normFormOfBasis hI_ne_zero b_oriented = Q.1 := by
    have hb0 : ((b_oriented.basis 0 : 𝓞K) : K) = α := hα.symm
    have hb1 : ((b_oriented.basis 1 : 𝓞K) : K) = β := hβ.symm
    have ha_pos_int : 0 < Q.1.a := Q.2.2.2.1
    have hane : Q.1.a ≠ 0 := ne_of_gt ha_pos_int
    have hdetCoord : b_oriented.detCoord = -(Q.1.a : ℚ) / 2 := by
      unfold OrientedBasis.detCoord
      rw [hb0, hb1, h0_re, h0_im, h1_re, h1_im]
      ring
    have hz_eq : ((RingOfIntegers.ringOfIntegersBasisOfModFourEqOne hd4).det
        ((↑) ∘ b_oriented.basis) : ℤ) = -Q.1.a := by
      have hz_cast : (((RingOfIntegers.ringOfIntegersBasisOfModFourEqOne hd4).det
          ((↑) ∘ b_oriented.basis) : ℤ) : ℚ) = -(Q.1.a : ℚ) := by
        rw [b_oriented.det_eq_one_cast_eq_two_detCoord hd4, hdetCoord]
        ring
      exact_mod_cast hz_cast
    have hN_eq : (Ideal.absNorm (I : Ideal 𝓞K) : ℤ) = Q.1.a := by
      have hz_abs := b_oriented.det_eq_one_natAbs_eq_absNorm hd4
      rw [hz_eq] at hz_abs
      simp only [Int.natAbs_neg] at hz_abs
      omega
    have hdiscQ : (Q.1.b : ℚ) ^ 2 - 4 * (Q.1.a : ℚ) * (Q.1.c : ℚ) = (d : ℚ) := by
      have hz : Q.1.disc = d :=
        calc Q.1.disc = fieldDiscriminant d := Q.2.1
          _ = d := fieldDiscriminant_of_mod_four_eq_one hd4
      unfold BinaryQuadraticForm.disc at hz
      exact_mod_cast hz
    have hnorm0 : Algebra.norm ℤ (b_oriented.basis 0 : 𝓞K) = Q.1.a ^ 2 := by
      have h : (Algebra.norm ℤ (b_oriented.basis 0 : 𝓞K) : ℚ) = (Q.1.a : ℚ) ^ 2 := by
        rw [fieldNorm_int_eq, hb0, h0_re, h0_im]
        ring
      exact_mod_cast h
    have hnorm1 : Algebra.norm ℤ (b_oriented.basis 1 : 𝓞K) = Q.1.a * Q.1.c := by
      have h : (Algebra.norm ℤ (b_oriented.basis 1 : 𝓞K) : ℚ) =
          (Q.1.a : ℚ) * (Q.1.c : ℚ) := by
        rw [fieldNorm_int_eq, hb1, h1_re, h1_im]
        linear_combination (1 / 4 : ℚ) * hdiscQ
      exact_mod_cast h
    have hnormsum :
        Algebra.norm ℤ ((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K)) =
          Q.1.a ^ 2 + Q.1.a * Q.1.b + Q.1.a * Q.1.c := by
      have hsum_coe :
          (((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K) : 𝓞K) : K) =
            α + β := by
        have hpc :
            (((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K) : 𝓞K) : K) =
              ((b_oriented.basis 0 : 𝓞K) : K) + ((b_oriented.basis 1 : 𝓞K) : K) := by
          push_cast
          ring
        rw [hpc, hb0, hb1]
      have h :
          (Algebra.norm ℤ
            ((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K)) : ℚ) =
            (Q.1.a : ℚ) ^ 2 +
              (Q.1.a : ℚ) * (Q.1.b : ℚ) + (Q.1.a : ℚ) * (Q.1.c : ℚ) := by
        rw [fieldNorm_int_eq, hsum_coe]
        simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
          h0_re, h0_im, h1_re, h1_im]
        linear_combination (1 / 4 : ℚ) * hdiscQ
      exact_mod_cast h
    exact normFormOfBasis_eq_of_norms hI_ne_zero b_oriented hane hN_eq hnorm0 hnorm1 hnormsum
  have h_equiv : (normFormOfBasis hI_ne_zero
      (orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)).ProperEquivalent
      (normFormOfBasis hI_ne_zero b_oriented) :=
    (normFormOfBasis_properEquivalent hI_ne_zero _ _).symm
  have h_target : (normFormOfBasis hI_ne_zero
      (orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)).ProperEquivalent Q.1 :=
    h_equiv.trans (by rw [h_normform_eq]; exact BinaryQuadraticForm.ProperEquivalent.refl Q.1)
  dsimp [primitivePositiveDefiniteNormFormOfBasis]
  apply Quotient.sound
  simpa using h_target

end CoxLeftInverseEqOne

section CoxAssembly

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- A principal-ideal relation proves the right-inverse law for the `d % 4 ≠ 1`
branch for any chosen oriented basis.  This isolates the remaining Cox
arithmetic to constructing the two nonzero principal generators and the displayed
ideal equality. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  dsimp [idealClassOfForm_of_mod_four_ne_one]
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨x, y, hx, hy, by
    simpa [nonzeroIdealOfForm_of_mod_four_ne_one] using hrel⟩

/-- A principal-ideal relation proves the right-inverse law for the `d % 4 = 1`
branch for any chosen oriented basis.  This is the half-integral analogue of
`idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation`. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  dsimp [idealClassOfForm_of_mod_four_eq_one]
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨x, y, hx, hy, by
    simpa [nonzeroIdealOfForm_of_mod_four_eq_one] using hrel⟩

/-- In the `d % 4 ≠ 1` branch, it is enough to prove the right-inverse law after
replacing the norm form attached to an oriented ideal basis by a properly
equivalent representative. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_properEquivalent
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR :
      PrimitivePositiveDefiniteForm.ProperEquivalent
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) R)
    (hR : idealClassOfForm_of_mod_four_ne_one d hd4 R = ClassGroup.mk0 I) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  calc
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        idealClassOfForm_of_mod_four_ne_one d hd4 R :=
      idealClassOfForm_of_mod_four_ne_one_eq_of_properEquivalent d hd4 _ _ hQR
    _ = ClassGroup.mk0 I := hR

/-- In the `d % 4 = 1` branch, it is enough to prove the right-inverse law after
replacing the norm form attached to an oriented ideal basis by a properly
equivalent representative. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_properEquivalent
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR :
      PrimitivePositiveDefiniteForm.ProperEquivalent
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) R)
    (hR : idealClassOfForm_of_mod_four_eq_one d hd4 R = ClassGroup.mk0 I) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  calc
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        idealClassOfForm_of_mod_four_eq_one d hd4 R :=
      idealClassOfForm_of_mod_four_eq_one_eq_of_properEquivalent d hd4 _ _ hQR
    _ = ClassGroup.mk0 I := hR

/-- In the `d % 4 ≠ 1` branch, the scalar generator of the Cox ideal of the norm
form gives one generator of the principal-relation inclusion
`(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_scalar_mem_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm (((Q.1.a : ℤ) : Zsqrtd d)) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  have hα : (b.basis 0 : 𝓞K) ∈ (I : Ideal 𝓞K) := (b.basis 0).2
  have ha : e.symm (((Q.1.a : ℤ) : Zsqrtd d)) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) := by
    rw [Ideal.mem_span_singleton]
    exact ⟨1, by simp⟩
  simpa [mul_comm] using Ideal.mul_mem_mul ha hα

/-- In the `d % 4 = 1` branch, the scalar generator of the Cox ideal of the norm
form gives one generator of the principal-relation inclusion
`(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_scalar_mem_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
    (b.basis 0 : 𝓞K) * e.symm (((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  have hα : (b.basis 0 : 𝓞K) ∈ (I : Ideal 𝓞K) := (b.basis 0).2
  have ha : e.symm (((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) := by
    rw [Ideal.mem_span_singleton]
    exact ⟨1, by simp⟩
  simpa [mul_comm] using Ideal.mul_mem_mul ha hα

/-! ### Coordinate algebra for the Cox ideal-generator relation -/

/-- Rational real-coordinate identity behind the signed Cox relation
`α * ((-B) / 2 + √D) = -A * β` in the non-half-integral branch. -/
theorem cox_ideal_generator_relation_re {αr αi βr βi D N A B : ℚ}
    (hA : A = (αr ^ 2 - D * αi ^ 2) / N)
    (hB : B = 2 * (αr * βr - D * αi * βi) / N)
    (hN : N = αi * βr - αr * βi) (hN0 : N ≠ 0) :
    αr * (-B / 2) + D * αi = -A * βr := by
  apply mul_right_cancel₀ hN0
  rw [add_mul, neg_mul, hA, hB]
  field_simp [hN0]
  rw [hN]
  ring

/-- Rational imaginary-coordinate identity behind the signed Cox relation
`α * ((-B) / 2 + √D) = -A * β` in the non-half-integral branch. -/
theorem cox_ideal_generator_relation_im {αr αi βr βi D N A B : ℚ}
    (hA : A = (αr ^ 2 - D * αi ^ 2) / N)
    (hB : B = 2 * (αr * βr - D * αi * βi) / N)
    (hN : N = αi * βr - αr * βi) (hN0 : N ≠ 0) :
    αr + αi * (-B / 2) = -A * βi := by
  apply mul_right_cancel₀ hN0
  rw [add_mul, neg_mul, hA, hB]
  field_simp [hN0]
  rw [hN]
  ring

/-- In the `d % 4 ≠ 1` branch, the second Cox ideal generator of the norm form
satisfies the signed classical relation
`α · β_Q = -a_Q · β`, where `(α, β)` is the oriented ideal basis.  The sign is
forced by the orientation convention `N(I) = αᵢβᵣ - αᵣβᵢ`. -/
theorem basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg hI b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) =
      -(((Q.1.a : ℤ) : 𝓞K) * (b.basis 1 : 𝓞K)) := by
  intro hI Q e
  have hβQ :
      ((e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) : 𝓞K) : K).re =
        (-(Q.1.b : ℚ)) / 2 ∧
      ((e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) : 𝓞K) : K).im = 1 := by
    have hb_even : Even Q.1.b :=
      even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
    obtain ⟨k, hk⟩ := hb_even
    have hdiv : (-Q.1.b) / 2 = -k := by
      rw [hk]
      omega
    have hk_rat : (Q.1.b : ℚ) / 2 = k := by
      rw [hk]
      norm_num
    have h_embed (x : 𝓞K) : ((x : 𝓞K) : K) = Zsqrtd.toQsqrtdHom d (e x) := by
      simpa [e] using
        (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply d hd4 x).symm
    rw [h_embed]
    constructor
    · simp [e, Zsqrtd.toQsqrtdHom, RingEquiv.apply_symm_apply, hdiv]
      linarith
    · simp [e, Zsqrtd.toQsqrtdHom, RingEquiv.apply_symm_apply, hdiv]
  have ha : ((Q.1.a : ℤ) : ℚ) =
      (((b.basis 0 : 𝓞K) : K).re ^ 2 -
        (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im ^ 2) /
        (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (normFormOfBasis_a_mul_absNorm hI b)
    dsimp [Q, primitivePositiveDefiniteNormFormOfBasis] at h
    rw [fieldNorm_int_eq] at h
    have hN : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
      exact_mod_cast (absNorm_pos hI).ne'
    rw [eq_div_iff hN]
    simpa [Q, primitivePositiveDefiniteNormFormOfBasis] using h
  have hb : ((Q.1.b : ℤ) : ℚ) =
      (2 * (((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).re -
        (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im *
          ((b.basis 1 : 𝓞K) : K).im)) /
        (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (normFormOfBasis_b_mul_absNorm hI b)
    dsimp [Q, primitivePositiveDefiniteNormFormOfBasis] at h
    have hN : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
      exact_mod_cast (absNorm_pos hI).ne'
    rw [eq_div_iff hN]
    simpa [Q, primitivePositiveDefiniteNormFormOfBasis] using
      show ((normFormOfBasis hI b).b : ℚ) * (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
          2 * (((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).re -
            (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im *
              ((b.basis 1 : 𝓞K) : K).im) by
        have h' : ((normFormOfBasis hI b).b : ℚ) *
            (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
            ((Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
              Algebra.norm ℤ (b.basis 0 : 𝓞K) -
              Algebra.norm ℤ (b.basis 1 : 𝓞K) : ℤ) : ℚ) := by
          simpa using h
        rw [h']
        push_cast
        rw [fieldNorm_int_eq, fieldNorm_int_eq, fieldNorm_int_eq]
        push_cast
        simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
        ring
  have hNdet : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
      ((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).re -
        ((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).im := by
    have hdet : b.detCoord = -(Ideal.absNorm (I : Ideal 𝓞K) : ℚ) :=
      OrientedBasis.detCoord_eq_neg_absNorm_of_mod_four_ne_one hI hd4 b
    unfold OrientedBasis.detCoord at hdet
    linarith
  have hN0 : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
    exact_mod_cast (absNorm_pos hI).ne'
  apply IsFractionRing.injective 𝓞K K
  ext <;>
    simp only [map_mul, map_neg, map_intCast, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, zero_mul, add_zero,
      mul_zero, hβQ.1, hβQ.2]
  · simpa [mul_one] using cox_ideal_generator_relation_re ha hb hNdet hN0
  · simpa [one_mul] using cox_ideal_generator_relation_im ha hb hNdet hN0

/-- In the `d % 4 ≠ 1` branch, the second Cox ideal generator also satisfies
the principal-relation inclusion `(b₀) · β_Q ∈ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  rw [basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
    hdneg hd4 I b]
  have hβ : (b.basis 1 : 𝓞K) ∈ (I : Ideal 𝓞K) := (b.basis 1).2
  have ha : ((Q.1.a : ℤ) : 𝓞K) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) :=
    Ideal.subset_span (by simp)
  exact neg_mem (Ideal.mul_mem_mul ha hβ)

/-- In the `d % 4 ≠ 1` branch, the right-inverse law follows from the classical
Cox relation `(α) · J(Q_b) = (a_Q) · I`, where `α` is the first vector of the
oriented ideal basis and `Q_b` is its norm form. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_first_vector_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (hrel :
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span
            ({(((primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).1.a : ℤ) : 𝓞K)} :
              Set 𝓞K) *
          (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  have hb0_ne : (b.basis 0 : 𝓞K) ≠ 0 := fun h => b.basis.ne_zero 0 (Subtype.ext h)
  refine idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
    hdneg hd4 I b hb0_ne ?_ hrel
  exact_mod_cast
    (primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).2.2.2.1.ne'

/-- In the `d % 4 = 1` branch, the right-inverse law follows from the same
principal relation between the basis first vector, the Cox ideal of the norm
form, and the original ideal. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_first_vector_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (hrel :
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span
            ({(((primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).1.a : ℤ) : 𝓞K)} :
              Set 𝓞K) *
          (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  have hb0_ne : (b.basis 0 : 𝓞K) ≠ 0 := fun h => b.basis.ne_zero 0 (Subtype.ext h)
  refine idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
    hdneg hd4 I b hb0_ne ?_ hrel
  exact_mod_cast
    (primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).2.2.2.1.ne'

/-- A principal-ideal relation proves the right-inverse law for the canonical
oriented basis in the `d % 4 ≠ 1` branch. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_ne_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
    hdneg hd4 I (orientedBasisOfNeZero (I : Ideal 𝓞K)
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)) hx hy hrel

/-- A principal-ideal relation proves the right-inverse law for the canonical
oriented basis in the `d % 4 = 1` branch. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_eq_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
    hdneg hd4 I (orientedBasisOfNeZero (I : Ideal 𝓞K)
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)) hx hy hrel

/-- The Cox map followed by the inverse ideal-to-form map is the identity on
form classes. -/
theorem formClassToClassGroup_leftInverse (hdneg : d < 0) :
    ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C :=
  formClassToClassGroup_leftInverse_of_branch_representatives hdneg
    (classGroupToFormClass_idealClassOfForm_leftInverse_of_mod_four_ne_one hdneg)
    (classGroupToFormClass_idealClassOfForm_leftInverse_of_mod_four_eq_one hdneg)

/-- Assemble the Cox 7.7 equivalence from the two remaining right-inverse
branch laws.  The left inverse branch laws are already proved in this file. -/
noncomputable def formClassEquivClassGroupOfRightBranchLaws (hdneg : d < 0)
    (hne : ∀ (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰),
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       idealClassOfForm_of_mod_four_ne_one d hd4
         (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I)
    (heq : ∀ (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰),
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       idealClassOfForm_of_mod_four_eq_one d hd4
         (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup 𝓞K :=
  formClassEquivClassGroupOfInverseLaws hdneg
    (formClassToClassGroup_leftInverse hdneg)
    (formClassToClassGroup_rightInverse_of_branch_ideal_representatives hdneg hne heq)

end CoxAssembly
end BinaryQuadraticForm
end QuadraticNumberFields
