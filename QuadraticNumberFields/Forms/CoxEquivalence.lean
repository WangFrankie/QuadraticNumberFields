/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.InverseCox
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Zsqrtd.Basic

/-!
# Cox 7.7 Equivalence Assembly

This file is the assembly layer for the imaginary Cox 7.7 correspondence.  The
forward map from form classes to ideal classes lives in `Forms.Bridge`; the
inverse-direction map from ideal classes to form classes lives in
`Forms.InverseCox`, which imports `Forms.Bridge`.  Therefore the final
equivalence belongs here rather than in `Forms.Bridge`.

## Status

The scaffold lemmas in the `CoxEquivalence` section reduce the equivalence to
four branch hypotheses (two for `d % 4 ≠ 1`, two for `d % 4 = 1`).

The `CoxLeftInverse` section contains the core algebraic work for the
`d % 4 ≠ 1` branch: the spanning lemma `mem_span_coxBetaZ_of_mem_ideal` proves
that the Cox ideal `(a, ⟨-b/2, 1⟩)` in `Zsqrtd d` is spanned as a ℤ-module by
`{a, (b/2) - √d}`.  The left round-trip theorem is blocked on two issues:
1. `Basis` type not accessible from this file's import chain
2. The `b/2 = -((-b)/2)` identity for general integers (resolved for even `b`)
-/

open scoped NumberField nonZeroDivisors

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

/-! ## Left Inverse Round-Trip: `d % 4 ≠ 1` Branch (WIP)

Goal: `classGroupToFormClass hdneg (idealClassOfForm_of_mod_four_ne_one d hd4 Q) = ⟦Q⟧`.

✅ Core spanning lemma: `mem_span_coxBetaZ_of_mem_ideal` — the Cox ideal
   `(a, ⟨-b/2, 1⟩)` in `Zsqrtd d` is spanned as a ℤ-module by `{a, (b/2)-√d}`.

🚧 Remaining: construct the `Basis` from the spanning lemma (blocked: `Basis`
   not accessible from this file's import chain despite being used in
   `InverseCox.lean`), add orientation, compute norm form equality.

The key proof chain once the basis exists:
  classGroupToFormClass hdneg (idealClassOfForm Q)
    = formClassOfNonzeroIdeal hdneg (nonzeroIdealOfForm Q)  [L3: eq_of_mk0_eq]
    = ⟦normFormOfBasis hI b⟧  [formClassOfNonzeroIdeal_eq_mk]
    = ⟦Q.1⟧  [norm form = Q.1, via coxBasis computation]
    = ⟦Q⟧
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
      simp [m, n, coxBetaZ_re, coxBetaZ_im]
      rw [hk']
      have hneg : (-b : ℤ) / 2 = -k := by
        rw [show (-b : ℤ) / 2 = -(b / 2) by omega, hk']
      rw [hneg]
      calc
        (u₁ + u₂ * k - v₂ * c) * a + (-(u₂ * a) - v₁ + v₂ * k) * k
            = u₁ * a - v₁ * k + v₂ * (k * k - c * a) := by ring
        _ = u₁ * a - v₁ * k + v₂ * (k ^ 2 - a * c) := by
          rw [mul_comm c a]; ring
        _ = u₁ * a - v₁ * k + v₂ * d := by rw [h_ac]; ring
        _ = u₁ * a + (v₁ * (-k) + d * v₂) := by ring
    · -- imaginary part
      simp [m, n, coxBetaZ_re, coxBetaZ_im]
      have hneg' : v₂ * ((-b : ℤ) / 2) = -(v₂ * k) := by
        rw [show (-b : ℤ) / 2 = -(b / 2) by omega, hk']
        ring
      rw [hneg']
      ring
  rw [← hsum]
  refine Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-! ### Left inverse round-trip (blocked)

The remaining steps require `Basis` (not accessible from this import chain)
and the norm form equality (which follows from the spanning lemma once a
basis is constructed). The spanning lemma above is the core algebraic work.
-/

/-- **Left inverse round-trip** for `d % 4 ≠ 1` — `sorry` pending `Basis` resolution.

Once the oriented Cox basis is constructed from the spanning lemma above,
the proof chain is:
  classGroupToFormClass hdneg (idealClassOfForm Q)
    = formClassOfNonzeroIdeal hdneg (nonzeroIdealOfForm Q)  [by formClassOfNonzeroIdeal_eq_of_mk0_eq]
    = ⟦normFormOfBasis hI b⟧  [formClassOfNonzeroIdeal_eq_mk]
    = ⟦Q.1⟧  [norm form equality]
    = ⟦Q⟧

Constraint: `Basis` type not accessible from this file's import context.
Tested: spanning lemma `mem_span_coxBetaZ_of_mem_ideal` compiles clean. -/
theorem classGroupToFormClass_idealClassOfForm_leftInverse_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    classGroupToFormClass hdneg
      (idealClassOfForm_of_mod_four_ne_one d hd4 Q) =
      Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q := by
  sorry

end CoxLeftInverse
end BinaryQuadraticForm
end QuadraticNumberFields
