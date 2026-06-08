/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.CommonInstances
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.Transport
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# Discriminant of Quadratic Number Fields

This file proves the explicit discriminant formula for `Qsqrtd (d : ℚ)`:

* If `d % 4 = 1`, then `NumberField.discr (Qsqrtd (d : ℚ)) = d`.
* If `d % 4 ≠ 1`, then `NumberField.discr (Qsqrtd (d : ℚ)) = 4 * d`.

## Main Theorems

* `discr_of_mod_four_ne_one`: `NumberField.discr (Qsqrtd (d : ℚ)) = 4 * d`
  when `d % 4 ≠ 1`.
* `discr_of_mod_four_eq_one`: `NumberField.discr (Qsqrtd (d : ℚ)) = d`
  when `d % 4 = 1`.
* `discr_formula`: Unified discriminant formula combining both cases.
-/

open scoped NumberField

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd` models.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace RingOfIntegers

/-! ## Explicit Trace and Discriminant Computations -/

/-- The discriminant of the standard basis of `ℤ[√d]` is `4 * d`. -/
theorem discr_zsqrtd_basis (d : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis d 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd d)) = 4 * d := by
  rw [QuadraticAlgebra.discr_basis_int]
  ring

/-- The discriminant of the standard basis of `ℤ[(1+√(1+4k))/2]` is `1 + 4 * k`. -/
theorem discr_zOnePlusSqrtOverTwo_basis (k : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis k 1 :
      Module.Basis (Fin 2) ℤ (ZOnePlusSqrtOverTwo k)) = 1 + 4 * k := by
  rw [QuadraticAlgebra.discr_basis_int]
  ring

/-- Any ring equivalence between `ℤ`-algebras is automatically an `AlgEquiv ℤ`. -/
def ringEquivToIntAlgEquiv
    {R S : Type*} [CommRing R] [Algebra ℤ R] [CommRing S] [Algebra ℤ S]
    (e : R ≃+* S) : R ≃ₐ[ℤ] S :=
  AlgEquiv.ofRingEquiv (f := e) (fun n => by
    simp only [eq_intCast, map_intCast])

/-! ## Transport to NumberField.discr -/

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- **Discriminant of `Q(√d)` when `d % 4 ≠ 1`.**

When `d % 4 ≠ 1`, the ring of integers is `𝓞 ≅ ℤ[√d]` with ℤ-basis `{1, √d}`,
giving discriminant `4d`. -/
theorem discr_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    NumberField.discr (Qsqrtd (d : ℚ)) = 4 * d := by
  let e := ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let f : Zsqrtd d ≃ₐ[ℤ] 𝓞 (Qsqrtd (d : ℚ)) :=
    ringEquivToIntAlgEquiv e.symm
  let b' : Module.Basis (Fin 2) ℤ (𝓞 (Qsqrtd (d : ℚ))) :=
    (QuadraticAlgebra.basis d 0).map f.toLinearEquiv
  rw [← NumberField.discr_eq_discr (Qsqrtd (d : ℚ)) b']
  change Algebra.discr ℤ (⇑f ∘ ⇑(QuadraticAlgebra.basis d 0)) = 4 * d
  rw [← Algebra.discr_eq_discr_of_algEquiv _ f]
  exact discr_zsqrtd_basis d

/-- **Discriminant of `Q(√d)` when `d % 4 = 1`.**

Uses the ℤ-basis `{1, ω}` where `ω = (1 + √d)/2` for `𝓞 = ℤ[(1+√d)/2]`
to compute `disc = d`. -/
theorem discr_of_mod_four_eq_one (hd4 : d % 4 = 1) :
    NumberField.discr (Qsqrtd (d : ℚ)) = d := by
  obtain ⟨k, hk⟩ := exists_k_of_mod_four_eq_one hd4
  subst hk
  let e := ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq (1 + 4 * k) k rfl
  let f : ZOnePlusSqrtOverTwo k ≃ₐ[ℤ] 𝓞 (Qsqrtd (((1 + 4 * k : ℤ) : ℚ))) :=
    ringEquivToIntAlgEquiv e.symm
  let b' : Module.Basis (Fin 2) ℤ (𝓞 (Qsqrtd (((1 + 4 * k : ℤ) : ℚ)))) :=
    (QuadraticAlgebra.basis k 1).map f.toLinearEquiv
  rw [← NumberField.discr_eq_discr (Qsqrtd (((1 + 4 * k : ℤ) : ℚ))) b']
  change Algebra.discr ℤ (⇑f ∘ ⇑(QuadraticAlgebra.basis k 1)) = 1 + 4 * k
  rw [← Algebra.discr_eq_discr_of_algEquiv _ f]
  exact discr_zOnePlusSqrtOverTwo_basis k

/-- **Unified discriminant formula for `Q(√d)`.**

For squarefree `d ≠ 1`:
* `disc(Q(√d)) = d`   if `d ≡ 1 (mod 4)`
* `disc(Q(√d)) = 4d`  if `d ≢ 1 (mod 4)` -/
theorem discr_formula :
    NumberField.discr (Qsqrtd (d : ℚ)) = if d % 4 = 1 then d else 4 * d := by
  split
  · exact discr_of_mod_four_eq_one d ‹_›
  · exact discr_of_mod_four_ne_one d ‹_›

/-- Transport the standard-model discriminant formula back to an abstract field
identified with `Qsqrtd d`. -/
theorem discr_formula_of_algEquiv_qsqrtd
    {K : Type*} [Field K] [Algebra ℚ K] [NumberField K]
    (e : K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) :
    NumberField.discr K = if d % 4 = 1 then d else 4 * d := by
  calc
    NumberField.discr K = NumberField.discr (Qsqrtd (d : ℚ)) :=
      NumberField.discr_eq_of_algEquiv e
    _ = if d % 4 = 1 then d else 4 * d := discr_formula d

/-- Every abstract quadratic field admits a standard squarefree parameter whose
standard discriminant formula computes the field discriminant.

This is the abstract-field version of `discr_formula`: classification produces
`K ≃ₐ[ℚ] Qsqrtd d`, the standard-model formula computes there, and
`NumberField.discr_eq_of_algEquiv` transports the result back to `K`. -/
theorem exists_discr_formula_of_quadraticField
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧
      NumberField.discr K = if d % 4 = 1 then d else 4 * d := by
  obtain ⟨d, hd_sf, hd_ne, ⟨e⟩⟩ := exists_ringEquiv_qsqrtd K
  letI : Fact (Squarefree d) := ⟨hd_sf⟩
  letI : Fact (d ≠ 1) := ⟨hd_ne⟩
  refine ⟨d, hd_sf, hd_ne, ?_⟩
  calc
    NumberField.discr K = NumberField.discr (Qsqrtd (d : ℚ)) :=
      NumberField.discr_eq_discr_of_ringEquiv K e
    _ = if d % 4 = 1 then d else 4 * d := discr_formula d

/-! ## Named Examples

Common discriminants for frequently-used quadratic fields. -/

/-- **Gaussian integers**: `disc(Q(√(-1))) = -4`. -/
theorem discr_gaussian :
    NumberField.discr (Qsqrtd ((-1 : ℤ) : ℚ)) = -4 :=
  discr_of_mod_four_ne_one (-1) (by decide)


/-- **Eisenstein integers**: `disc(Q(√(-3))) = -3`. -/
theorem discr_eisenstein :
    NumberField.discr (Qsqrtd ((-3 : ℤ) : ℚ)) = -3 :=
  discr_of_mod_four_eq_one (-3) (by decide)


/-- **Q(√(-5))**: `disc(Q(√(-5))) = -20`. -/
theorem discr_Qsqrtd_neg_five :
    NumberField.discr (Qsqrtd ((-5 : ℤ) : ℚ)) = -20 :=
  discr_of_mod_four_ne_one (-5) (by decide)


end SquarefreeIntegerParameter

end RingOfIntegers
end QuadraticNumberFields
