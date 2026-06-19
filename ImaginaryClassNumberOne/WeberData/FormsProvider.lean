/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import BinaryQuadraticForms.Cox.IdealRelation
import FormClassGroup.ClassGroup.ClassNumber
import FormClassGroup.ClassGroup.Law
import ImaginaryClassNumberOne.WeberData.Core
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import QNFMathlib.Data.Int.Squarefree
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbol

/-!
# Forms Provider for the Weber Data Interface

This file contains the reduced-forms route for supplying the conductor-`2`
ring-class-number input used by the Baker-Heegner-Stark Weber/CM interface.

The core Weber data interface remains independent of this file.  Import this
module only when the proof route explicitly goes through primitive reduced
binary quadratic forms.

## Main definitions

* `ConductorTwoFormClassNumberThree`: Forms-side class-number-three statement for
  primitive reduced forms of discriminant `-4p` in the `p ≠ 3` inert branch.
* `conductor_two_zsqrtd_basis_discriminant_eq_neg_four_mul`: the concrete
  `Zsqrtd (-p)` conductor-`2` order has basis discriminant `-4p`.
* `conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_fieldDiscriminant`:
  the same discriminant equals `2 ^ 2` times the field discriminant.
* `fieldDiscriminant_eq_numberField_discr_neg_natCast_of_nat_mod_eight_eq_three`:
  the forms-side and number-field discriminants agree for `d = -p`.
* `conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_numberField_discr`:
  the same bridge stated using `NumberField.discr`.
* `conductorTwoSuborderHom`: the concrete conductor-`2` suborder inclusion
  `Zsqrtd (-p) ↪ ZOnePlusSqrtdOverTwo (-p / 4)` in the inert branch.
* `conductorTwoOrderIdealOfForm`: the Cox/order ideal in `Zsqrtd (-p)`
  attached to a primitive positive definite form of discriminant `-4p`.
* `conductorTwoMaximalOrderIdealOfForm`: its extension to the half-integral
  maximal-order model in the inert branch.
* `conductorTwoRingOfIntegersIdealOfForm`: the same extended ideal transported
  to `𝓞 (Qsqrtd (-p))`, ready to define a maximal-order ideal class.
* `conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet`: the
  finite-table reduced-form computation for the non-exceptional inert Heegner
  primes.
* `three_le_conductor_two_reduced_forms_card`: the explicit lower bound coming
  from three conductor-`2` reduced forms.
* `ConductorTwoReducedFormCoverData`: the remaining forms-side upper-bound
  interface, expressed as a finite-fiber cover of conductor-`2` reduced forms by
  field-discriminant reduced forms.
* `ConductorTwoReducedFormRepCoverData`: the same upper-bound interface stated
  on finite reduced-form representative types.
* `ConductorTwoFormClassCoverData`: the upper-bound interface stated on
  primitive positive definite form classes, closer to the Cox/order map.
* `inertFieldFormClassEquivClassGroup`: Cox's field-discriminant equivalence
  specialized to the inert branch, where the field discriminant is `-p`.
* `ConductorTwoOrderClassNumberFormula`: the non-exceptional Cox order
  class-number formula statement for the conductor-`2` order.
* `conductor_two_order_class_number_formula`: the remaining Cox/Picard order
  class-number formula input for the conductor-`2` route.
* `ConductorTwoIdealClassCoverData`: the order/Picard-shaped upper-bound
  interface, stated after extending conductor-`2` classes to maximal-order
  ideal classes.
* `ConductorTwoIdealClassKernelData`: the Picard-exact-sequence-shaped kernel
  interface behind the alternate conductor-`2` finite-cover route.
* `conductor_two_ideal_class_fiber_card_le_three_of_kernel_data`: the bridge
  from explicit kernel data to the ideal-class fiber bound.
* `conductor_two_ideal_class_cover_data_of_kernel_data`: the bridge from explicit
  kernel data to ideal-class cover data.
* `conductor_two_reduced_forms_card_le_three_mul_classNumber_of_cover`: the
  finite-fiber cover bridge from conductor-`2` reduced forms to the maximal-order
  class number.
* `conductor_two_form_class_cover_data_of_kernel_data`: the bridge from
  explicit kernel data to the quotient-level conductor-lowering cover map.
* `conductorTwoFormClassNumberThree_of_order_class_number_formula`: the
  bridge from the Cox/order formula equality to Forms-side class-number data.
* `ringClassNumberConductorTwoEqualsThree_of_forms`: the bridge from the Forms
  provider to the core ring-class-number Prop.
* `formsInertPrimeWeberDataProvider`: the reduced-forms route packaged as the
  core inert-prime provider interface.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- Forms-side class-number-three statement for the conductor-`2` discriminant `-4p`.

This is the Cox/reduced-forms route into the conductor-`2` ring-class-number
input. It records only the computable primitive reduced form count, leaving the
still-missing Cox order class-number formula as the named bridge. -/
def ConductorTwoFormClassNumberThree (p : ℕ) : Prop :=
  (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3

/-- In the inert-prime branch `p ≡ 3 (mod 8)`, the conductor-`2` order
discriminant is `2 ^ 2` times the field discriminant, namely `-4p`. -/
theorem conductor_two_order_discriminant_eq_neg_four_mul
    (p : ℕ) (hp8 : p % 8 = 3) :
    (2 : ℤ) ^ 2 * BinaryQuadraticForm.fieldDiscriminant (-(p : ℤ)) =
      -(4 * (p : ℤ)) := by
  rw [BinaryQuadraticForm.fieldDiscriminant_neg_natCast_of_nat_mod_eight_eq_three hp8]
  ring

/-- In the inert branch `p % 8 = 3`, the forms-side field discriminant at `-p`
agrees with the number-field discriminant of `ℚ(√-p)`. -/
theorem fieldDiscriminant_eq_numberField_discr_neg_natCast_of_nat_mod_eight_eq_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) :
    BinaryQuadraticForm.fieldDiscriminant (-(p : ℤ)) =
      NumberField.discr (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) := by
  rw [BinaryQuadraticForm.fieldDiscriminant_neg_natCast_of_nat_mod_eight_eq_three hp8,
    RingOfIntegers.discr_of_mod_four_eq_one (-(p : ℤ))
      (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)]

/-- The concrete order `Zsqrtd (-p)` has standard-basis discriminant `-4p`.

For `p ≡ 3 (mod 8)`, the maximal order in `ℚ(√-p)` is half-integral, so this
is the expected conductor-`2` quadratic order.  The statement deliberately
records only the basis discriminant; the Picard/order class-number formula is
kept as the separate Cox boundary below. -/
theorem conductor_two_zsqrtd_basis_discriminant_eq_neg_four_mul (p : ℕ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis (-(p : ℤ)) 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd (-(p : ℤ)))) =
      -(4 * (p : ℤ)) := by
  rw [RingOfIntegers.discr_zsqrtd_basis]
  ring

/-- The concrete conductor-`2` order model `Zsqrtd (-p)` has discriminant
`2 ^ 2` times the field discriminant in the inert branch. -/
theorem conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_fieldDiscriminant
    (p : ℕ) (hp8 : p % 8 = 3) :
    Algebra.discr ℤ (QuadraticAlgebra.basis (-(p : ℤ)) 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd (-(p : ℤ)))) =
      (2 : ℤ) ^ 2 * BinaryQuadraticForm.fieldDiscriminant (-(p : ℤ)) := by
  rw [conductor_two_zsqrtd_basis_discriminant_eq_neg_four_mul,
    conductor_two_order_discriminant_eq_neg_four_mul p hp8]

/-- The concrete conductor-`2` order model `Zsqrtd (-p)` has discriminant
`2 ^ 2` times the number-field discriminant in the inert branch. -/
theorem conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_numberField_discr
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) :
    Algebra.discr ℤ (QuadraticAlgebra.basis (-(p : ℤ)) 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd (-(p : ℤ)))) =
      (2 : ℤ) ^ 2 * NumberField.discr (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) := by
  rw [conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_fieldDiscriminant p hp8,
    fieldDiscriminant_eq_numberField_discr_neg_natCast_of_nat_mod_eight_eq_three p hp8]

/-- In the inert branch `p % 8 = 3`, the half-integral maximal-order parameter
`-p / 4` satisfies `1 + 4 * (-p / 4) = -p`. -/
theorem conductor_two_half_integral_parameter_eq_neg_natCast
    (p : ℕ) (hp8 : p % 8 = 3) :
    1 + 4 * (-(p : ℤ) / 4) = -(p : ℤ) :=
  (Int.neg_natCast_eq_one_add_four_mul_div_four_of_nat_mod_eight_eq_three hp8).symm

/-- The concrete conductor-`2` suborder inclusion in the inert branch.

For `p % 8 = 3`, the maximal order of `ℚ(√-p)` is modeled by
`ZOnePlusSqrtdOverTwo (-p / 4)`.  This homomorphism realizes
`Zsqrtd (-p)` as the conductor-`2` suborder whose `ω`-coefficient is even. -/
def conductorTwoSuborderHom (p : ℕ) (hp8 : p % 8 = 3) :
    Zsqrtd (-(p : ℤ)) →+* ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4) where
  toFun := fun z => ⟨z.re - z.im, 2 * z.im⟩
  map_one' := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' := by
    intro x y
    have hparam : -(p : ℤ) = 1 + 4 * (-(p : ℤ) / 4) :=
      Int.neg_natCast_eq_one_add_four_mul_div_four_of_nat_mod_eight_eq_three hp8
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
      linear_combination hparam * x.im * y.im
    · simp only [QuadraticAlgebra.im_mul]
      ring
  map_zero' := by
    ext <;> simp [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
  map_add' := by
    intro x y
    ext <;> simp [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;> ring

/-- The concrete conductor-`2` suborder inclusion is injective. -/
theorem conductorTwoSuborderHom_injective (p : ℕ) (hp8 : p % 8 = 3) :
    Function.Injective (conductorTwoSuborderHom p hp8) := by
  intro x y hxy
  ext
  · have hre : x.re - x.im = y.re - y.im := by
      simpa [conductorTwoSuborderHom] using congrArg QuadraticAlgebra.re hxy
    have him : 2 * x.im = 2 * y.im := by
      simpa [conductorTwoSuborderHom] using congrArg QuadraticAlgebra.im hxy
    omega
  · have him : 2 * x.im = 2 * y.im := by
      simpa [conductorTwoSuborderHom] using congrArg QuadraticAlgebra.im hxy
    omega

/-- The image of the concrete conductor-`2` suborder inside the half-integral
maximal-order model is exactly the even-`ω`-coefficient part. -/
theorem mem_range_conductorTwoSuborderHom_iff_even_im
    (p : ℕ) (hp8 : p % 8 = 3) (w : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) :
    (∃ z : Zsqrtd (-(p : ℤ)), conductorTwoSuborderHom p hp8 z = w) ↔
      2 ∣ w.im := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.im, rfl⟩
  · rintro ⟨b, hb⟩
    refine ⟨⟨w.re + b, b⟩, ?_⟩
    ext <;> simp [conductorTwoSuborderHom, hb]

/-- The Cox/order ideal in the concrete conductor-`2` order `Zsqrtd (-p)`
attached to a primitive positive definite form of discriminant `-4p`.

This is the order-level object whose extension to the maximal order should
underlie the quotient-level cover map `ConductorTwoFormClassCoverData`. -/
noncomputable def conductorTwoOrderIdealOfForm
    (p : ℕ) (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    Ideal (Zsqrtd (-(p : ℤ))) :=
  CoxIdealRelation.coxIdeal (-(p : ℤ)) 0 Q.1.a ((-Q.1.b) / 2)

/-- The leading coefficient belongs to the conductor-`2` Cox/order ideal. -/
theorem self_mem_conductorTwoOrderIdealOfForm
    (p : ℕ) (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    (Q.1.a : Zsqrtd (-(p : ℤ))) ∈ conductorTwoOrderIdealOfForm p Q := by
  exact CoxIdealRelation.self_mem_coxIdeal (-(p : ℤ)) 0 Q.1.a ((-Q.1.b) / 2)

/-- The second Cox generator belongs to the conductor-`2` Cox/order ideal. -/
theorem generator_mem_conductorTwoOrderIdealOfForm
    (p : ℕ) (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd (-(p : ℤ))) ∈ conductorTwoOrderIdealOfForm p Q := by
  exact Ideal.subset_span (by simp)

/-- The conductor-`2` Cox/order ideal attached to a positive definite form is
nonzero. -/
theorem conductorTwoOrderIdealOfForm_ne_bot
    (p : ℕ) (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    conductorTwoOrderIdealOfForm p Q ≠ ⊥ := by
  intro hbot
  have hmem := self_mem_conductorTwoOrderIdealOfForm p Q
  rw [hbot] at hmem
  have ha_zero : Q.1.a = 0 := by
    have hzero : (Q.1.a : Zsqrtd (-(p : ℤ))) = 0 := by
      simpa [Ideal.mem_bot] using hmem
    have hre := congrArg QuadraticAlgebra.re hzero
    simpa using hre
  have hpos : 0 < Q.1.a := Q.2.2.2.1
  omega

/-- The determinant identity for an element of `SL₂(ℤ)`, in the matrix
coordinate form used by the Cox ideal-relation API. -/
theorem sl2z_det_fin_two (g : BinaryQuadraticForm.SL2Z) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  simpa using h

/-- The conductor-`2` Cox/order ideal relation in `Zsqrtd (-p)` for a proper
transform of a primitive positive definite form. -/
theorem conductorTwoOrderIdeal_relation_transform
    (p : ℕ)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (g : BinaryQuadraticForm.SL2Z) :
    Ideal.span
        ({(((BinaryQuadraticForm.transform Q.1 g).a : ℤ) : Zsqrtd (-(p : ℤ)))} :
          Set (Zsqrtd (-(p : ℤ)))) *
      conductorTwoOrderIdealOfForm p Q =
    Ideal.span
        ({(((g 0 0 * Q.1.a : ℤ) : Zsqrtd (-(p : ℤ))) -
          (g 1 0 : Zsqrtd (-(p : ℤ))) * (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd (-(p : ℤ))))} :
          Set (Zsqrtd (-(p : ℤ)))) *
      Ideal.span
        ({(((BinaryQuadraticForm.transform Q.1 g).a : ℤ) : Zsqrtd (-(p : ℤ))),
          (⟨(-(BinaryQuadraticForm.transform Q.1 g).b) / 2, 1⟩ :
            Zsqrtd (-(p : ℤ)))} : Set (Zsqrtd (-(p : ℤ)))) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := sl2z_det_fin_two g
  have hdisc : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 4 * (-(p : ℤ)) := by
    simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc] using Q.2.1
  have hb_even : Even Q.1.b :=
    BinaryQuadraticForm.even_b_of_hasDiscriminant_neg_four_mul_natCast Q.2.1
  have hdisc_transform :
      (BinaryQuadraticForm.transform Q.1 g).HasDiscriminant (-(4 * (p : ℤ))) := by
    simpa using (Q.transform g).2.1
  have hb_transform_even : Even (BinaryQuadraticForm.transform Q.1 g).b :=
    BinaryQuadraticForm.even_b_of_hasDiscriminant_neg_four_mul_natCast hdisc_transform
  have hu : 2 * ((-Q.1.b) / 2) = -Q.1.b :=
    Int.two_mul_neg_ediv_two_of_even hb_even
  have hv : 2 * ((-(BinaryQuadraticForm.transform Q.1 g).b) / 2) =
      -(2 * Q.1.a * g 0 0 * g 0 1 +
        Q.1.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) +
        2 * Q.1.c * g 1 0 * g 1 1) := by
    simpa [BinaryQuadraticForm.transform_b] using
      Int.two_mul_neg_ediv_two_of_even hb_transform_even
  simpa [conductorTwoOrderIdealOfForm, BinaryQuadraticForm.transform_a] using
    CoxIdealRelation.ideal_relation (DD := -(p : ℤ)) (bb := 0) (A := Q.1.a)
      (B := Q.1.b) (C := Q.1.c) (p := g 0 0) (q := g 0 1)
      (r := g 1 0) (s := g 1 1) (u := (-Q.1.b) / 2)
      (v := (-(BinaryQuadraticForm.transform Q.1 g).b) / 2)
      hdet (by simpa using hdisc) (by simpa using hu) (by simpa using hv)

/-- The conductor-`2` Cox/order ideal relation, stated using
`conductorTwoOrderIdealOfForm` on both sides. -/
theorem conductorTwoOrderIdeal_relation_transform'
    (p : ℕ)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (g : BinaryQuadraticForm.SL2Z) :
    Ideal.span
        ({(((BinaryQuadraticForm.transform Q.1 g).a : ℤ) : Zsqrtd (-(p : ℤ)))} :
          Set (Zsqrtd (-(p : ℤ)))) *
      conductorTwoOrderIdealOfForm p Q =
    Ideal.span
        ({(((g 0 0 * Q.1.a : ℤ) : Zsqrtd (-(p : ℤ))) -
          (g 1 0 : Zsqrtd (-(p : ℤ))) * (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd (-(p : ℤ))))} :
          Set (Zsqrtd (-(p : ℤ)))) *
      conductorTwoOrderIdealOfForm p (Q.transform g) := by
  simpa [conductorTwoOrderIdealOfForm, CoxIdealRelation.coxIdeal] using
    conductorTwoOrderIdeal_relation_transform p Q g

/-- The generic Cox basis specialized to the conductor-`2` order ideal attached
to a form of discriminant `-4p`. -/
noncomputable def conductorTwoOrderIdealBasisOfForm
    (p : ℕ) (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    Module.Basis (Fin 2) ℤ (conductorTwoOrderIdealOfForm p Q) := by
  have hb_even : Even Q.1.b :=
    BinaryQuadraticForm.even_b_of_hasDiscriminant_neg_four_mul_natCast Q.2.1
  change Module.Basis (Fin 2) ℤ
    (CoxIdealRelation.coxIdeal (-(p : ℤ)) 0 Q.1.a ((-Q.1.b) / 2))
  refine CoxIdealRelation.coxIdealBasis (DD := -(p : ℤ)) (bb := 0)
    (A := Q.1.a) (B := Q.1.b) (C := Q.1.c) (u := (-Q.1.b) / 2)
    (ne_of_gt Q.2.2.2.1) ?_ ?_
  · simpa using Int.two_mul_neg_ediv_two_of_even hb_even
  · simpa [BinaryQuadraticForm.HasDiscriminant, BinaryQuadraticForm.disc] using Q.2.1

/-- Extension of the conductor-`2` Cox/order ideal from `Zsqrtd (-p)` to the
half-integral maximal-order model in the inert branch. -/
noncomputable def conductorTwoMaximalOrderIdealOfForm
    (p : ℕ) (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    Ideal (ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) :=
  Ideal.map (conductorTwoSuborderHom p hp8) (conductorTwoOrderIdealOfForm p Q)

/-- The leading coefficient belongs to the maximal-order extension of the
conductor-`2` Cox/order ideal. -/
theorem self_mem_conductorTwoMaximalOrderIdealOfForm
    (p : ℕ) (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    (Q.1.a : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) ∈
      conductorTwoMaximalOrderIdealOfForm p hp8 Q := by
  simpa [conductorTwoMaximalOrderIdealOfForm, conductorTwoSuborderHom] using
    Ideal.mem_map_of_mem (conductorTwoSuborderHom p hp8)
      (self_mem_conductorTwoOrderIdealOfForm p Q)

/-- The image of the second Cox/order generator belongs to the maximal-order
extension ideal. -/
theorem generator_mem_conductorTwoMaximalOrderIdealOfForm
    (p : ℕ) (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    (⟨(-Q.1.b) / 2 - 1, 2⟩ : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) ∈
      conductorTwoMaximalOrderIdealOfForm p hp8 Q := by
  simpa [conductorTwoMaximalOrderIdealOfForm, conductorTwoSuborderHom] using
    Ideal.mem_map_of_mem (conductorTwoSuborderHom p hp8)
      (generator_mem_conductorTwoOrderIdealOfForm p Q)

/-- The maximal-order extension of the conductor-`2` Cox/order ideal is
nonzero. -/
theorem conductorTwoMaximalOrderIdealOfForm_ne_bot
    (p : ℕ) (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    conductorTwoMaximalOrderIdealOfForm p hp8 Q ≠ ⊥ := by
  intro hbot
  have hmem := self_mem_conductorTwoMaximalOrderIdealOfForm p hp8 Q
  rw [hbot] at hmem
  have ha_zero : Q.1.a = 0 := by
    have hzero :
        (Q.1.a : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) = 0 := by
      simpa [Ideal.mem_bot] using hmem
    have hre := congrArg QuadraticAlgebra.re hzero
    simpa using hre
  have hpos : 0 < Q.1.a := Q.2.2.2.1
  omega

/-- The conductor-`2` Cox/order ideal relation after extending ideals to the
half-integral maximal-order model. -/
theorem conductorTwoMaximalOrderIdeal_relation_transform
    (p : ℕ) (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (g : BinaryQuadraticForm.SL2Z) :
    Ideal.span
        ({conductorTwoSuborderHom p hp8
          (((BinaryQuadraticForm.transform Q.1 g).a : ℤ) : Zsqrtd (-(p : ℤ)))} :
          Set (ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4))) *
      conductorTwoMaximalOrderIdealOfForm p hp8 Q =
    Ideal.span
        ({conductorTwoSuborderHom p hp8
          (((g 0 0 * Q.1.a : ℤ) : Zsqrtd (-(p : ℤ))) -
            (g 1 0 : Zsqrtd (-(p : ℤ))) *
              (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd (-(p : ℤ))))} :
          Set (ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4))) *
      conductorTwoMaximalOrderIdealOfForm p hp8 (Q.transform g) := by
  let f := conductorTwoSuborderHom p hp8
  have h := congrArg (Ideal.map f) (conductorTwoOrderIdeal_relation_transform' p Q g)
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span] at h
  simpa [conductorTwoMaximalOrderIdealOfForm, f] using h

/-- The maximal-order extension ideal, transported from the half-integral model
to the actual ring of integers of `ℚ(√-p)`. -/
noncomputable def conductorTwoRingOfIntegersIdealOfForm
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    Ideal (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))) :=
  Ideal.comap
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      (-(p : ℤ)) (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)).toRingHom
    (conductorTwoMaximalOrderIdealOfForm p hp8 Q)

/-- The transported leading coefficient belongs to the ring-of-integers ideal
attached to a conductor-`2` form. -/
theorem self_mem_conductorTwoRingOfIntegersIdealOfForm
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      (-(p : ℤ)) (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)
    e.symm ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) ∈
      conductorTwoRingOfIntegersIdealOfForm p hp8 Q := by
  intro e
  change e (e.symm ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4))) ∈
    conductorTwoMaximalOrderIdealOfForm p hp8 Q
  rw [RingEquiv.apply_symm_apply]
  exact self_mem_conductorTwoMaximalOrderIdealOfForm p hp8 Q

/-- The transported second Cox/order generator belongs to the ring-of-integers
ideal attached to a conductor-`2` form. -/
theorem generator_mem_conductorTwoRingOfIntegersIdealOfForm
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      (-(p : ℤ)) (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)
    e.symm (⟨(-Q.1.b) / 2 - 1, 2⟩ : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) ∈
      conductorTwoRingOfIntegersIdealOfForm p hp8 Q := by
  intro e
  change e (e.symm (⟨(-Q.1.b) / 2 - 1, 2⟩ :
      ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4))) ∈
    conductorTwoMaximalOrderIdealOfForm p hp8 Q
  rw [RingEquiv.apply_symm_apply]
  exact generator_mem_conductorTwoMaximalOrderIdealOfForm p hp8 Q

/-- The conductor-`2` Cox/order ideal relation after transporting the extended
ideals to the ring of integers of `ℚ(√-p)`. -/
theorem conductorTwoRingOfIntegersIdeal_relation_transform
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (g : BinaryQuadraticForm.SL2Z) :
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      (-(p : ℤ)) (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)
    let f := conductorTwoSuborderHom p hp8
    Ideal.span
        ({e.symm (f (((BinaryQuadraticForm.transform Q.1 g).a : ℤ) :
          Zsqrtd (-(p : ℤ))))} :
          Set (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) *
      conductorTwoRingOfIntegersIdealOfForm p hp8 Q =
    Ideal.span
        ({e.symm (f
          (((g 0 0 * Q.1.a : ℤ) : Zsqrtd (-(p : ℤ))) -
            (g 1 0 : Zsqrtd (-(p : ℤ))) *
              (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd (-(p : ℤ)))))} :
          Set (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) *
      conductorTwoRingOfIntegersIdealOfForm p hp8 (Q.transform g) := by
  intro e f
  have hcoord := conductorTwoMaximalOrderIdeal_relation_transform p hp8 Q g
  have hcomap := congrArg (Ideal.comap (e : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) →+*
    ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4))) hcoord
  rw [Ideal.comap_span_singleton_mul_of_ringEquiv e
      (f (((BinaryQuadraticForm.transform Q.1 g).a : ℤ) : Zsqrtd (-(p : ℤ))))
      (conductorTwoMaximalOrderIdealOfForm p hp8 Q)] at hcomap
  rw [Ideal.comap_span_singleton_mul_of_ringEquiv e
      (f (((g 0 0 * Q.1.a : ℤ) : Zsqrtd (-(p : ℤ))) -
        (g 1 0 : Zsqrtd (-(p : ℤ))) *
          (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd (-(p : ℤ)))))
      (conductorTwoMaximalOrderIdealOfForm p hp8 (Q.transform g))] at hcomap
  simpa [conductorTwoRingOfIntegersIdealOfForm, e, f] using hcomap

/-- The ring-of-integers ideal attached to a conductor-`2` form is nonzero. -/
theorem conductorTwoRingOfIntegersIdealOfForm_ne_zero
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    conductorTwoRingOfIntegersIdealOfForm p hp8 Q ≠ 0 := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (-(p : ℤ)) (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)
  let x : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) :=
    e.symm (((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)))
  have hxmem : x ∈ conductorTwoRingOfIntegersIdealOfForm p hp8 Q := by
    change (e.symm (((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)))) ∈
      conductorTwoRingOfIntegersIdealOfForm p hp8 Q
    exact self_mem_conductorTwoRingOfIntegersIdealOfForm p hp8 Q
  intro hI
  have hxzero : x = 0 := by
    have hxmem0 : x ∈ (0 : Ideal (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) := by
      simpa [hI] using hxmem
    simpa using hxmem0
  have haZ :
      ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) = 0 := by
    let aZ : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4) :=
      ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4))
    change aZ = 0
    calc
      aZ = e x := by
        dsimp [x, aZ]
        exact (e.apply_symm_apply aZ).symm
      _ = e 0 := congrArg e hxzero
      _ = 0 := by simpa using e.map_zero
  have ha0 : Q.1.a = 0 := by
    simpa using congrArg QuadraticAlgebra.re haZ
  exact (ne_of_gt Q.2.2.2.1) ha0

/-- The ring-of-integers ideal attached to a conductor-`2` form, packaged as a
nonzero ideal for `ClassGroup.mk0`. -/
noncomputable def conductorTwoRingOfIntegersNonzeroIdealOfForm
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    nonZeroDivisors (Ideal (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) :=
  ⟨conductorTwoRingOfIntegersIdealOfForm p hp8 Q,
    mem_nonZeroDivisors_iff_ne_zero.mpr
      (conductorTwoRingOfIntegersIdealOfForm_ne_zero p hp8 Q)⟩

/-- The maximal-order ideal class attached to a conductor-`2` form by extending
its Cox/order ideal to `𝓞 (Qsqrtd (-p))`. -/
noncomputable def conductorTwoRingOfIntegersIdealClassOfForm
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))) :=
  ClassGroup.mk0 (conductorTwoRingOfIntegersNonzeroIdealOfForm p hp8 Q)

/-- Properly transforming a conductor-`2` form does not change the maximal-order
ideal class obtained by extending its Cox/order ideal. -/
theorem conductorTwoRingOfIntegersIdealClassOfForm_eq_of_transform
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q R : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (g : BinaryQuadraticForm.SL2Z) (hR : R.1 = BinaryQuadraticForm.transform Q.1 g) :
    conductorTwoRingOfIntegersIdealClassOfForm p hp8 Q =
      conductorTwoRingOfIntegersIdealClassOfForm p hp8 R := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (-(p : ℤ)) (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)
  let f := conductorTwoSuborderHom p hp8
  let alpha : Zsqrtd (-(p : ℤ)) :=
    (((BinaryQuadraticForm.transform Q.1 g).a : ℤ) : Zsqrtd (-(p : ℤ)))
  let lam : Zsqrtd (-(p : ℤ)) :=
    (((g 0 0 * Q.1.a : ℤ) : Zsqrtd (-(p : ℤ))) -
      (g 1 0 : Zsqrtd (-(p : ℤ))) *
        (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd (-(p : ℤ))))
  let x : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) := e.symm (f alpha)
  let y : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) := e.symm (f lam)
  have hx : x ≠ 0 := by
    intro hx0
    have hfalpha_zero : f alpha = 0 := by
      calc
        f alpha = e x := by
          dsimp [x]
          exact (e.apply_symm_apply (f alpha)).symm
        _ = e 0 := congrArg e hx0
        _ = 0 := by simpa using e.map_zero
    have halpha_zero : alpha = 0 := by
      exact (conductorTwoSuborderHom_injective p hp8) (by simpa [f] using hfalpha_zero)
    have ha_zero : (BinaryQuadraticForm.transform Q.1 g).a = 0 := by
      have hre := congrArg QuadraticAlgebra.re halpha_zero
      change (BinaryQuadraticForm.transform Q.1 g).a = 0 at hre
      exact hre
    exact (ne_of_gt (Q.transform g).2.2.2.1) ha_zero
  have hy : y ≠ 0 := by
    intro hy0
    have hflam_zero : f lam = 0 := by
      calc
        f lam = e y := by
          dsimp [y]
          exact (e.apply_symm_apply (f lam)).symm
        _ = e 0 := congrArg e hy0
        _ = 0 := by simpa using e.map_zero
    have hlam_zero : lam = 0 := by
      exact (conductorTwoSuborderHom_injective p hp8) (by simpa [f] using hflam_zero)
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := sl2z_det_fin_two g
    have hlam_ne : lam ≠ 0 := by
      dsimp [lam]
      exact CoxIdealRelation.lam_ne_zero (DD := -(p : ℤ)) (bb := 0)
        (A := Q.1.a) (p := g 0 0) (r := g 1 0) (u := (-Q.1.b) / 2)
        (ne_of_gt Q.2.2.2.1) hdet
    exact hlam_ne hlam_zero
  have hideal := conductorTwoRingOfIntegersIdeal_relation_transform p hp8 Q g
  have hform : Q.transform g = R := Subtype.ext hR.symm
  rw [hform] at hideal
  unfold conductorTwoRingOfIntegersIdealClassOfForm
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa [x, y, alpha, lam, e, f, conductorTwoRingOfIntegersNonzeroIdealOfForm] using hideal

/-- Properly equivalent conductor-`2` forms have the same maximal-order ideal
class after extending their Cox/order ideals. -/
theorem conductorTwoRingOfIntegersIdealClassOfForm_eq_of_properEquivalent
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q R : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (hQR : BinaryQuadraticForm.PrimitivePositiveDefiniteForm.ProperEquivalent Q R) :
    conductorTwoRingOfIntegersIdealClassOfForm p hp8 Q =
      conductorTwoRingOfIntegersIdealClassOfForm p hp8 R := by
  rcases hQR with ⟨g, hg⟩
  exact conductorTwoRingOfIntegersIdealClassOfForm_eq_of_transform p hp8 Q R g hg.symm

/-- The maximal-order ideal class attached to a conductor-`2` form class by
extending the representative-level Cox/order ideal. -/
noncomputable def conductorTwoRingOfIntegersIdealClassOfFormClass
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) :
    BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) →
      ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))) := by
  classical
  exact Quotient.lift (conductorTwoRingOfIntegersIdealClassOfForm p hp8)
    (conductorTwoRingOfIntegersIdealClassOfForm_eq_of_properEquivalent p hp8)

/-- On representatives, the conductor-`2` form-class extension map is the
maximal-order ideal class obtained from the concrete extended Cox/order ideal. -/
theorem conductorTwoRingOfIntegersIdealClassOfFormClass_mk
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    conductorTwoRingOfIntegersIdealClassOfFormClass p hp8
        (Quotient.mk (BinaryQuadraticForm.primitivePositiveDefiniteFormSetoid _) Q) =
      conductorTwoRingOfIntegersIdealClassOfForm p hp8 Q :=
  rfl

/-- In the inert conductor-`2` branch, the unit group of `𝓞(ℚ(√-p))/(2)` has
exactly three elements. -/
theorem conductor_two_ringOfIntegers_quotient_span_two_units_card_eq_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) :
    Nat.card (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
      Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))ˣ = 3 := by
  exact RingOfIntegers.ringOfIntegers_quotient_span_two_units_card_eq_three_of_mod_eight_eq_five
    (-(p : ℤ)) (Int.neg_natCast_emod_eight_eq_five_of_nat_mod_eight_eq_three hp8)

/-- In the inert conductor-`2` branch, the unit group of `𝓞(ℚ(√-p))/(2)` has
at most three elements. -/
theorem conductor_two_ringOfIntegers_quotient_span_two_units_card_le_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) :
    Nat.card (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
      Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))ˣ ≤ 3 := by
  exact le_of_eq (conductor_two_ringOfIntegers_quotient_span_two_units_card_eq_three p hp8)

/-- The conductor-`2` local factor in Cox's order class-number formula is `3`
for the inert-prime branch `p ≡ 3 (mod 8)`. -/
theorem conductor_two_order_class_number_formula_factor_eq_three
    (p : ℕ) (hp8 : p % 8 = 3) :
    (2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2) = 3 := by
  rw [kroneckerTwo_neg_natCast_eq_neg_one_of_nat_mod_eight_eq_three hp8]
  norm_num

/-- Cox order class-number formula for the conductor-`2` order in the
non-exceptional inert branch.

This is exactly the missing order/Picard class-number formula input: primitive
reduced forms of discriminant `-4p` count the conductor-`2` order class number,
and Cox's formula relates it to the maximal-order class number with the inert
local factor at `2`.  The hypothesis `p ≠ 3` records that the unit index in Cox
Theorem 7.24 is `1`; the exceptional `p = 3` order has extra units. -/
def ConductorTwoOrderClassNumberFormula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (_hp8 : p % 8 = 3) (_hp_ne_three : p ≠ 3) : Prop :=
  ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
    (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
      ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2))

/-- A concrete reduced-form cardinality computation supplies the Forms-side
conductor-`2` class-number-three statement. -/
theorem conductorTwoFormClassNumberThree_of_reducedForms_card
    (p : ℕ)
    (hcard :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3) :
    ConductorTwoFormClassNumberThree p :=
  hcard

/-- The Forms-side conductor-`2` statement is equivalent to the reduced-form
cardinality statement at discriminant `-4p`. -/
theorem conductorTwoFormClassNumberThree_iff_reducedForms_card
    (p : ℕ) :
    ConductorTwoFormClassNumberThree p ↔
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  rfl

/-- Forms-side class-number-three data supplies the conductor-`2`
ring-class-number input used by the Weber/CM layer. -/
theorem ringClassNumberConductorTwoEqualsThree_of_forms
    {p : ℕ} (hforms : ConductorTwoFormClassNumberThree p) :
    RingClassNumberConductorTwoEqualsThree p := by
  -- This is the remaining order/forms class-number bridge: it should identify
  -- the primitive reduced-form count for discriminant `-4p` with the ring
  -- class number of the conductor-`2` order.
  sorry

/-- A reduced-form cardinality computation at discriminant `-4p` supplies the
core conductor-`2` ring-class-number input. -/
theorem ringClassNumberConductorTwoEqualsThree_of_reducedForms_card
    (p : ℕ)
    (hcard :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductorTwoFormClassNumberThree_of_reducedForms_card p hcard)

/-- For the non-exceptional inert Heegner primes, the conductor-`2`
discriminant `-4p` has exactly three primitive reduced positive definite forms.

This is the finite-table reduced-form computation behind the conductor-`2`
ring/order/forms bridge. It intentionally avoids the `p = 3` unit-exception
case, where the order class-number formula has a different unit index. -/
theorem conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  rw [BinaryQuadraticForm.enumPrimitiveReducedForms_card_eq_length]
  norm_num [heegnerPrimeSet] at hp_mem
  rcases hp_mem with hp | hp | hp | hp | hp | hp
  · omega
  · have hp' : p = 11 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg44_length
  · have hp' : p = 19 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg76_length
  · have hp' : p = 43 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg172_length
  · have hp' : p = 67 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg268_length
  · have hp' : p = 163 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg652_length

/-- In the non-exceptional inert prime branch, the conductor-`2` discriminant
`-4p` has at least three primitive reduced positive definite forms.

For `p = 11` this uses the finite table. For larger `p`, the three forms are
`(1, 0, p)` and `(4, ±2, (p + 1) / 4)`, with the quotient represented by the
integer `2 * (p / 8) + 1`. -/
theorem three_le_conductor_two_reduced_forms_card
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3) :
    3 ≤ (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card := by
  by_cases hp11 : p = 11
  · subst p
    have hcard :=
      conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet 11
        (by norm_num [heegnerPrimeSet]) (by norm_num)
    omega
  · obtain ⟨m, hm, hm_ge, hm_odd⟩ :
        ∃ m : ℤ, 4 * m = (p : ℤ) + 1 ∧ 4 ≤ m ∧ m % 2 = 1 := by
      refine ⟨2 * (p / 8 : ℤ) + 1, ?_, ?_, ?_⟩
      · omega
      · have hp_div_ge : 2 ≤ p / 8 := by omega
        omega
      · omega
    exact
      BinaryQuadraticForm.three_le_card_enumPrimitiveReducedForms_neg_four_mul
        p m hp hm hm_ge hm_odd

/-- In the inert branch, class number one for `ℚ(√-p)` is equivalent on the
Forms side to the field-discriminant reduced-form count at `-p`. -/
theorem field_reduced_forms_card_eq_classNumberQsqrtd
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card =
      classNumberQsqrtd (-(p : ℤ)) := by
  have hp_pos_int : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hdneg : -(p : ℤ) < 0 := neg_neg_iff_pos.mpr hp_pos_int
  have hclass_forms := classNumberQsqrtd_eq_reducedForms_card (-(p : ℤ)) hdneg
  rw [BinaryQuadraticForm.fieldDiscriminant_neg_natCast_of_nat_mod_eight_eq_three hp8]
    at hclass_forms
  exact hclass_forms.symm

/-- Cox's field-discriminant form-class equivalence specialized to the inert
branch `d = -p`, where `fieldDiscriminant (-p) = -p`. -/
noncomputable def inertFieldFormClassEquivClassGroup
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) :
    BinaryQuadraticForm.FormClass (-(p : ℤ)) ≃
      ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))) := by
  have hp_pos_int : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hdneg : -(p : ℤ) < 0 := by omega
  exact
    (Equiv.cast (congrArg BinaryQuadraticForm.FormClass
      (BinaryQuadraticForm.fieldDiscriminant_neg_natCast_of_nat_mod_eight_eq_three hp8))).symm.trans
      (BinaryQuadraticForm.formClassEquivClassGroup (d := -(p : ℤ)) hdneg)

/-- In the inert branch, class number one for `ℚ(√-p)` gives a singleton
reduced-form enumeration at field discriminant `-p`. -/
theorem field_reduced_forms_card_eq_one_of_classNumber_one
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card = 1 := by
  rw [field_reduced_forms_card_eq_classNumberQsqrtd p hp hp8, hclass]

/-- The remaining upper bound `h(-4p) ≤ 3`, combined with the three explicit
conductor-`2` reduced forms, gives the exact conductor-`2` reduced-form count. -/
theorem conductor_two_reduced_forms_card_eq_three_of_card_le_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 :=
  le_antisymm hupper (three_le_conductor_two_reduced_forms_card p hp hp8 hp_ne_three)

/-- Class number one for the maximal order, plus the remaining conductor-`2`
upper bound, gives the exact conductor-`2` reduced-form count. The class-number
hypothesis is first transported to the field-discriminant reduced-form count,
so this theorem is ready for either a coordinate upper-bound proof or a future
quadratic-order/Picard proof. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  have _hfield :=
    field_reduced_forms_card_eq_one_of_classNumber_one p hp hp8 hclass
  exact conductor_two_reduced_forms_card_eq_three_of_card_le_three p hp hp8 hp_ne_three hupper

/-- Forms-side cover data for the conductor-`2` upper-bound step.

This is the explicit remaining finite-fiber interface behind the upper bound
`h(-4p) ≤ 3 * h(-p)`: every conductor-`2` reduced form maps to a field
discriminant reduced form, and each field reduced form has at most three
conductor-`2` reduced-form preimages.  Constructing this map can be done either
by a direct form-theoretic conductor-lowering argument or by the corresponding
quadratic-order/Picard-group map. -/
structure ConductorTwoReducedFormCoverData (p : ℕ) where
  /-- The conductor-lowering map on raw reduced-form representatives. -/
  toFieldForm : BinaryQuadraticForm → BinaryQuadraticForm
  /-- The map sends conductor-`2` reduced forms of discriminant `-4p` to field
  reduced forms of discriminant `-p`. -/
  maps_mem : ∀ {Q : BinaryQuadraticForm},
    Q ∈ BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ))) →
      toFieldForm Q ∈ BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))
  /-- Every field-discriminant reduced form has at most three conductor-`2`
  reduced-form preimages. -/
  fiber_card_le_three : ∀ {R : BinaryQuadraticForm},
    R ∈ BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ)) →
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).filter
        fun Q => toFieldForm Q = R).card ≤ 3

/-- Typed finite-cover data for the conductor-`2` upper-bound step.

This is the same mathematical interface as `ConductorTwoReducedFormCoverData`,
but stated directly on finite reduced-form representative types.  A future
conductor-lowering construction can target this form without separately
carrying membership proofs for raw forms. -/
structure ConductorTwoReducedFormRepCoverData (p : ℕ) where
  /-- The conductor-lowering map on finite conductor-`2` reduced representatives. -/
  toFieldRep :
    BinaryQuadraticForm.ReducedFormRep (-(4 * (p : ℤ))) →
      BinaryQuadraticForm.ReducedFormRep (-(p : ℤ))
  /-- Every field-discriminant reduced representative has at most three
  conductor-`2` reduced-representative preimages. -/
  fiber_card_le_three :
    ∀ R : BinaryQuadraticForm.ReducedFormRep (-(p : ℤ)),
      Fintype.card
        { Q : BinaryQuadraticForm.ReducedFormRep (-(4 * (p : ℤ))) // toFieldRep Q = R } ≤ 3

/-- Quotient-level conductor-`2` finite-cover data.

This is the most natural Forms-side target for a future Cox/order or
Picard-group construction: a map from primitive positive definite form classes
of order discriminant `-4p` to the field-discriminant form classes of
discriminant `-p`, with fibers of size at most three. -/
structure ConductorTwoFormClassCoverData (p : ℕ) where
  /-- The conductor-lowering map on primitive positive definite form classes. -/
  toFieldClass :
    BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) →
      BinaryQuadraticForm.FormClass (-(p : ℤ))
  /-- Every field-discriminant form class has at most three conductor-`2`
  form-class preimages. -/
  fiber_card_le_three :
    ∀ R : BinaryQuadraticForm.FormClass (-(p : ℤ)),
      Nat.card
        { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) // toFieldClass Q = R } ≤ 3

/-- Ideal-class-level conductor-`2` finite-cover data.

This is the order/Picard-shaped version of the remaining upper-bound step:
the canonical maximal-order ideal class obtained by extending conductor-`2`
Cox/order ideals has fibers of size at most three.  The quotient descent for
this canonical map is already proved by
`conductorTwoRingOfIntegersIdealClassOfFormClass`; the remaining input is only
the order/Picard fiber bound. -/
structure ConductorTwoIdealClassCoverData
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) where
  /-- Every maximal-order ideal class has at most three conductor-`2` form-class
  preimages under the canonical extension map. -/
  fiber_card_le_three :
    ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
      Nat.card
        { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
          conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C } ≤ 3

/-- Picard-exact-sequence-shaped kernel data for the conductor-`2` extension map.

The local target is the concrete unit group `(𝓞K / 2𝓞K)ˣ`.  The remaining
order/Picard input is the fiber injection into this local quotient; the inert
branch cardinal bound for the target is proved separately below. -/
structure ConductorTwoIdealClassKernelData
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) where
  /-- Every fiber of the conductor-`2` extension map injects into the local
  quotient `(𝓞K / 2𝓞K)ˣ`. -/
  fiberEmbedding :
    ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
      { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
        conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C } ↪
          (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
            Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))ˣ

/-- Kernel data gives the ideal-class fiber bound for the canonical
conductor-`2` extension map. -/
theorem conductor_two_ideal_class_fiber_card_le_three_of_kernel_data
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hkernel : ConductorTwoIdealClassKernelData p hp8)
    (C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) :
    Nat.card
      { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
        conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C } ≤ 3 := by
  letI := RingOfIntegers.ringOfIntegers_quotient_span_two_fintype_of_mod_four_eq_one
    (-(p : ℤ)) (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)
  exact le_trans
    (Nat.card_le_card_of_injective (hkernel.fiberEmbedding C)
      (hkernel.fiberEmbedding C).injective)
    (conductor_two_ringOfIntegers_quotient_span_two_units_card_le_three p hp8)

/-- Ideal-class-level conductor-`2` cover data supplies the quotient-level
form-class cover by transporting maximal-order ideal classes back to
field-discriminant form classes via Cox's equivalence. -/
noncomputable def conductor_two_form_class_cover_data_of_ideal_class_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hcover : ConductorTwoIdealClassCoverData p hp8) :
    ConductorTwoFormClassCoverData p where
  toFieldClass := fun Q =>
    (inertFieldFormClassEquivClassGroup p hp hp8).symm
      (conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q)
  fiber_card_le_three := by
    intro R
    let e := inertFieldFormClassEquivClassGroup p hp hp8
    let F := conductorTwoRingOfIntegersIdealClassOfFormClass p hp8
    have hcard :
        Nat.card
          { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
            e.symm (F Q) = R } =
          Nat.card
            { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
              F Q = e R } := by
      exact Nat.card_congr
        { toFun := fun Q =>
            ⟨Q.1, by
              calc
                F Q.1 = e (e.symm (F Q.1)) := (e.apply_symm_apply (F Q.1)).symm
                _ = e R := congrArg (fun C => e C) Q.2⟩
          invFun := fun Q =>
            ⟨Q.1, by
              calc
                e.symm (F Q.1) = e.symm (e R) :=
                  congrArg (fun C => e.symm C) Q.2
                _ = R := e.symm_apply_apply R⟩
          left_inv := by
            intro Q
            cases Q
            rfl
          right_inv := by
            intro Q
            cases Q
            rfl }
    rw [hcard]
    exact hcover.fiber_card_le_three (e R)

/-- Quotient-level conductor-`2` finite-fiber cover data gives the upper bound
on finite form-class cardinalities. -/
theorem conductor_two_formClass_card_le_three_mul_field_formClass_card_of_class_cover
    (p : ℕ) (hcover : ConductorTwoFormClassCoverData p) :
    Fintype.card (BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) ≤
      3 * Fintype.card (BinaryQuadraticForm.FormClass (-(p : ℤ))) := by
  classical
  let S : Finset (BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) := Finset.univ
  let T : Finset (BinaryQuadraticForm.FormClass (-(p : ℤ))) := Finset.univ
  have hbound : S.card ≤ 3 * T.card := by
    have hmaps : ∀ Q ∈ S, hcover.toFieldClass Q ∈ T := by
      simp [T]
    have hfiber : ∀ R ∈ T, (S.filter fun Q => hcover.toFieldClass Q = R).card ≤ 3 := by
      intro R _hR
      have hcard :
          Nat.card
              { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
                hcover.toFieldClass Q = R } =
            (S.filter fun Q => hcover.toFieldClass Q = R).card := by
        apply Nat.subtype_card
        intro Q
        simp [S]
      rw [← hcard]
      exact hcover.fiber_card_le_three R
    exact Finset.card_le_mul_card_image_of_maps_to hmaps 3 hfiber
  simpa [S, T] using hbound

/-- Quotient-level conductor-`2` finite-fiber cover data gives the upper bound
`#forms(-4p) ≤ 3 * #forms(-p)` on reduced-form enumerations. -/
theorem conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_class_cover
    (p : ℕ) (hcover : ConductorTwoFormClassCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card := by
  have hbound :=
    conductor_two_formClass_card_le_three_mul_field_formClass_card_of_class_cover
      p hcover
  simpa [BinaryQuadraticForm.formClass_card_eq_enumPrimitiveReducedForms_card] using hbound

/-- Quotient-level conductor-`2` finite-fiber cover data gives the upper bound
`#forms(-4p) ≤ 3 * h(-p)` after transporting the field reduced-form count to
`classNumberQsqrtd`. -/
theorem conductor_two_reduced_forms_card_le_three_mul_classNumber_of_class_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hcover : ConductorTwoFormClassCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * classNumberQsqrtd (-(p : ℤ)) := by
  have hbound :=
    conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_class_cover
      p hcover
  rwa [field_reduced_forms_card_eq_classNumberQsqrtd p hp hp8] at hbound

/-- Class number one plus quotient-level conductor-`2` cover data gives the exact
conductor-`2` reduced-form count. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_class_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoFormClassCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
    p hp hp8 hp_ne_three hclass
    (by
      have hupper :=
        conductor_two_reduced_forms_card_le_three_mul_classNumber_of_class_cover
          p hp hp8 hcover
      rw [hclass] at hupper
      omega)

/-- Class number one plus quotient-level conductor-`2` cover data supplies
Forms-side class-number-three data. -/
theorem conductor_two_form_class_number_three_of_classNumber_one_of_class_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoFormClassCoverData p) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_class_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- Class number one plus quotient-level conductor-`2` cover data supplies the
core ring-class-number input. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_class_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoFormClassCoverData p) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three_of_classNumber_one_of_class_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- A conductor-`2` finite-fiber cover gives the upper bound
`#forms(-4p) ≤ 3 * #forms(-p)` on reduced-form enumerations. -/
theorem conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_cover
    (p : ℕ) (hcover : ConductorTwoReducedFormCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card := by
  let S := BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))
  let T := BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))
  have hmaps : ∀ Q ∈ S, hcover.toFieldForm Q ∈ T := by
    intro Q hQ
    exact hcover.maps_mem (by simpa [S] using hQ)
  have hfiber : ∀ R ∈ T, (S.filter fun Q => hcover.toFieldForm Q = R).card ≤ 3 := by
    intro R hR
    exact hcover.fiber_card_le_three (by simpa [T] using hR)
  exact Finset.card_le_mul_card_image_of_maps_to hmaps 3 hfiber

/-- A conductor-`2` finite-fiber cover gives the upper bound
`#forms(-4p) ≤ 3 * h(-p)` after transporting the field reduced-form count to
`classNumberQsqrtd`. -/
theorem conductor_two_reduced_forms_card_le_three_mul_classNumber_of_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hcover : ConductorTwoReducedFormCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * classNumberQsqrtd (-(p : ℤ)) := by
  have hbound :=
    conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_cover
      p hcover
  rwa [field_reduced_forms_card_eq_classNumberQsqrtd p hp hp8] at hbound

/-- Typed conductor-`2` finite-fiber cover data gives the upper bound
`#forms(-4p) ≤ 3 * #forms(-p)` on reduced-form enumerations. -/
theorem conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_rep_cover
    (p : ℕ) (hcover : ConductorTwoReducedFormRepCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card := by
  classical
  let S := BinaryQuadraticForm.ReducedFormRep (-(4 * (p : ℤ)))
  let T := BinaryQuadraticForm.ReducedFormRep (-(p : ℤ))
  have hrep := by
    have hmaps : ∀ Q ∈ (Finset.univ : Finset S), hcover.toFieldRep Q ∈
        (Finset.univ : Finset T) := by
      simp
    have hfiber :
        ∀ R ∈ (Finset.univ : Finset T),
          ((Finset.univ : Finset S).filter fun Q => hcover.toFieldRep Q = R).card ≤ 3 := by
      intro R _hR
      simpa [Fintype.card_subtype] using hcover.fiber_card_le_three R
    exact Finset.card_le_mul_card_image_of_maps_to hmaps 3 hfiber
  simpa [S, T, BinaryQuadraticForm.reducedFormRep_card] using hrep

/-- Typed conductor-`2` finite-fiber cover data gives the upper bound
`#forms(-4p) ≤ 3 * h(-p)` after transporting the field reduced-form count to
`classNumberQsqrtd`. -/
theorem conductor_two_reduced_forms_card_le_three_mul_classNumber_of_rep_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hcover : ConductorTwoReducedFormRepCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * classNumberQsqrtd (-(p : ℤ)) := by
  have hbound :=
    conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_rep_cover
      p hcover
  rwa [field_reduced_forms_card_eq_classNumberQsqrtd p hp hp8] at hbound

/-- Class number one plus typed conductor-`2` cover data gives the exact
conductor-`2` reduced-form count. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_rep_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormRepCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
    p hp hp8 hp_ne_three hclass
    (by
      have hupper :=
        conductor_two_reduced_forms_card_le_three_mul_classNumber_of_rep_cover
          p hp hp8 hcover
      rw [hclass] at hupper
      omega)

/-- Class number one plus typed conductor-`2` cover data supplies Forms-side
class-number-three data. -/
theorem conductor_two_form_class_number_three_of_classNumber_one_of_rep_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormRepCoverData p) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_rep_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- Class number one plus typed conductor-`2` cover data supplies the core
ring-class-number input. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_rep_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormRepCoverData p) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three_of_classNumber_one_of_rep_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- If the field reduced-form enumeration is a singleton and the conductor-`2`
cover has fibers of size at most three, then the conductor-`2` reduced-form
enumeration has size at most three. -/
theorem conductor_two_reduced_forms_card_le_three_of_field_card_eq_one_of_cover
    (p : ℕ)
    (hfield : (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card = 1)
    (hcover : ConductorTwoReducedFormCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3 := by
  have hbound :=
    conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_cover
      p hcover
  rw [hfield] at hbound
  omega

/-- Class number one plus conductor-`2` cover data gives the exact conductor-`2`
reduced-form count. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
    p hp hp8 hp_ne_three hclass
    (conductor_two_reduced_forms_card_le_three_of_field_card_eq_one_of_cover p
      (field_reduced_forms_card_eq_one_of_classNumber_one p hp hp8 hclass) hcover)

/-- Class number one plus conductor-`2` cover data supplies Forms-side
class-number-three data. -/
theorem conductor_two_form_class_number_three_of_classNumber_one_of_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormCoverData p) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- Class number one plus conductor-`2` cover data supplies the core
ring-class-number input. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormCoverData p) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three_of_classNumber_one_of_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- The finite inert-Heegner-prime reduced-form computation supplies
Forms-side conductor-`2` class-number-three data. -/
theorem conductor_two_form_class_number_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet
      p hp_mem hp_ne_three)

/-- The finite inert-Heegner-prime reduced-form computation supplies the core
conductor-`2` ring-class-number-three input. -/
theorem conductor_two_class_number_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three_of_mem_heegnerPrimeSet
      p hp_mem hp_ne_three)

/-- A conductor-`2` reduced-form upper bound supplies Forms-side
class-number-three data in the non-exceptional inert branch. -/
theorem conductor_two_form_class_number_three_of_card_le_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_card_le_three p hp hp8 hp_ne_three hupper)

/-- Class number one plus a conductor-`2` reduced-form upper bound supplies
Forms-side conductor-`2` class-number-three data. -/
theorem conductor_two_form_class_number_three_of_classNumber_one_of_card_le_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
      p hp hp8 hp_ne_three hclass hupper)

/-- A conductor-`2` reduced-form upper bound supplies the core ring-class-number
input in the non-exceptional inert branch. -/
theorem conductor_two_class_number_three_of_card_le_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three_of_card_le_three p hp hp8 hp_ne_three hupper)

/-- Class number one plus a conductor-`2` reduced-form upper bound supplies the
core ring-class-number input in the non-exceptional inert branch. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_card_le_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three_of_classNumber_one_of_card_le_three
      p hp hp8 hp_ne_three hclass hupper)

/-- On the finite non-exceptional inert Heegner-prime table, the conductor-`2`
reduced-form count agrees with the specialized order class-number formula. -/
theorem conductor_two_reduced_forms_card_order_class_number_formula_of_mem_heegnerPrimeSet
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
      (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
        ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2)) := by
  have hcard :=
    conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet p hp_mem hp_ne_three
  have hclass : classNumberQsqrtd (-(p : ℤ)) = 1 := by
    unfold classNumberQsqrtd
    apply classNumber_eq_one_of_mem_heegnerSet
    norm_num [heegnerSet, heegnerPrimeSet] at hp_mem ⊢
    omega
  have hfactor := conductor_two_order_class_number_formula_factor_eq_three p hp8
  rw [hcard, hclass, hfactor]
  norm_num

/-- On the finite non-exceptional inert Heegner-prime table, the specialized
order class-number formula holds. -/
theorem conductor_two_order_class_number_formula_of_mem_heegnerPrimeSet
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three :=
  conductor_two_reduced_forms_card_order_class_number_formula_of_mem_heegnerPrimeSet
    p hp8 hp_mem hp_ne_three

/-- The canonical conductor-`2` ideal-class extension map supplies the
ideal-class cover data once explicit kernel data is available. -/
def conductor_two_ideal_class_cover_data_of_kernel_data
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hkernel : ConductorTwoIdealClassKernelData p hp8) :
    ConductorTwoIdealClassCoverData p hp8 := by
  exact {
    fiber_card_le_three := fun C =>
      conductor_two_ideal_class_fiber_card_le_three_of_kernel_data
        p hp8 hkernel C }

/-- **Conductor-lowering form-class cover, conductor `2`.** In the inert prime
family `d = -p`, conductor-`2` form classes of discriminant `-4p` map to
field-discriminant form classes of discriminant `-p` with fibers of size at most
three, once explicit ideal-class kernel data is available. -/
noncomputable def conductor_two_form_class_cover_data_of_kernel_data
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hkernel : ConductorTwoIdealClassKernelData p hp8) :
    ConductorTwoFormClassCoverData p :=
  conductor_two_form_class_cover_data_of_ideal_class_cover p hp hp8
    (conductor_two_ideal_class_cover_data_of_kernel_data p hp8 hkernel)

/-- Once the conductor-`2` order class-number formula is available, class
number one for the maximal order and the inert local factor `3` give exactly
three conductor-`2` primitive reduced forms. -/
theorem conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hformula :
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
        (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
          ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2)))
    (hfactor : (2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2) = 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  have hcard_rat :
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
        3 := by
    rw [hformula, hclass, hfactor]
    norm_num
  exact_mod_cast hcard_rat

/-- The order class-number formula and class number one give exactly three
conductor-`2` primitive reduced forms. -/
theorem conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula_prop
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hformula : ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 :=
  conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula p
    hformula (conductor_two_order_class_number_formula_factor_eq_three p hp8) hclass

/-- The order class-number formula and class number one supply the Forms-side
class-number-three statement. -/
theorem conductorTwoFormClassNumberThree_of_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hformula : ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula_prop
      p hp8 hp_ne_three hformula hclass)

/-- The order class-number formula and class number one supply the core
ring-class-number input. -/
theorem ringClassNumberConductorTwoEqualsThree_of_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hformula : ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductorTwoFormClassNumberThree_of_order_class_number_formula
      p hp8 hp_ne_three hformula hclass)

/-- With maximal-order class number one, the conductor-`2` Forms target is
equivalent to the non-exceptional Cox order class-number formula.

This isolates the remaining mathematical input for
`conductor_two_form_class_number_three`: after the local factor at `2` has been
computed, proving the conductor-`2` form class number is the same as proving
Cox 7.24 / Corollary 7.28 in the `p ≠ 3` branch. -/
theorem conductorTwoFormClassNumberThree_iff_order_class_number_formula_of_classNumber_one
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    ConductorTwoFormClassNumberThree p ↔
      ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three := by
  constructor
  · intro hforms
    unfold ConductorTwoFormClassNumberThree at hforms
    unfold ConductorTwoOrderClassNumberFormula
    rw [hforms, hclass, conductor_two_order_class_number_formula_factor_eq_three p hp8]
    norm_num
  · intro hformula
    exact conductorTwoFormClassNumberThree_of_order_class_number_formula
      p hp8 hp_ne_three hformula hclass

/-- Formula equality and class number one give exactly three conductor-`2` primitive
reduced forms. -/
theorem conductorTwoFormClassNumberThree_of_order_class_number_formula_eq
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hformula :
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
        (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
          ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2)))
    (hfactor : (2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2) = 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula p
      hformula hfactor hclass)

/-- Once the conductor-`2` order class-number formula is available, class
number one for the maximal order supplies the core ring-class-number input. -/
theorem ringClassNumberConductorTwoEqualsThree_of_order_class_number_formula_eq
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hformula :
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
        (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
          ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2)))
    (hfactor : (2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2) = 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductorTwoFormClassNumberThree_of_order_class_number_formula_eq p
      hformula hfactor hclass)

/-- **Cox order class-number formula input, conductor `2`.** In the
non-exceptional inert prime branch, Cox's order class-number formula identifies
the conductor-`2` reduced-form count with the maximal-order class number times
the local factor at `2`.

This is now the remaining conductor-`2` mathematical input for the Forms
provider.  It should be supplied by Cox 7.24 / Corollary 7.28, or by an
equivalent quadratic-order/Picard-group computation. -/
theorem conductor_two_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3) :
    ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three := by
  -- Cox 7.24 / Corollary 7.28, or an equivalent quadratic-order Picard-group
  -- construction, belongs here. The local factor at `2` is already closed by
  -- `conductor_two_order_class_number_formula_factor_eq_three`.
  sorry

/-- In the inert prime family `d = -p`, class number one for `ℚ(√-p)` gives
three primitive reduced positive definite forms of conductor-`2` discriminant
`-4p`, away from the unit-exception case `p = 3`. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula_prop
    p hp8 hp_ne_three (conductor_two_order_class_number_formula p hp hp8 hp_ne_three)
    hclass

/-- Target-shaped conductor-`2` reduced-form class-number statement.

This version derives the squarefree parameter facts from the prime hypothesis,
so its assumptions match the Baker-Heegner-Stark inert branch:
`h(-p) = 1`, `p` prime, `p % 8 = 3`, and `p ≠ 3`. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_prime
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1)) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  haveI : Fact (Squarefree (-(p : ℤ))) :=
    ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
  haveI : Fact ((-(p : ℤ)) ≠ 1) :=
    ⟨Int.neg_natCast_ne_one p⟩
  exact conductor_two_reduced_forms_card_eq_three_of_classNumber_one
    p hp hp8 hp_ne_three hclass

/-- **Cox forms class-number input.** In the inert prime family `d = -p`, class
number one for `ℚ(√-p)` gives Forms-side class-number-three data for primitive
positive definite forms of conductor-`2` discriminant `-4p`, away from the
unit-exception case `p = 3`. -/
theorem conductor_two_form_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    ConductorTwoFormClassNumberThree p := by
  exact conductorTwoFormClassNumberThree_of_order_class_number_formula
    p hp8 hp_ne_three (conductor_two_order_class_number_formula p hp hp8 hp_ne_three)
    hclass

/-- Target-shaped Forms-side conductor-`2` class-number statement.

This wrapper removes the auxiliary `Fact` parameters by deriving them from
`Nat.Prime p`.  The remaining mathematical input is still Cox 7.24 / Corollary
7.28, isolated by `conductor_two_order_class_number_formula`. -/
theorem conductor_two_form_class_number_three_of_prime
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1)) :
    ConductorTwoFormClassNumberThree p := by
  exact conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_prime
      p hp hp8 hp_ne_three hclass)

/-- The reduced-forms provider supplies the core conductor-`2` ring-class-number
input in the non-exceptional inert branch. -/
theorem conductor_two_class_number_three_of_forms
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    RingClassNumberConductorTwoEqualsThree p := by
  exact ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three p hp hp8 hp_ne_three hclass)

/-- Target-shaped core conductor-`2` ring-class-number statement supplied by the
Forms route. -/
theorem conductor_two_class_number_three_of_forms_of_prime
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1)) :
    RingClassNumberConductorTwoEqualsThree p := by
  exact ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three_of_prime p hp hp8 hp_ne_three hclass)

/-- **Deep Weber/CM input from ring-class-number three, via the Forms provider.**
The conductor-`2` ring-class-number-three datum supplies the refined Weber data:
a concrete Heegner equation solution, the associated gamma value, and its
finite-table association with `p`, in the non-exceptional inert branch `p ≠ 3`. -/
theorem conductor_two_weber_data_of_ring_class_number_three_of_forms
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3) (horder : RingClassNumberConductorTwoEqualsThree p) :
    Nonempty (ConductorTwoClassNumberThreeWeberData p) := by
  sorry

/-- The Forms provider turns conductor-`2` ring-class-number-three data into
Stark-Heegner algebraic data. -/
theorem exists_weber_data_of_conductor_two_class_number_three_of_forms
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3)
    (horder : RingClassNumberConductorTwoEqualsThree p) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact exists_weber_data_of_conductor_two_weber_data
    (conductor_two_weber_data_of_ring_class_number_three_of_forms p hp hp8 hp_ne_three horder)

/-- The reduced-forms route supplies Weber/CM algebraic data from class number
one in the non-exceptional inert branch. -/
theorem exists_weber_data_of_classNumber_one_inert_prime_of_forms
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact exists_weber_data_of_conductor_two_class_number_three_of_forms p hp hp8 hp_ne_three
    (conductor_two_class_number_three_of_forms p hp hp8 hp_ne_three hclass)

/-- The reduced-forms route packaged as the core provider interface. -/
def formsInertPrimeWeberDataProvider : InertPrimeWeberDataProvider where
  exists_weber_data p _ _ hp hp8 hp_ne_three hclass :=
    exists_weber_data_of_classNumber_one_inert_prime_of_forms p hp hp8 hp_ne_three hclass

end Heegner
end QuadraticNumberFields
