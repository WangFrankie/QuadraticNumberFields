/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import BinaryQuadraticForms.Cox.IdealRelation
import FormClassGroup.ClassGroup.Law
import ImaginaryClassNumberOne.WeberCM.ConductorTwo.Basic
import QNFMathlib.RingTheory.Ideal.Span

/-!
# Residue and Cover Machinery for the Conductor-Two Route

This file contains the concrete conductor-`2` order inclusion, ideals, residue
units, ideal-class fibers, kernel certificates, and cover bridges used by the Weber/CM
conductor-`2` route.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

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
underlie the quotient-level cover map `ConductorTwoFormClassCover`. -/
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

/-- The integer leading coefficient itself belongs to the ring-of-integers
ideal attached to a conductor-`2` form. -/
theorem intCast_a_mem_conductorTwoRingOfIntegersIdealOfForm
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    ((Q.1.a : ℤ) : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))) ∈
      conductorTwoRingOfIntegersIdealOfForm p hp8 Q := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (-(p : ℤ)) (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)
  have h := self_mem_conductorTwoRingOfIntegersIdealOfForm p hp8 Q
  change e.symm ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (-(p : ℤ) / 4)) ∈
    conductorTwoRingOfIntegersIdealOfForm p hp8 Q at h
  convert h using 1
  exact (map_intCast e.symm Q.1.a).symm

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

/-- If the conductor-`2` representative has odd leading coefficient, then that
leading coefficient generates the unit ideal modulo `(2)` in the maximal order. -/
theorem span_intCast_a_sup_span_two_eq_top_of_odd_a
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (ha : Odd Q.1.a) :
    Ideal.span
        ({((Q.1.a : ℤ) : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _) ⊔
      Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  let O := 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))
  have ha_mem : ((Q.1.a : ℤ) : O) ∈
      Ideal.span ({((Q.1.a : ℤ) : O)} : Set O) :=
    Ideal.subset_span (by simp)
  have ha_mem_sup : ((Q.1.a : ℤ) : O) ∈
      Ideal.span ({((Q.1.a : ℤ) : O)} : Set O) ⊔
        Ideal.span ({(2 : O)} : Set O) :=
    Ideal.mem_sup_left ha_mem
  have h2_mem : (2 : O) ∈ Ideal.span ({(2 : O)} : Set O) :=
    Ideal.subset_span (by simp)
  have h2_mem_sup : (2 : O) ∈
      Ideal.span ({((Q.1.a : ℤ) : O)} : Set O) ⊔
        Ideal.span ({(2 : O)} : Set O) :=
    Ideal.mem_sup_right h2_mem
  rcases ha with ⟨k, hk⟩
  have h_one : (1 : O) = ((Q.1.a : ℤ) : O) - (k : O) * (2 : O) := by
    rw [hk]
    rw [Int.cast_add, Int.cast_mul]
    norm_num
    ring
  rw [h_one]
  exact Ideal.sub_mem _ ha_mem_sup (Ideal.mul_mem_left _ (k : O) h2_mem_sup)

/-- The residue unit represented by an odd leading coefficient of a conductor-`2`
form.  This is the local unit used in the conductor-`2` kernel map. -/
noncomputable def conductorTwoLeadingCoeffResidueUnitOfOddA
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (ha : Odd Q.1.a) :
    (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
      Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))ˣ :=
  Ideal.Quotient.unitOfSpanSupEqTop
    (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
    (((Q.1.a : ℤ) : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))))
    (span_intCast_a_sup_span_two_eq_top_of_odd_a p Q ha)

@[simp]
theorem conductorTwoLeadingCoeffResidueUnitOfOddA_coe
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (ha : Odd Q.1.a) :
    (conductorTwoLeadingCoeffResidueUnitOfOddA p Q ha :
      𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
        Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _)) =
      Ideal.Quotient.mk
        (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
        (((Q.1.a : ℤ) : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) := by
  exact Ideal.Quotient.coe_unitOfSpanSupEqTop _ _ _

/-- A chosen odd-leading-coefficient representative of a conductor-`2` form
class. -/
noncomputable def conductorTwoFormClassOddRepresentative
    (p : ℕ) (C : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) :
    BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))) :=
  BinaryQuadraticForm.oddARepresentativeOfDiscriminantNegFourMulNatCast p C

/-- The chosen conductor-`2` representative has odd leading coefficient. -/
theorem conductorTwoFormClassOddRepresentative_odd_a
    (p : ℕ) (C : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) :
    Odd (conductorTwoFormClassOddRepresentative p C).1.a :=
  BinaryQuadraticForm.oddARepresentativeOfDiscriminantNegFourMulNatCast_odd_a p C

/-- The chosen odd-leading representative represents the original form class. -/
theorem conductorTwoFormClassOddRepresentative_mk_eq
    (p : ℕ) (C : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) :
    Quotient.mk (BinaryQuadraticForm.primitivePositiveDefiniteFormSetoid _)
        (conductorTwoFormClassOddRepresentative p C) = C :=
  BinaryQuadraticForm.oddARepresentativeOfDiscriminantNegFourMulNatCast_mk_eq p C

/-- The residue unit attached to a conductor-`2` form class by choosing an
odd-leading representative. -/
noncomputable def conductorTwoFormClassResidueUnit
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (C : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) :
    (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
      Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))ˣ :=
  conductorTwoLeadingCoeffResidueUnitOfOddA p
    (conductorTwoFormClassOddRepresentative p C)
    (conductorTwoFormClassOddRepresentative_odd_a p C)

@[simp]
theorem conductorTwoFormClassResidueUnit_coe
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (C : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) :
    (conductorTwoFormClassResidueUnit p C :
      𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
        Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _)) =
      Ideal.Quotient.mk
        (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
        ((((conductorTwoFormClassOddRepresentative p C).1.a : ℤ) :
          𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) := by
  exact conductorTwoLeadingCoeffResidueUnitOfOddA_coe p
    (conductorTwoFormClassOddRepresentative p C)
    (conductorTwoFormClassOddRepresentative_odd_a p C)

/-- If the chosen conductor-`2` form representative has odd leading coefficient,
then its extended maximal-order ideal is coprime to `(2)`. -/
theorem span_two_sup_conductorTwoRingOfIntegersIdealOfForm_eq_top_of_odd_a
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (ha : Odd Q.1.a) :
    Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _) ⊔
        conductorTwoRingOfIntegersIdealOfForm p hp8 Q = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  let O := 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))
  have h2_mem : (2 : O) ∈ Ideal.span ({(2 : O)} : Set _) :=
    Ideal.subset_span (by simp)
  have h2_mem_sup : (2 : O) ∈ Ideal.span ({(2 : O)} : Set _) ⊔
      conductorTwoRingOfIntegersIdealOfForm p hp8 Q :=
    Ideal.mem_sup_left h2_mem
  have ha_mem : ((Q.1.a : ℤ) : O) ∈ conductorTwoRingOfIntegersIdealOfForm p hp8 Q :=
    intCast_a_mem_conductorTwoRingOfIntegersIdealOfForm p hp8 Q
  have ha_mem_sup : ((Q.1.a : ℤ) : O) ∈ Ideal.span ({(2 : O)} : Set _) ⊔
      conductorTwoRingOfIntegersIdealOfForm p hp8 Q :=
    Ideal.mem_sup_right ha_mem
  rcases ha with ⟨k, hk⟩
  have h_one : (1 : O) = ((Q.1.a : ℤ) : O) - (k : O) * (2 : O) := by
    rw [hk]
    rw [Int.cast_add, Int.cast_mul]
    norm_num
    ring
  rw [h_one]
  exact Ideal.sub_mem _ ha_mem_sup (Ideal.mul_mem_left _ (k : O) h2_mem_sup)

/-- If the chosen conductor-`2` form representative has odd leading
coefficient, then its extended ideal maps to `⊤` modulo `(2)`. -/
theorem map_conductorTwoRingOfIntegersIdealOfForm_quotient_span_two_eq_top_of_odd_a
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))))
    (ha : Odd Q.1.a) :
    (conductorTwoRingOfIntegersIdealOfForm p hp8 Q).map
      (Ideal.Quotient.mk
        (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))) = ⊤ := by
  exact (Ideal.Quotient.map_eq_top_iff_sup_eq_top _ _).2
    (span_two_sup_conductorTwoRingOfIntegersIdealOfForm_eq_top_of_odd_a p hp8 Q ha)

/-- The extended ideal of the chosen odd-leading representative maps to `⊤`
modulo `(2)`. -/
theorem map_conductorTwoRingOfIntegersIdealOfForm_quotient_span_two_eq_top_of_formClass
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (C : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) :
    (conductorTwoRingOfIntegersIdealOfForm p hp8
      (conductorTwoFormClassOddRepresentative p C)).map
      (Ideal.Quotient.mk
        (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))) = ⊤ := by
  exact map_conductorTwoRingOfIntegersIdealOfForm_quotient_span_two_eq_top_of_odd_a
    p hp8 (conductorTwoFormClassOddRepresentative p C)
    (conductorTwoFormClassOddRepresentative_odd_a p C)

/-- Every conductor-`2` form has a properly equivalent representative whose
extended maximal-order ideal is coprime to `(2)`. -/
theorem exists_properEquivalent_span_two_sup_conductorTwoRingOfIntegersIdealOfForm_eq_top
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    ∃ R : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))),
      BinaryQuadraticForm.PrimitivePositiveDefiniteForm.ProperEquivalent Q R ∧
        Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _) ⊔
          conductorTwoRingOfIntegersIdealOfForm p hp8 R = ⊤ := by
  rcases BinaryQuadraticForm.exists_properEquivalent_odd_a_of_discriminant_neg_four_mul_natCast
      Q with ⟨R, hQR, hRa⟩
  exact ⟨R, hQR,
    span_two_sup_conductorTwoRingOfIntegersIdealOfForm_eq_top_of_odd_a p hp8 R hRa⟩

/-- Every conductor-`2` form has a properly equivalent representative whose
extended ideal is coprime to `(2)` and whose leading coefficient gives an
explicit unit modulo `(2)`. -/
theorem exists_properEquivalent_prime_to_two_with_leading_coeff_residue_unit
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    ∃ R : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ))),
      BinaryQuadraticForm.PrimitivePositiveDefiniteForm.ProperEquivalent Q R ∧
        Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _) ⊔
          conductorTwoRingOfIntegersIdealOfForm p hp8 R = ⊤ ∧
        ∃ u : (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
            Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))ˣ,
          (u : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
              Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _)) =
            Ideal.Quotient.mk
              (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
              (((R.1.a : ℤ) : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) := by
  rcases BinaryQuadraticForm.exists_properEquivalent_odd_a_of_discriminant_neg_four_mul_natCast
      Q with ⟨R, hQR, hRa⟩
  refine ⟨R, hQR,
    span_two_sup_conductorTwoRingOfIntegersIdealOfForm_eq_top_of_odd_a p hp8 R hRa,
    ?_⟩
  exact ⟨conductorTwoLeadingCoeffResidueUnitOfOddA p R hRa, by simp⟩

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

/-- The maximal-order ideal class of the chosen odd-leading representative is
the canonical ideal-class image of the original form class. -/
theorem conductorTwoRingOfIntegersIdealClassOfForm_oddRepresentative
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (C : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) :
    conductorTwoRingOfIntegersIdealClassOfForm p hp8
        (conductorTwoFormClassOddRepresentative p C) =
      conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 C := by
  calc
    conductorTwoRingOfIntegersIdealClassOfForm p hp8
        (conductorTwoFormClassOddRepresentative p C) =
        conductorTwoRingOfIntegersIdealClassOfFormClass p hp8
          (Quotient.mk (BinaryQuadraticForm.primitivePositiveDefiniteFormSetoid _)
            (conductorTwoFormClassOddRepresentative p C)) := by
          rw [conductorTwoRingOfIntegersIdealClassOfFormClass_mk]
    _ = conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 C := by
          rw [conductorTwoFormClassOddRepresentative_mk_eq]

/-- Equality of the maximal-order ideal classes attached to two conductor-`2`
forms is equivalent to the classical principal-span relation between the two
extended ideals. -/
theorem conductorTwoRingOfIntegersIdealClassOfForm_eq_iff_exists_span_mul
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (Q R : BinaryQuadraticForm.PrimitivePositiveDefiniteForm (-(4 * (p : ℤ)))) :
    conductorTwoRingOfIntegersIdealClassOfForm p hp8 Q =
        conductorTwoRingOfIntegersIdealClassOfForm p hp8 R ↔
      ∃ x y : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)), x ≠ 0 ∧ y ≠ 0 ∧
        Ideal.span ({x} : Set (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) *
            conductorTwoRingOfIntegersIdealOfForm p hp8 Q =
          Ideal.span ({y} : Set (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) *
            conductorTwoRingOfIntegersIdealOfForm p hp8 R := by
  unfold conductorTwoRingOfIntegersIdealClassOfForm
  rw [ClassGroup.mk0_eq_mk0_iff]
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨x, y, hx, hy, by
      simpa [conductorTwoRingOfIntegersNonzeroIdealOfForm] using hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨x, y, hx, hy, by
      simpa [conductorTwoRingOfIntegersNonzeroIdealOfForm] using hxy⟩

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

/-- Quotient-level conductor-`2` finite cover.

This is the most natural Forms-side target for a future Cox/order or
Picard-group construction: a map from primitive positive definite form classes
of order discriminant `-4p` to the field-discriminant form classes of
discriminant `-p`, with fibers of size at most three. -/
structure ConductorTwoFormClassCover (p : ℕ) where
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

/-- Ideal-class-level conductor-`2` finite cover.

This is the order/Picard-shaped version of the remaining upper-bound step:
the canonical maximal-order ideal class obtained by extending conductor-`2`
Cox/order ideals has fibers of size at most three.  The quotient descent for
this canonical map is already proved by
`conductorTwoRingOfIntegersIdealClassOfFormClass`; the remaining input is only
the order/Picard fiber bound. -/
structure ConductorTwoIdealClassCover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) where
  /-- Every maximal-order ideal class has at most three conductor-`2` form-class
  preimages under the canonical extension map. -/
  fiber_card_le_three :
    ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
      Nat.card
        { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
          conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C } ≤ 3

/-- The chosen odd-leading representative of a form class in an ideal-class
fiber still maps to that same ideal class. -/
theorem conductorTwoFormClassOddRepresentative_mem_idealClassFiber
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))))
    (Q : { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
      conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C }) :
    conductorTwoRingOfIntegersIdealClassOfForm p hp8
        (conductorTwoFormClassOddRepresentative p Q.1) = C := by
  rw [conductorTwoRingOfIntegersIdealClassOfForm_oddRepresentative, Q.2]

/-- The residue-unit map on a fiber of the conductor-`2` ideal-class map.

The remaining Cox/Picard kernel step is to prove this map is injective on each
fiber; that injectivity is exactly the missing `fiberEmbedding` field below. -/
noncomputable def conductorTwoIdealClassFiberResidueUnit
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))))
    (Q : { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
      conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C }) :
    (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
      Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))ˣ :=
  conductorTwoFormClassResidueUnit p Q.1

@[simp]
theorem conductorTwoIdealClassFiberResidueUnit_coe
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))))
    (Q : { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
      conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C }) :
    (conductorTwoIdealClassFiberResidueUnit p hp8 C Q :
      𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) ⧸
        Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _)) =
      conductorTwoFormClassResidueUnit p Q.1 :=
  rfl

/-- Two form classes in the same ideal-class fiber have chosen odd-leading
representatives whose extended ideals are class-group equivalent, hence satisfy
the principal-span relation used by `ClassGroup.mk0_eq_mk0_iff`. -/
theorem exists_span_mul_of_mem_conductorTwoIdealClassFiber
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))))
    (Q R : { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
      conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C }) :
    ∃ x y : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)), x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span ({x} : Set (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) *
          conductorTwoRingOfIntegersIdealOfForm p hp8
            (conductorTwoFormClassOddRepresentative p Q.1) =
        Ideal.span ({y} : Set (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) *
          conductorTwoRingOfIntegersIdealOfForm p hp8
            (conductorTwoFormClassOddRepresentative p R.1) := by
  have hQ :=
    conductorTwoFormClassOddRepresentative_mem_idealClassFiber p hp8 C Q
  have hR :=
    conductorTwoFormClassOddRepresentative_mem_idealClassFiber p hp8 C R
  have hclasses :
      conductorTwoRingOfIntegersIdealClassOfForm p hp8
          (conductorTwoFormClassOddRepresentative p Q.1) =
        conductorTwoRingOfIntegersIdealClassOfForm p hp8
          (conductorTwoFormClassOddRepresentative p R.1) := by
    rw [hQ, hR]
  exact (conductorTwoRingOfIntegersIdealClassOfForm_eq_iff_exists_span_mul
    p hp8 (conductorTwoFormClassOddRepresentative p Q.1)
      (conductorTwoFormClassOddRepresentative p R.1)).1 hclasses

/-- Equality of the explicit residue units on a fiber is equality of the chosen
odd leading coefficients modulo `(2)`. -/
theorem quotient_mk_intCast_a_eq_of_conductorTwoIdealClassFiberResidueUnit_eq
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))))
    (Q R : { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
      conductorTwoRingOfIntegersIdealClassOfFormClass p hp8 Q = C })
    (hres :
      conductorTwoIdealClassFiberResidueUnit p hp8 C Q =
        conductorTwoIdealClassFiberResidueUnit p hp8 C R) :
    Ideal.Quotient.mk
        (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
        ((((conductorTwoFormClassOddRepresentative p Q.1).1.a : ℤ) :
          𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) =
      Ideal.Quotient.mk
        (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
        ((((conductorTwoFormClassOddRepresentative p R.1).1.a : ℤ) :
          𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) := by
  let O := 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))
  let I : Ideal O := Ideal.span ({(2 : O)} : Set O)
  have hcoe := congrArg (fun (u : (O ⧸ I)ˣ) => (u : O ⧸ I)) hres
  simpa using hcoe

/-- Representative reconstruction criterion for the conductor-`2` residue-unit map.

This is the remaining local Cox/order input for the fiber-residue injectivity route.  It says
that two conductor-`2` form classes are equal once their chosen odd representatives have the same
extended maximal-order ideal class and the same leading coefficient modulo `(2)`.

In Cox's notation this is the injectivity part hidden behind the prime-to-conductor ideal
comparison and the exact sequence in Theorem 7.24.  The reusable order/Picard version belongs under
`QuadraticNumberFields.QuadraticOrder`; this conductor-`2` coordinate specialization stays here. -/
def ConductorTwoFormClassReconstruction
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) : Prop :=
  let O := 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))
  ∀ Q R : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))),
      conductorTwoRingOfIntegersIdealClassOfForm p hp8
          (conductorTwoFormClassOddRepresentative p Q) =
        conductorTwoRingOfIntegersIdealClassOfForm p hp8
          (conductorTwoFormClassOddRepresentative p R) →
      Ideal.Quotient.mk (Ideal.span ({(2 : O)} : Set O))
          ((((conductorTwoFormClassOddRepresentative p Q).1.a : ℤ) : O)) =
        Ideal.Quotient.mk (Ideal.span ({(2 : O)} : Set O))
          ((((conductorTwoFormClassOddRepresentative p R).1.a : ℤ) : O)) →
      Q = R

/-- A representative-level reconstruction criterion proves injectivity of the
explicit residue-unit map on every ideal-class fiber.

This is the narrow remaining Cox/Picard step: after choosing odd representatives,
same extended ideal class and same leading coefficient modulo `(2)` must force
the original conductor-`2` form classes to be equal. -/
theorem conductorTwoIdealClassFiberResidueUnit_injective_of_formClassReconstruction
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hrec : ConductorTwoFormClassReconstruction p hp8)
    (C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) :
    Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C) := by
  intro Q R hres
  apply Subtype.ext
  apply hrec
  · rw [conductorTwoRingOfIntegersIdealClassOfForm_oddRepresentative,
      conductorTwoRingOfIntegersIdealClassOfForm_oddRepresentative, Q.2, R.2]
  · exact quotient_mk_intCast_a_eq_of_conductorTwoIdealClassFiberResidueUnit_eq
      p hp8 C Q R hres

/-- Picard-exact-sequence-shaped kernel certificate for the conductor-`2` extension map.

The local target is the concrete unit group `(𝓞K / 2𝓞K)ˣ`.  The remaining
order/Picard input is the fiber injection into this local quotient; the inert
branch cardinal bound for the target is proved separately below. -/
structure ConductorTwoIdealClassKernelCertificate
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

/-- Injectivity of the explicit residue-unit map on every ideal-class fiber
constructs the conductor-`2` kernel certificate. -/
noncomputable def conductor_two_ideal_class_kernel_certificate_of_fiberResidueUnit_injective
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3)
    (hinj : ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
      Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C)) :
    ConductorTwoIdealClassKernelCertificate p hp8 where
  fiberEmbedding := fun C =>
    { toFun := conductorTwoIdealClassFiberResidueUnit p hp8 C
      inj' := hinj C }

/-- The representative-level reconstruction criterion constructs the
conductor-`2` kernel certificate. -/
noncomputable def conductor_two_ideal_class_kernel_certificate_of_formClassReconstruction
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hrec : ConductorTwoFormClassReconstruction p hp8) :
    ConductorTwoIdealClassKernelCertificate p hp8 :=
  conductor_two_ideal_class_kernel_certificate_of_fiberResidueUnit_injective p hp8
    (conductorTwoIdealClassFiberResidueUnit_injective_of_formClassReconstruction p hp8 hrec)

/-- Kernel certificate gives the ideal-class fiber bound for the canonical
conductor-`2` extension map. -/
theorem conductor_two_ideal_class_fiber_card_le_three_of_kernel_certificate
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hkernel : ConductorTwoIdealClassKernelCertificate p hp8)
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

/-- Ideal-class-level conductor-`2` cover supplies the quotient-level
form-class cover by transporting maximal-order ideal classes back to
field-discriminant form classes via Cox's equivalence. -/
noncomputable def conductor_two_form_class_cover_of_ideal_class_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hcover : ConductorTwoIdealClassCover p hp8) :
    ConductorTwoFormClassCover p where
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

/-- The canonical conductor-`2` ideal-class extension map supplies the
ideal-class cover once an explicit kernel certificate is available. -/
def conductor_two_ideal_class_cover_of_kernel_certificate
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hkernel : ConductorTwoIdealClassKernelCertificate p hp8) :
    ConductorTwoIdealClassCover p hp8 := by
  exact {
    fiber_card_le_three := fun C =>
      conductor_two_ideal_class_fiber_card_le_three_of_kernel_certificate
        p hp8 hkernel C }

/-- **Conductor-lowering form-class cover, conductor `2`.** In the inert prime
family `d = -p`, conductor-`2` form classes of discriminant `-4p` map to
field-discriminant form classes of discriminant `-p` with fibers of size at most
three, once an explicit ideal-class kernel certificate is available. -/
noncomputable def conductor_two_form_class_cover_of_kernel_certificate
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hkernel : ConductorTwoIdealClassKernelCertificate p hp8) :
    ConductorTwoFormClassCover p :=
  conductor_two_form_class_cover_of_ideal_class_cover p hp hp8
    (conductor_two_ideal_class_cover_of_kernel_certificate p hp8 hkernel)

end Heegner
end QuadraticNumberFields
