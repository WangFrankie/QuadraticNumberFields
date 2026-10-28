/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import QNFMathlib.NumberTheory.ModularForms.ModularPolynomialTwo
import QNFMathlib.NumberTheory.ModularForms.WeberGamma
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.ClassGroup.GenusTheory.GenusTheorem
import QuadraticNumberFields.ClassGroup.GenusTheory.Sieve
import FormClassGroup.Cox.Equivalence
import FormClassGroup.ClassGroup.ClassNumber
import FormClassGroup.Computed
import ImaginaryClassNumberOne.ClassNumberOne
import ImaginaryClassNumberOne.StarkHeegner
import ImaginaryClassNumberOne.Weber.ConductorTwo

/-!
# Core axiom audit

Run `lake env lean scripts/check_core_axioms.lean` after `lake build`.

Check the transitive axioms of representative project results, including both
the ideal-theoretic and reduced-form routes to class numbers, the computed
class-group facade, the conductor-`2` reduced-form count, Weber's cubic and the
level-two modular polynomial, and the
Baker-Heegner-Stark statements under the explicit Weber existence hypothesis.
Only Lean's standard classical axioms are allowed; `sorryAx`,
native-evaluation axioms, and any new axioms fail the audit.
-/

open Lean in
run_cmd do
  let declarations : Array Name := #[
    ``ModularForm.gamma₂_cube,
    ``ModularForm.jInvariant_smul,
    ``ModularForm.mdifferentiable_jInvariant,
    ``ModularForm.weber_cubic_factorization,
    ``ModularForm.jInvariant_eq_weberF,
    ``ModularForm.jInvariant_eq_weberF₁,
    ``ModularForm.jInvariant_eq_weberF₂,
    ``ModularForm.gamma₂_mul_weberF_pow_8,
    ``ModularForm.gamma₂_mul_weberF₁_pow_8,
    ``ModularForm.gamma₂_mul_weberF₂_pow_8,
    ``ModularForm.modularPolynomialTwo_monic,
    ``ModularForm.modularPolynomialTwo_natDegree,
    ``ModularForm.modularPolynomialTwo_jInvariant,
    ``ModularForm.modularPolynomialTwo_jInvariant_half,
    ``ModularForm.modularPolynomialTwo_jInvariant_half_add_one,
    ``exists_squarefree_int_param_of_isQuadraticField,
    ``exists_algEquiv_qsqrtd,
    ``isQuadraticField_iff_exists_squarefree_int_param,
    ``QuadraticNumberFields.RingOfIntegers.ringOfIntegers_classification,
    ``QuadraticNumberFields.RingOfIntegers.discr_formula,
    ``QuadraticNumberFields.ClassGroup.GenusTheory.twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one,
    ``QuadraticNumberFields.ClassGroup.GenusTheory.genusCharacterMap_ker_eq_square,
    ``QuadraticNumberFields.ClassGroup.GenusTheory.classNumber_eq_one_imp_parameter_prime_shape,
    ``QuadraticNumberFields.BinaryQuadraticForm.formClassEquivClassGroup,
    ``QuadraticNumberFields.classNumber_qsqrtd_eq_reducedForms_card,
    ``QuadraticNumberFields.computedClassNumber_eq_classNumber,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg1,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg2,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg3,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg7,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg11,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg19,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg43,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg67,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg163,
    ``QuadraticNumberFields.Heegner.heegner_xy_solutions,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_iff_mem_heegnerSet,
    ``QuadraticNumberFields.BinaryQuadraticForm.card_enumPrimitiveReducedForms_neg_four_mul_eq_three,
    ``QuadraticNumberFields.Heegner.conductor_two_form_class_number_three,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_iff_mem_heegnerSet_of_conductorTwoWeberHypothesis]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{declaration} depends on unexpected axioms: {unexpected.toList}"
  logInfo m!"Core axiom audit passed for {declarations.size} declarations."
