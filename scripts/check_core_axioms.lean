/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.ClassGroup.GenusTheory.GenusTheorem
import QuadraticNumberFields.ClassGroup.GenusTheory.Sieve
import FormClassGroup.Cox.Equivalence
import FormClassGroup.ClassGroup.ClassNumber
import ImaginaryClassNumberOne.ClassNumberOne

/-!
# Core axiom audit

Run `lake env lean scripts/check_core_axioms.lean` after `lake build`.

Check the transitive axioms of representative project results, including both
the ideal-theoretic and reduced-form routes to class numbers. Precise imports
keep this audit separate from the unfinished computed-class-group and Weber
provider interfaces. Only Lean's standard classical axioms are allowed;
`sorryAx`, native-evaluation axioms, and any new axioms fail the audit.
-/

open Lean in
run_cmd do
  let declarations : Array Name := #[
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
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg1,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg2,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg3,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg7,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg11,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg19,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg43,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg67,
    ``QuadraticNumberFields.Heegner.classNumber_eq_one_neg163]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{declaration} depends on unexpected axioms: {unexpected.toList}"
  logInfo m!"Core axiom audit passed for {declarations.size} declarations."
