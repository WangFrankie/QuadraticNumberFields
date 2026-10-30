/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.RingOfIntegers
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Conductor
import QuadraticNumberFields.ClassGroup.GenusTheory.GenusTheorem
import QuadraticNumberFields.ClassGroup.GenusTheory.Sieve
import FormClassGroup.Cox.Equivalence
import FormClassGroup.ClassGroup.ClassNumber

/-!
# Core axiom audit

Run `lake env lean scripts/check_core_axioms.lean` after `lake build`.

Check the transitive axioms of representative project results, including both
the ideal-theoretic and reduced-form routes to class numbers. Precise imports
keep this audit separate from the unfinished computed-class-group interface.
Only Lean's standard classical axioms are allowed;
`sorryAx`, native-evaluation axioms, and any new axioms fail the audit.
-/

open Lean in
run_cmd do
  let declarations : Array Name := #[
    ``QuadraticAlgebra.mem_adjoin_singleton_iff_dvd_im,
    ``QuadraticAlgebra.conductor_eq_span_im,
    ``QuadraticAlgebra.range_algHom_eq_adjoin,
    ``QuadraticAlgebra.mem_range_algHom_iff_dvd_im,
    ``QuadraticAlgebra.index_range_algHom,
    ``QuadraticAlgebra.isQuadraticOrder_map_adjoin_iff,
    ``QuadraticAlgebra.isQuadraticOrder_map_range_iff,
    ``QuadraticAlgebra.isQuadraticOrder_map_range_iff_index_ne_zero,
    ``QuadraticAlgebra.isQuadraticOrder_range_toRat,
    ``NumberField.isOrder_integralClosure,
    ``ZOnePlusSqrtdOverTwo.fromZsqrtd,
    ``ZOnePlusSqrtdOverTwo.fromZsqrtd_apply,
    ``ZOnePlusSqrtdOverTwo.fromZsqrtd_re,
    ``ZOnePlusSqrtdOverTwo.fromZsqrtd_im,
    ``ZOnePlusSqrtdOverTwo.fromZsqrtd_sqrtd,
    ``ZOnePlusSqrtdOverTwo.fromZsqrtd_injective,
    ``ZOnePlusSqrtdOverTwo.mem_range_fromZsqrtd_iff,
    ``ZOnePlusSqrtdOverTwo.range_fromZsqrtd,
    ``ZOnePlusSqrtdOverTwo.index_range_fromZsqrtd,
    ``ZOnePlusSqrtdOverTwo.mem_conductor_iff_even_coordinates,
    ``ZOnePlusSqrtdOverTwo.conductor_eq_span_two,
    ``ZOnePlusSqrtdOverTwo.isQuadraticOrder_range_fromZsqrtd,
    ``QuadraticField.isQuadraticOrder_integralClosure,
    ``exists_squarefree_int_param_of_isQuadraticField,
    ``exists_algEquiv_qsqrtd,
    ``isQuadraticField_iff_exists_squarefree_int_param,
    ``QuadraticNumberFields.RingOfIntegers.ringOfIntegers_classification,
    ``QuadraticNumberFields.RingOfIntegers.discr_formula,
    ``QuadraticNumberFields.ClassGroup.GenusTheory.twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one,
    ``QuadraticNumberFields.ClassGroup.GenusTheory.genusCharacterMap_ker_eq_square,
    ``QuadraticNumberFields.ClassGroup.GenusTheory.classNumber_eq_one_imp_parameter_prime_shape,
    ``QuadraticNumberFields.BinaryQuadraticForm.formClassEquivClassGroup,
    ``QuadraticNumberFields.classNumber_qsqrtd_eq_reducedForms_card]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{declaration} depends on unexpected axioms: {unexpected.toList}"
  logInfo m!"Core axiom audit passed for {declarations.size} declarations."
