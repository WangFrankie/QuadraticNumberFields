/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.ClassGroupStructure

/-!
# Reduced-Form Multiplication Tables

This file is the second layer of the class-group structure examples.  It keeps
the concrete reduced-form table checks separate from the final transport to the
ideal class group.
-/

set_option linter.style.nativeDecide false

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## Discriminant `-20`: `ℚ(√-5)` -/

/-- Principal reduced form for discriminant `-20`. -/
def f5_id : BinaryQuadraticForm := BinaryQuadraticForm.mk 1 0 5

/-- The non-principal reduced form for discriminant `-20`. -/
def f5_non : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 2 3

example : f5_id.disc = -20 := by native_decide
example : f5_non.disc = -20 := by native_decide
example : f5_id.IsPrimitive := by unfold IsPrimitive; native_decide
example : f5_non.IsPrimitive := by unfold IsPrimitive; native_decide

/-- Order-two relation for the non-principal class over `ℚ(√-5)`. -/
def composeAndReduce5 := @composeAndReduce

example : composeAndReduce5 f5_non f5_non = f5_id := by
  native_decide

/-! ## Discriminant `-23`: `ℚ(√-23)` -/

/-- Principal reduced form for discriminant `-23`. -/
def f23_id : BinaryQuadraticForm := BinaryQuadraticForm.mk 1 1 6

/-- First non-principal reduced form for discriminant `-23`. -/
def f23_a : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 1 3

/-- Second non-principal reduced form for discriminant `-23`. -/
def f23_b : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 (-1) 3

example : f23_id.disc = -23 := by native_decide
example : f23_a.disc = -23 := by native_decide
example : f23_b.disc = -23 := by native_decide

/-- Composition on the reduced forms of discriminant `-23`. -/
def composeAndReduce23 := @composeAndReduce

example : composeAndReduce23 f23_a (composeAndReduce23 f23_a f23_a) = f23_id := by
  native_decide

example : composeAndReduce23 f23_b (composeAndReduce23 f23_b f23_b) = f23_id := by
  native_decide

example : composeAndReduce23 f23_a f23_a = f23_b := by
  native_decide

example : composeAndReduce23 f23_a f23_b = f23_id := by
  native_decide

/-! ## Discriminant `-84`: `ℚ(√-21)` -/

/-- Principal reduced form for discriminant `-84`. -/
def f21_id : BinaryQuadraticForm := BinaryQuadraticForm.mk 1 0 21

/-- First non-principal reduced form for discriminant `-84`. -/
def f21_A : BinaryQuadraticForm := BinaryQuadraticForm.mk 2 2 11

/-- Second non-principal reduced form for discriminant `-84`. -/
def f21_B : BinaryQuadraticForm := BinaryQuadraticForm.mk 3 0 7

/-- Third non-principal reduced form for discriminant `-84`. -/
def f21_C : BinaryQuadraticForm := BinaryQuadraticForm.mk 5 4 5

/-- Composition on the reduced forms of discriminant `-84`. -/
def composeAndReduce21 := @composeAndReduce

example : composeAndReduce21 f21_A f21_A = f21_id := by native_decide
example : composeAndReduce21 f21_B f21_B = f21_id := by native_decide
example : composeAndReduce21 f21_C f21_C = f21_id := by native_decide
example : composeAndReduce21 f21_A f21_B = f21_C := by native_decide
example : composeAndReduce21 f21_A f21_C = f21_B := by native_decide
example : composeAndReduce21 f21_B f21_C = f21_A := by native_decide
example : composeAndReduce21 f21_id f21_A = f21_A := by native_decide
example : composeAndReduce21 f21_id f21_B = f21_B := by native_decide
example : composeAndReduce21 f21_id f21_C = f21_C := by native_decide
example : composeAndReduce21 f21_id f21_id = f21_id := by native_decide

end BinaryQuadraticForm
end QuadraticNumberFields
