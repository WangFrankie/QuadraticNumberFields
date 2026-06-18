/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Forms.ClassGroup.ClassNumber
import QuadraticNumberFields.Heegner.ClassNumberOne
import QuadraticNumberFields.Heegner.Diophantine

/-!
# Weber Data Interface for the Baker-Heegner-Stark Proof

This file records the class-field-theoretic and Weber-function inputs in the
inert-prime branch of the Baker-Heegner-Stark theorem.  These declarations are
interfaces: they name the deep mathematical facts without attempting to prove
them in the final assembly file.

## Main definitions

* `RingClassNumberConductorTwoData`: structured placeholder for the conductor-`2`
  ring-class-number jump.
* `ConductorTwoFormClassNumberThreeData`: Forms-side class-number-three input for
  primitive reduced forms of discriminant `-4p` in the `p ≠ 3` inert branch.
* `heegnerGammaPrimePairs`: the finite Cox-Heegner table relating inert primes
  to gamma values.
* `IsAssociatedHeegnerGamma`: the table relation between a prime `p` and the
  gamma value obtained from the Weber/CM construction.
* `StarkHeegnerAlgebraicData`: the algebraic data needed by the elementary
  framework layer.
* `ConductorTwoClassNumberThreeWeberData`: refined conductor-`2` Weber/CM data
  bundling the ring-class-number input with the extracted Stark-Heegner data.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- Structured conductor-`2` ring-class-number data in the Cox-Heegner route.

This is intentionally a small interface rather than a real theory of quadratic
orders.  The future replacement should identify `orderClassNumber` with the
class number of the quadratic order of conductor `2` and discriminant `-4p`. -/
structure RingClassNumberConductorTwoData (p : ℕ) where
  /-- The conductor of the quadratic order. -/
  conductor : ℕ
  /-- This framework layer is specifically about conductor `2`. -/
  conductor_eq_two : conductor = 2
  /-- The discriminant of the conductor-`2` order in `ℚ(√-p)`. -/
  discriminant : ℤ
  /-- The discriminant is `-4p`. -/
  discriminant_eq : discriminant = -(4 * (p : ℤ))
  /-- The ring class number of this quadratic order. -/
  orderClassNumber : ℕ
  /-- Cox's class-number jump gives ring class number `3`. -/
  orderClassNumber_eq_three : orderClassNumber = 3

/-- The conductor-`2` ring-class-number input used by the Weber/CM layer. -/
def HasRingClassNumberThreeAtConductorTwo (p : ℕ) : Prop :=
  Nonempty (RingClassNumberConductorTwoData p)

/-- Forms-side class-number-three data for the conductor-`2` discriminant `-4p`.

This is the Cox/reduced-forms route into the conductor-`2` ring-class-number
input. It deliberately records only the computable primitive reduced form count,
leaving the still-missing Cox order class-number formula as the named bridge. -/
structure ConductorTwoFormClassNumberThreeData (p : ℕ) where
  /-- The discriminant whose primitive positive definite form classes are counted. -/
  discriminant : ℤ
  /-- The conductor-`2` discriminant is `-4p`. -/
  discriminant_eq_neg_four_mul : discriminant = -(4 * (p : ℤ))
  /-- The Forms-side class number, counted by primitive reduced forms. -/
  reducedFormClassNumber : ℕ
  /-- The Forms-side class number is the cardinality of the reduced-form enumeration. -/
  reducedFormClassNumber_eq_card :
    reducedFormClassNumber =
      (BinaryQuadraticForm.enumPrimitiveReducedForms discriminant).card
  /-- Cox's conductor-`2` class-number jump gives Forms-side class number `3`. -/
  reducedFormClassNumber_eq_three : reducedFormClassNumber = 3

/-- There is Forms-side class-number-three data for the conductor-`2`
discriminant `-4p`. -/
def HasConductorTwoFormClassNumberThreeData (p : ℕ) : Prop :=
  Nonempty (ConductorTwoFormClassNumberThreeData p)

/-- A concrete reduced-form cardinality computation supplies the Forms-side
conductor-`2` class-number-three data. -/
theorem hasConductorTwoFormClassNumberThreeData_of_reducedForms_card
    (p : ℕ)
    (hcard :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3) :
    HasConductorTwoFormClassNumberThreeData p := by
  exact ⟨{
    discriminant := -(4 * (p : ℤ))
    discriminant_eq_neg_four_mul := rfl
    reducedFormClassNumber :=
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card
    reducedFormClassNumber_eq_card := rfl
    reducedFormClassNumber_eq_three := hcard }⟩

/-- Forms-side class-number-three data supplies the conductor-`2`
ring-class-number input used by the Weber/CM layer. -/
theorem hasRingClassNumberThreeAtConductorTwo_of_forms
    {p : ℕ} (hforms : HasConductorTwoFormClassNumberThreeData p) :
    HasRingClassNumberThreeAtConductorTwo p := by
  rcases hforms with ⟨hforms⟩
  exact ⟨{
    conductor := 2
    conductor_eq_two := rfl
    discriminant := hforms.discriminant
    discriminant_eq := hforms.discriminant_eq_neg_four_mul
    orderClassNumber := hforms.reducedFormClassNumber
    orderClassNumber_eq_three := hforms.reducedFormClassNumber_eq_three }⟩

/-- **Cox forms class-number input.** In the inert prime family `d = -p`, class
number one for `ℚ(√-p)` gives Forms-side class-number-three data for primitive
positive definite forms of conductor-`2` discriminant `-4p`, away from the
unit-exception case `p = 3`. -/
theorem conductor_two_form_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    HasConductorTwoFormClassNumberThreeData p := by
  -- Alternative routes for this bridge:
  -- * prove Cox's order class-number formula via Picard groups of quadratic orders;
  -- * build the conductor-`2` Picard group directly and avoid reduced-form enumeration;
  -- * follow Stark's no-Weber variant, replacing this downstream input entirely.
  sorry

/-- The finite Cox-Heegner table matching positive inert Heegner primes with
the corresponding Weber gamma values. -/
def heegnerGammaPrimePairs : Finset (ℤ × ℤ) :=
  {((3 : ℤ), 0), (11, -32), (19, -96), (43, -960), (67, -5280), (163, -640320)}

/-- The Weber/CM gamma value `gamma` is associated to the inert prime `p` by
the finite Cox-Heegner gamma-prime table. -/
def IsAssociatedHeegnerGamma (p : ℕ) (gamma : ℤ) : Prop :=
  ((p : ℤ), gamma) ∈ heegnerGammaPrimePairs

/-- **Conductor-two ring-class-number input.** In the inert prime family
`d = -p`, class number one for `ℚ(√-p)` gives the conductor-`2` ring class
number datum used by Cox's proof, away from the `p = 3` unit exception. -/
theorem conductor_two_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    HasRingClassNumberThreeAtConductorTwo p := by
  exact hasRingClassNumberThreeAtConductorTwo_of_forms
    (conductor_two_form_class_number_three p hp hp8 hp_ne_three hclass)

/-- Algebraic data extracted from the Weber/CM construction in the inert-prime
Baker-Heegner-Stark core. -/
structure StarkHeegnerAlgebraicData (p : ℕ) where
  /-- The `X` coordinate of the integral point on `Y ^ 2 = 2 * X * (X ^ 3 + 1)`. -/
  X : ℤ
  /-- The `Y` coordinate of the integral point on `Y ^ 2 = 2 * X * (X ^ 3 + 1)`. -/
  Y : ℤ
  /-- The gamma value attached to the Weber/CM construction. -/
  gamma : ℤ
  /-- The extracted integer point satisfies the Heegner equation. -/
  xyEquation : HeegnerXYEquation X Y
  /-- The extracted gamma value is computed from the integer point. -/
  gamma_eq : gamma = heegnerGammaValue X Y
  /-- The gamma value is associated to the prime `p` by the Weber/CM construction. -/
  associatedGamma : IsAssociatedHeegnerGamma p gamma

/-- Refined conductor-`2`, ring-class-number-three Weber/CM data.

This interface is the precise deep input needed after the conductor-`2`
ring-class-number jump: it records both the quadratic-order datum and the
Stark-Heegner algebraic data extracted from the Weber construction. -/
structure ConductorTwoClassNumberThreeWeberData (p : ℕ) where
  /-- The conductor-`2` ring-class-number datum feeding the Weber/CM construction. -/
  ringClassNumberData : RingClassNumberConductorTwoData p
  /-- The Stark-Heegner algebraic data extracted from the Weber/CM construction. -/
  starkHeegnerData : StarkHeegnerAlgebraicData p

/-- There is refined conductor-`2`, ring-class-number-three Weber/CM data. -/
def HasConductorTwoClassNumberThreeWeberData (p : ℕ) : Prop :=
  Nonempty (ConductorTwoClassNumberThreeWeberData p)

/-- **Deep Weber/CM input from ring-class-number three.** The conductor-`2`
ring-class-number-three datum supplies the refined Weber data: a concrete
Heegner equation solution, the associated gamma value, and its finite-table
association with `p`, in the non-exceptional inert branch `p ≠ 3`. -/
theorem conductor_two_weber_data_of_ring_class_number_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3) (horder : HasRingClassNumberThreeAtConductorTwo p) :
    HasConductorTwoClassNumberThreeWeberData p := by
  sorry

/-- Refined conductor-`2` Weber data projects to the Stark-Heegner algebraic
data needed by the elementary framework layer. -/
theorem exists_weber_data_of_conductor_two_weber_data
    {p : ℕ} (hweber : HasConductorTwoClassNumberThreeWeberData p) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact Nonempty.map ConductorTwoClassNumberThreeWeberData.starkHeegnerData hweber

/-- **Weber/CM existence input from conductor-two data.** The conductor-`2`
ring-class-number datum yields the algebraic point and gamma value used in the
inert-prime core. -/
theorem exists_weber_data_of_conductor_two_class_number_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3)
    (horder : HasRingClassNumberThreeAtConductorTwo p) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact exists_weber_data_of_conductor_two_weber_data
    (conductor_two_weber_data_of_ring_class_number_three p hp hp8 hp_ne_three horder)

/-- **Weber/CM existence input from class number one.** In the non-exceptional
inert prime family `d = -p`, class number one supplies the Stark-Heegner
algebraic data. -/
theorem exists_weber_data_of_classNumber_one_inert_prime
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact exists_weber_data_of_conductor_two_class_number_three p hp hp8 hp_ne_three
    (conductor_two_class_number_three p hp hp8 hp_ne_three hclass)

end Heegner
end QuadraticNumberFields
