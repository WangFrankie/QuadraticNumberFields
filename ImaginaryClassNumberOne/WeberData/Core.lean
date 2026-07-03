/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import ImaginaryClassNumberOne.ClassNumberOne
import ImaginaryClassNumberOne.Diophantine

/-!
# Weber Data Interface for the Baker-Heegner-Stark Proof

This file records the class-field-theoretic and Weber-function inputs in the
inert-prime branch of the Baker-Heegner-Stark theorem.  These declarations are
interfaces: they name the deep mathematical facts without attempting to prove
them in the final assembly file.

This core interface is intentionally independent of the reduced-forms backend.
Optional providers, such as the `Forms` route through conductor-`2` reduced-form
class numbers, should live in separate files.

## Main definitions

* `RingClassNumberConductorTwoData`: structured placeholder for the conductor-`2`
  ring-class-number jump.
* `heegnerGammaPrimePairs`: the finite Cox-Heegner table relating inert primes
  to gamma values.
* `IsAssociatedHeegnerGamma`: the table relation between a prime `p` and the
  gamma value obtained from the Weber/CM construction.
* `StarkHeegnerAlgebraicData`: the algebraic data needed by the elementary
  framework layer.
* `InertPrimeWeberDataProvider`: a provider interface for the deep inert-prime
  Weber/CM input from class number one.
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

/-- The finite Cox-Heegner table matching positive inert Heegner primes with
the corresponding Weber gamma values. -/
def heegnerGammaPrimePairs : Finset (ℤ × ℤ) :=
  {((3 : ℤ), 0), (11, -32), (19, -96), (43, -960), (67, -5280), (163, -640320)}

/-- The Weber/CM gamma value `gamma` is associated to the inert prime `p` by
the finite Cox-Heegner gamma-prime table. -/
def IsAssociatedHeegnerGamma (p : ℕ) (gamma : ℤ) : Prop :=
  ((p : ℤ), gamma) ∈ heegnerGammaPrimePairs

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

/-- Provider interface for the deep non-exceptional inert-prime Weber/CM input.

The core file records only the shape of the input.  A reduced-forms route,
quadratic-order/Picard proof, Stark no-Weber argument, or Baker logarithmic
argument may provide this structure in a separate file. -/
structure InertPrimeWeberDataProvider where
  /-- In the non-exceptional inert family `d = -p`, class number one gives the
  Stark-Heegner algebraic data needed by the elementary framework layer. -/
  exists_weber_data :
    ∀ (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)],
      Nat.Prime p →
      p % 8 = 3 →
      p ≠ 3 →
      NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1 →
      Nonempty (StarkHeegnerAlgebraicData p)

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

/-- Refined conductor-`2` Weber data projects to the Stark-Heegner algebraic
data needed by the elementary framework layer. -/
theorem exists_weber_data_of_conductor_two_weber_data
    {p : ℕ} (hweber : HasConductorTwoClassNumberThreeWeberData p) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact Nonempty.map ConductorTwoClassNumberThreeWeberData.starkHeegnerData hweber

/-- Weber/CM existence input from class number one. In the non-exceptional
inert prime family `d = -p`, class number one gives the Stark-Heegner
algebraic data. -/
theorem exists_weber_data_of_classNumber_one_inert_prime
    (hprovider : InertPrimeWeberDataProvider)
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact hprovider.exists_weber_data p hp hp8 hp_ne_three hclass

end Heegner
end QuadraticNumberFields
