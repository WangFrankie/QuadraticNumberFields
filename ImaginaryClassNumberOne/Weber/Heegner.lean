/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import ImaginaryClassNumberOne.ClassNumberOne
import ImaginaryClassNumberOne.Diophantine

/-!
# Weber's Hypothesis and Heegner's Integral Points

This file defines the integral points and gamma values occurring in Heegner's
argument. `InertPrimeWeberHypothesis` states that class number one implies the
existence of such a point in the non-exceptional inert prime case. It is an
explicit mathematical hypothesis, not a theorem proved in this file.

The relation with reduced binary quadratic forms of conductor `2` is studied
separately in `ImaginaryClassNumberOne.Weber.ConductorTwo`.

## Main definitions

* `ConductorTwoClassNumberParameters`: numerical parameters for conductor `2`
  and class number `3`, without an identification with an actual quadratic order.
* `heegnerGammaPrimePairs`: the finite Cox-Heegner table relating inert primes
  to gamma values.
* `IsAssociatedHeegnerGamma`: the table relation between a prime `p` and the
  gamma value obtained from the Weber/CM construction.
* `HeegnerIntegralPoint`: an integral point on Heegner's curve together with its
  associated gamma value.
* `InertPrimeWeberHypothesis`: existence of a Heegner integral point under the
  class-number-one hypothesis.
* `ConductorTwoHeegnerIntegralPoint`: a Heegner integral point together with
  the conductor-`2` numerical parameters.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- Numerical parameters for conductor `2`, discriminant `-4p`, and class number `3`.

The identification of `orderClassNumber` with the class number of the quadratic
order is not part of this definition. This structure is inhabited for every `p`;
its existence alone cannot serve as a hypothesis for Weber's argument. -/
structure ConductorTwoClassNumberParameters (p : ℕ) where
  /-- The conductor of the quadratic order. -/
  conductor : ℕ
  /-- The conductor equals `2`. -/
  conductor_eq_two : conductor = 2
  /-- The discriminant of the conductor-`2` order in `ℚ(√-p)`. -/
  discriminant : ℤ
  /-- The discriminant is `-4p`. -/
  discriminant_eq : discriminant = -(4 * (p : ℤ))
  /-- The proposed class number, still to be identified with that of the order. -/
  orderClassNumber : ℕ
  /-- Cox's class-number jump gives ring class number `3`. -/
  orderClassNumber_eq_three : orderClassNumber = 3

attribute [nolint simpNF] ConductorTwoClassNumberParameters.mk.injEq

/-- Existence of the conductor-`2` numerical parameters. -/
def HasConductorTwoClassNumberParameters (p : ℕ) : Prop :=
  Nonempty (ConductorTwoClassNumberParameters p)

/-- The finite Cox-Heegner table matching positive inert Heegner primes with
the corresponding Weber gamma values. -/
def heegnerGammaPrimePairs : Finset (ℤ × ℤ) :=
  {((3 : ℤ), 0), (11, -32), (19, -96), (43, -960), (67, -5280), (163, -640320)}

/-- The Weber/CM gamma value `gamma` is associated to the inert prime `p` by
the finite Cox-Heegner gamma-prime table. -/
def IsAssociatedHeegnerGamma (p : ℕ) (gamma : ℤ) : Prop :=
  ((p : ℤ), gamma) ∈ heegnerGammaPrimePairs

/-- An integral point on Heegner's curve with a gamma value associated to `p`. -/
structure HeegnerIntegralPoint (p : ℕ) where
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

/-- Weber's existence hypothesis for inert primes: if `p ≡ 3 (mod 8)`, `p ≠ 3`,
and `ℚ(√-p)` has class number one, there is an associated Heegner integral point.
This proposition remains a hypothesis of the conditional classification theorem. -/
def InertPrimeWeberHypothesis : Prop :=
  ∀ (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)],
    Nat.Prime p →
    p % 8 = 3 →
    p ≠ 3 →
    NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1 →
    Nonempty (HeegnerIntegralPoint p)

/-- A Heegner integral point with conductor-`2` numerical parameters. -/
structure ConductorTwoHeegnerIntegralPoint (p : ℕ) where
  /-- The conductor-`2` numerical parameters. -/
  orderParameters : ConductorTwoClassNumberParameters p
  /-- The associated Heegner integral point. -/
  integralPoint : HeegnerIntegralPoint p

/-- Existence of a Heegner integral point with conductor-`2` parameters. -/
def HasConductorTwoHeegnerIntegralPoint (p : ℕ) : Prop :=
  Nonempty (ConductorTwoHeegnerIntegralPoint p)

/-- Forgetting the conductor parameters gives a Heegner integral point. -/
theorem nonempty_heegnerIntegralPoint_of_conductorTwo
    {p : ℕ} (hweber : HasConductorTwoHeegnerIntegralPoint p) :
    Nonempty (HeegnerIntegralPoint p) := by
  exact Nonempty.map ConductorTwoHeegnerIntegralPoint.integralPoint hweber

/-- Apply Weber's existence hypothesis to an inert prime of class number one. -/
theorem nonempty_heegnerIntegralPoint_of_classNumber_eq_one
    (hweber : InertPrimeWeberHypothesis)
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1) :
    Nonempty (HeegnerIntegralPoint p) := by
  exact hweber p hp hp8 hp_ne_three hclass

end Heegner
end QuadraticNumberFields
