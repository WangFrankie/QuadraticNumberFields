/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import ImaginaryClassNumberOne.ClassNumberOne
import ImaginaryClassNumberOne.Diophantine
import ImaginaryClassNumberOne.WeberCM.ConductorTwo.Basic

/-!
# Weber/CM Interface for the Baker-Heegner-Stark Proof

This file records the class-field-theoretic and Weber-function inputs in the
inert-prime branch of the Baker-Heegner-Stark theorem.  These declarations are
interfaces: they name the deep mathematical facts without attempting to prove
them in the final assembly file.

The core `Heegner.WeberCM.Core` interface is intentionally independent of the
reduced-forms backend.  Optional conductor-`2` assembly routes, such as the
`Forms` route through reduced-form class numbers, should live in separate files.

## Main definitions

* `ConductorTwoClassNumberThree`: plain Prop for the conductor-`2`
  class-number-three input.
* `heegnerGammaPrimePairs`: the finite Cox-Heegner table relating inert primes
  to gamma values.
* `IsAssociatedHeegnerGamma`: the table relation between a prime `p` and the
  gamma value obtained from the Weber/CM construction.
* `StarkHeegnerAlgebraicCertificate`: the algebraic certificate needed by the elementary
  framework layer.
* `HasInertPrimeWeberCM`: a named input for the deep inert-prime
  Weber/CM input from class number one.
* `ConductorTwoWeberCertificate`: refined conductor-`2` Weber/CM certificate
  bundling the class-number-three input with the extracted Stark-Heegner certificate.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- The finite Cox-Heegner table matching positive inert Heegner primes with
the corresponding Weber gamma values. -/
def heegnerGammaPrimePairs : Finset (ℤ × ℤ) :=
  {((3 : ℤ), 0), (11, -32), (19, -96), (43, -960), (67, -5280), (163, -640320)}

/-- The Weber/CM gamma value `gamma` is associated to the inert prime `p` by
the finite Cox-Heegner gamma-prime table. -/
def IsAssociatedHeegnerGamma (p : ℕ) (gamma : ℤ) : Prop :=
  ((p : ℤ), gamma) ∈ heegnerGammaPrimePairs

/-- Algebraic certificate extracted from the Weber/CM construction in the inert-prime
Baker-Heegner-Stark core. -/
structure StarkHeegnerAlgebraicCertificate (p : ℕ) where
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

/-- Named input for the deep non-exceptional inert-prime Weber/CM input.

The core file records only the shape of the input.  A reduced-forms route,
quadratic-order/Picard proof, Stark no-Weber argument, or Baker logarithmic
argument may supply this named Prop in a separate file. -/
def HasInertPrimeWeberCM : Prop :=
  ∀ (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)],
    Nat.Prime p →
    p % 8 = 3 →
    p ≠ 3 →
    classNumberQsqrtd (-(p : ℤ)) = 1 →
    Nonempty (StarkHeegnerAlgebraicCertificate p)

/-- Refined conductor-`2`, class-number-three Weber/CM certificate.

This interface is the precise deep input needed after the conductor-`2`
class-number-three step: it records both the quadratic-order input and the
Stark-Heegner algebraic certificate extracted from the Weber construction. -/
structure ConductorTwoWeberCertificate (p : ℕ) where
  /-- The conductor-`2` class-number-three input feeding the Weber/CM construction. -/
  classNumberThree : ConductorTwoClassNumberThree p
  /-- The Stark-Heegner algebraic certificate extracted from the Weber/CM construction. -/
  starkHeegner : StarkHeegnerAlgebraicCertificate p

/-- Refined conductor-`2` Weber certificates project to the Stark-Heegner
algebraic certificate needed by the elementary framework layer. -/
theorem exists_weber_certificate_of_conductor_two_weber_certificate
    {p : ℕ} (hweber : Nonempty (ConductorTwoWeberCertificate p)) :
    Nonempty (StarkHeegnerAlgebraicCertificate p) := by
  exact Nonempty.map ConductorTwoWeberCertificate.starkHeegner hweber

/-- **Weber/CM existence input from class number one.** In the non-exceptional
inert prime family `d = -p`, class number one supplies the Stark-Heegner
algebraic certificate. -/
theorem exists_weber_certificate_of_classNumber_one_inert_prime
    (hweber : HasInertPrimeWeberCM)
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    Nonempty (StarkHeegnerAlgebraicCertificate p) := by
  exact hweber p hp hp8 hp_ne_three hclass

end Heegner
end QuadraticNumberFields
