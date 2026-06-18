/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Heegner.ClassNumberOne
import QuadraticNumberFields.Heegner.Diophantine

/-!
# Weber Data Interface for the Baker-Heegner-Stark Proof

This file records the class-field-theoretic and Weber-function inputs in the
inert-prime branch of the Baker-Heegner-Stark theorem.  These declarations are
interfaces: they name the deep mathematical facts without attempting to prove
them in the final assembly file.

## Main definitions

* `HasRingClassNumberThreeAtConductorTwo`: placeholder for the conductor-`2`
  ring-class-number jump.
* `IsAssociatedHeegnerGamma`: placeholder relating a prime `p` to the gamma
  value obtained from the Weber/CM construction.
* `StarkHeegnerAlgebraicData`: the algebraic data needed by the elementary
  framework layer.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- Placeholder for the order-class-number statement
`h(-p) = 1 -> h(-4p) = 3` in the Cox-Heegner route. -/
def HasRingClassNumberThreeAtConductorTwo (p : ℕ) : Prop :=
  p = p

/-- Placeholder saying that `gamma` is the gamma value associated to the
inert prime `p` by the Weber/CM construction. -/
def IsAssociatedHeegnerGamma (p : ℕ) (gamma : ℤ) : Prop :=
  (p : ℤ) = (p : ℤ) ∧ gamma = gamma

/-- **Conductor-two ring-class-number input.** In the inert prime family
`d = -p`, class number one for `ℚ(√-p)` gives the conductor-`2` ring class
number datum used by Cox's proof. -/
theorem conductor_two_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    HasRingClassNumberThreeAtConductorTwo p := by
  sorry

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

/-- **Weber/CM existence input from conductor-two data.** The conductor-`2`
ring-class-number datum yields the algebraic point and gamma value used in the
inert-prime core. -/
theorem exists_weber_data_of_conductor_two_class_number_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (horder : HasRingClassNumberThreeAtConductorTwo p) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  sorry

/-- **Weber/CM existence input from class number one.** In the inert prime family
`d = -p`, class number one supplies the Stark-Heegner algebraic data. -/
theorem exists_weber_data_of_classNumber_one_inert_prime
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact exists_weber_data_of_conductor_two_class_number_three p hp hp8
    (conductor_two_class_number_three p hp hp8 hclass)

end Heegner
end QuadraticNumberFields
