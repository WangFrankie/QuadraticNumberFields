/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.PositivePrincipal.Internal

/-!
# Imaginary Positive-Principal Ramified Parity Relation

The imaginary quadratic branch: total positivity is vacuous (there are no real
embeddings), so an ordinary-principal ramified parity relation is automatically
narrow-principal.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

/-- In the imaginary quadratic case, an ordinary-principal ramified parity
relation is automatically narrow-principal because total positivity is vacuous.

This is only the imaginary branch of the unified genus-theory input. In real
quadratic fields the sign/unit correction is a genuine extra argument, so this
lemma is not used as a uniform replacement for
`exists_nonzero_ramifiedParity_tp_generator`. -/
theorem exists_nonzero_ramifiedParity_tp_generator_of_imaginary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hprincipal :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
        (∃ p, r p ≠ 0) ∧
          ∃ γ : (FractionRing R)ˣ,
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r)) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  letI : IsEmpty (FractionRing R →+* ℝ) := by
    simpa [R] using Qsqrtd.Imaginary.isEmpty_fractionRing_realEmbeddings d hd
  obtain ⟨r, hrnonzero, γ, hγ⟩ := hprincipal
  exact ⟨r, hrnonzero, γ, NarrowClassGroup.isTotallyPositive_of_isEmpty
    (γ : FractionRing R), hγ⟩

end Internal
end GenusTheory
end ClassGroup
end QuadraticNumberFields
