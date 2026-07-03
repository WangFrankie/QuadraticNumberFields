/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.Basic

/-!
# Galois Number Fields

Material destined for mathlib.

This file contains small bridges between Galois extensions of number fields and
the corresponding extensions of their rings of integers' fraction fields.
-/

open scoped NumberField

namespace NumberField

attribute [local instance] FractionRing.liftAlgebra

/-- If `K/ℚ` is Galois, then the fraction-field extension
`FractionRing (𝓞 K) / FractionRing ℤ` is Galois. This is usually installed with
`haveI` before using relative-ideal-norm lemmas such as
`Ideal.relNorm_eq_pow_of_isPrime_isGalois`. -/
theorem isGalois_fractionRing_ringOfIntegers
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K] :
    IsGalois (FractionRing ℤ) (FractionRing (𝓞 K)) := by
  refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv ℤ ℚ).toRingEquiv.symm)
    (g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm) <|
      RingHom.ext fun _ ↦ IsFractionRing.algEquiv_commutes
        (FractionRing.algEquiv ℤ ℚ).symm (FractionRing.algEquiv (𝓞 K) K).symm _

end NumberField
