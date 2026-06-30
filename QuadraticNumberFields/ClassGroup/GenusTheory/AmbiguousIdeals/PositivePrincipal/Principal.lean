/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.PositivePrincipal.Internal

/-!
# Ordinary-Principal Ramified Parity Relation

The ordinary (wide) principal branch of the positive-principal genus-theory
input: from the product-formula boundary to a principal generator of the full
ramified-parity ideal product.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

/-- Product-formula boundary for the ordinary-principal relation.

There is a principal ambiguous integral ideal whose factorization has a nonzero
ramified parity vector. In the final proof this should be supplied by the
different/`√d` ramified-prime product formula, with the small `d = -1` behavior
handled explicitly rather than by a uniform constant-one shortcut. -/
theorem exists_principal_ambiguousIdeal_with_nonzero_ramifiedParityVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ J : (Ideal R)⁰,
      IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (J : Ideal R) ∧
        (J : Ideal R).IsPrincipal ∧ ∃ p, fullRamifiedParityVector d J p ≠ 0 := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hsqrtd_ne : Splitting.sqrtdInt d ≠ 0 := by
    intro h
    have hcoe : ((Splitting.sqrtdInt d : R) : Qsqrtd (d : ℚ)) = 0 := by
      rw [h]
      simp
    rw [Splitting.coe_sqrtdInt] at hcoe
    have him := congrArg QuadraticAlgebra.im hcoe
    norm_num at him
  let J : (Ideal R)⁰ :=
    ⟨Ideal.span ({Splitting.sqrtdInt d} : Set R), by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
        Ideal.span_singleton_eq_bot]
      exact hsqrtd_ne⟩
  by_cases hJparity : ∃ p, fullRamifiedParityVector d J p ≠ 0
  · refine ⟨J, ?_, ?_, hJparity⟩
    · change
        Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R)
            (Ideal.span ({Splitting.sqrtdInt d} : Set R)) =
          Ideal.span ({Splitting.sqrtdInt d} : Set R)
      rw [Ideal.map_span, Set.image_singleton]
      have hmap :
          conjAutRingOfIntegers (Qsqrtd (d : ℚ)) (Splitting.sqrtdInt d) =
            -Splitting.sqrtdInt d := by
        apply NumberField.RingOfIntegers.ext
        rw [coe_conjAutRingOfIntegers_apply]
        change (Qsqrtd.starAlgEquiv (d : ℚ))
            (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)) =
          (-(QuadraticAlgebra.omega : Qsqrtd (d : ℚ)))
        rw [Qsqrtd.starAlgEquiv_apply]
        simp [QuadraticAlgebra.star_mk, QuadraticAlgebra.omega]
      simp [hmap, Ideal.span_singleton_neg]
    · change (Ideal.span ({Splitting.sqrtdInt d} : Set R)).IsPrincipal
      infer_instance
  · by_cases hdm1 : d = -1
    · subst d
      let h2 : 2 ∈ ramifiedPrimes (-1) := two_mem_ramifiedPrimes_neg_one
      let R := NumberField.RingOfIntegers (Qsqrtd (((-1 : ℤ)) : ℚ))
      let J : (Ideal R)⁰ :=
        ⟨ramifiedPrimeIdeal (-1) h2,
          mem_nonZeroDivisors_iff_ne_zero.mpr (ramifiedPrimeIdeal_ne_bot (-1) h2)⟩
      refine ⟨J, ?_, ?_, ?_⟩
      · change Ideal.map
            (conjAutRingOfIntegers (Qsqrtd (((-1 : ℤ)) : ℚ)) : R →+* R)
            (ramifiedPrimeIdeal (-1) h2) =
          ramifiedPrimeIdeal (-1) h2
        exact map_conjAut_eq_of_mem_primesOver_of_mem_ramifiedPrimes (-1) h2
          (ramifiedPrimeIdeal_mem_primesOver (-1) h2)
      · change (ramifiedPrimeIdeal (-1) h2 : Ideal R).IsPrincipal
        exact ramifiedPrimeIdeal_two_neg_one_isPrincipal
      · exact ⟨⟨2, h2⟩, fullRamifiedParityVector_ramifiedPrimeIdeal_self_ne_zero (-1) h2⟩
    · exact False.elim <| hJparity <| by
        simpa [J, R] using
          exists_nonzero_fullRamifiedParityVector_span_sqrtdInt_of_ne_neg_one d hdm1

/-- A principal ambiguous ideal with nonzero ramified parity gives an
ordinary-principal ramified parity relation. -/
theorem exists_nonzero_ramifiedParity_isPrincipal_of_principal_ambiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJamb : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hJprincipal : (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))).IsPrincipal)
    (hJparity : ∃ p, fullRamifiedParityVector d J p ≠ 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧ (fullRamifiedParityIdealProduct d r : Ideal R).IsPrincipal := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let r := fullRamifiedParityVector d J
  refine ⟨r, hJparity, ?_⟩
  have hnarrow :=
    ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct_of_factorization' d J hJamb
  have hwide := congrArg (NarrowClassGroup.toClassGroup R) hnarrow
  have hJwide : ClassGroup.mk0 J = (1 : ClassGroup R) := by
    exact (ClassGroup.mk0_eq_one_iff J.2).mpr hJprincipal
  have hfullwide :
      ClassGroup.mk0 (fullRamifiedParityIdealProduct d r) = (1 : ClassGroup R) := by
    simpa [R, r, NarrowClassGroup.toClassGroup_mk0] using hwide.symm.trans hJwide
  exact (ClassGroup.mk0_eq_one_iff (fullRamifiedParityIdealProduct d r).2).mp hfullwide

/-- Ordinary-principal ramified parity relation as an integral ideal statement.

This is the product-formula boundary for the wide relation: one must produce a
nonzero, `d`-dependent ramified parity vector whose full ramified parity ideal
product is principal. -/
theorem exists_nonzero_ramifiedParity_isPrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧ (fullRamifiedParityIdealProduct d r : Ideal R).IsPrincipal := by
  classical
  obtain ⟨J, hJamb, hJprincipal, hJparity⟩ :=
    exists_principal_ambiguousIdeal_with_nonzero_ramifiedParityVector d
  exact exists_nonzero_ramifiedParity_isPrincipal_of_principal_ambiguousIdeal
    d J hJamb hJprincipal hJparity

/-- Ordinary-principal ramified parity relation.

There is a nonzero, `d`-dependent ramified parity vector whose full ramified
parity ideal product is principal in the wide ideal-class sense. This is the
first half of the positive-principal input; it does not yet include the narrow sign
condition on the generator. -/
theorem exists_nonzero_ramifiedParity_principal_generator
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          toPrincipalIdeal R (FractionRing R) γ =
            FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  obtain ⟨r, hrnonzero, hprincipal⟩ := exists_nonzero_ramifiedParity_isPrincipal d
  obtain ⟨γ, hγ⟩ :=
    exists_toPrincipalIdeal_eq_mk0_of_isPrincipal
      (I := fullRamifiedParityIdealProduct d r) hprincipal
  exact ⟨r, hrnonzero, γ, hγ⟩

end Internal
end GenusTheory
end ClassGroup
end QuadraticNumberFields
