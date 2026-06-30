/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.ClassGroup.Narrow
import QuadraticNumberFields.ClassGroup.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex

/-!
# Narrow Class Groups of Quadratic Fields

This file specializes the generic `NarrowClassGroup` API to the standard
quadratic fields `Qsqrtd d`.
-/

open scoped NumberField nonZeroDivisors

namespace QuadraticNumberFields

/-- Scoped notation for the narrow ideal class group `Cl⁺(𝓞(ℚ(√d)))`. -/
scoped[QuadraticNumberFields.ClassGroup]
  notation "Cl⁺(" d ")" => NarrowClassGroup
    (NumberField.RingOfIntegers
      (Qsqrtd ((d : ℤ) : ℚ)))

namespace Qsqrtd

open _root_.Qsqrtd

open scoped QuadraticNumberFields.ClassGroup

section NarrowClassGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞 (Qsqrtd (d : ℚ))

/-- The narrow class number of `ℚ(√d)`. -/
noncomputable def narrowClassNumber : ℕ :=
  NarrowClassGroup.classNumber OK

/-- The natural map from the narrow class group of `𝓞(ℚ(√d))` to the ordinary
wide ideal class group. -/
noncomputable abbrev narrowToClassGroup :
    Cl⁺(d) →* Cl(d) :=
  NarrowClassGroup.toClassGroup OK

/-- The natural map from the narrow class group to the ordinary wide ideal class
group is surjective. -/
theorem narrowToClassGroup_surjective :
    Function.Surjective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_surjective OK

/-- If every unit of the fraction field of `𝓞(ℚ(√d))` is totally positive, then
the narrow class group and ordinary wide class group are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup_of_forall_isTotallyPositive
    (hpos : ∀ x : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing OK)) :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  NarrowClassGroup.nonempty_mulEquivClassGroup_of_forall_isTotallyPositive OK hpos

/-- If every unit of the fraction field of `𝓞(ℚ(√d))` is totally positive, then
the natural map from the narrow class group to the ordinary wide class group is
bijective. -/
theorem narrowToClassGroup_bijective_of_forall_isTotallyPositive
    (hpos : ∀ x : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing OK)) :
    Function.Bijective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_bijective_of_forall_isTotallyPositive OK hpos

namespace Imaginary

/-- If `d < 0`, then the fraction field of `𝓞(ℚ(√d))` has no real embeddings. -/
theorem isEmpty_fractionRing_realEmbeddings (hd : d < 0) :
    IsEmpty (FractionRing OK →+* ℝ) := by
  refine ⟨fun σ => ?_⟩
  letI : Algebra ℚ (Qsqrtd (d : ℚ)) := DivisionRing.toRatAlgebra
  haveI : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) :=
    { finrank_eq_two' := finrank_ratAlgebra_eq_two ((d : ℤ) : ℚ) }
  haveI : QuadraticField (Qsqrtd (d : ℚ)) :=
    { isQuadratic := inferInstance }
  haveI : NumberField (Qsqrtd (d : ℚ)) :=
    QuadraticField.instNumberField (Qsqrtd (d : ℚ))
  haveI : IsFractionRing OK (Qsqrtd (d : ℚ)) := inferInstance
  let e := IsLocalization.algEquiv OK⁰ (FractionRing OK) (Qsqrtd (d : ℚ))
  let φ : Qsqrtd (d : ℚ) →+* ℂ := Complex.ofRealHom.comp (σ.comp e.symm.toRingHom)
  haveI := isTotallyComplex d hd
  exact (NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ) (by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp [φ, NumberField.ComplexEmbedding.conjugate_coe_eq])

/-- In the imaginary quadratic case, the narrow and ordinary principal fractional
ideal subgroups coincide. -/
theorem narrowPrincipalIdeals_eq_principalIdeals (hd : d < 0) :
    NarrowClassGroup.narrowPrincipalIdeals OK (FractionRing OK) =
      (toPrincipalIdeal OK (FractionRing OK)).range := by
  letI := isEmpty_fractionRing_realEmbeddings d hd
  exact NarrowClassGroup.narrowPrincipalIdeals_eq_principalIdeals_of_isEmpty

/-- In the imaginary quadratic case, the narrow class group is naturally isomorphic
to the ordinary wide ideal class group. -/
noncomputable def narrowMulEquivClassGroup (hd : d < 0) :
    Cl⁺(d) ≃* Cl(d) := by
  letI := isEmpty_fractionRing_realEmbeddings d hd
  exact NarrowClassGroup.mulEquivClassGroupOfIsEmpty OK

/-- In the imaginary quadratic case, the narrow class group and ordinary wide ideal
class group are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup (hd : d < 0) :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  ⟨narrowMulEquivClassGroup d hd⟩

/-- In the imaginary quadratic case, the natural map from the narrow class group to
the ordinary wide class group is bijective. -/
theorem narrowToClassGroup_bijective (hd : d < 0) :
    Function.Bijective (narrowToClassGroup d) := by
  letI := isEmpty_fractionRing_realEmbeddings d hd
  exact NarrowClassGroup.toClassGroup_bijective_of_isEmpty OK

end Imaginary

/-- If the fraction field of `𝓞(ℚ(√d))` has no real embeddings, then the narrow
class group and ordinary wide class group are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup_of_isEmpty
    [IsEmpty (FractionRing OK →+* ℝ)] :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  NarrowClassGroup.nonempty_mulEquivClassGroup_of_isEmpty OK

/-- If the fraction field of `𝓞(ℚ(√d))` has no real embeddings, then the natural
map from the narrow class group to the ordinary wide class group is bijective. -/
theorem narrowToClassGroup_bijective_of_isEmpty
    [IsEmpty (FractionRing OK →+* ℝ)] :
    Function.Bijective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_bijective_of_isEmpty OK

end NarrowClassGroup

end Qsqrtd

end QuadraticNumberFields
