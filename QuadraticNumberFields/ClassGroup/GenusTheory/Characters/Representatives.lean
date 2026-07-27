/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Raw
import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Discriminant-Coprime Narrow Representatives

This file proves that every narrow ideal class has a nonzero integral
representative whose absolute norm is coprime to the field discriminant.
-/

open scoped NumberField nonZeroDivisors QuadraticNumberFields.ClassGroup

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- The narrow class map restricted to discriminant-coprime integral ideals. -/
noncomputable def narrowMk0OnGenusCoprimeIdeals :
    GenusCoprimeIdeal d →* Cl⁺(d) :=
  NarrowClassGroup.mk0.comp (genusCoprimeIdeals d).subtype

/-- Every narrow ideal class has a discriminant-coprime integral
representative. -/
theorem exists_genusCoprimeIdeal_mk0_eq (C : Cl⁺(d)) :
    ∃ I : GenusCoprimeIdeal d, narrowMk0OnGenusCoprimeIdeals d I = C := by
  let M : ℕ := primeDiscriminantModulus d
  let Mideal : Ideal OK := Ideal.span ({(M : OK)} : Set OK)
  have hM_ne : M ≠ 0 := by
    simpa [M] using primeDiscriminantModulus_ne_zero d
  have hM_cast_ne : (M : OK) ≠ 0 := Nat.cast_ne_zero.mpr hM_ne
  have hMideal_ne : Mideal ≠ ⊥ := by
    dsimp [Mideal]
    exact Ideal.span_singleton_eq_bot.not.mpr hM_cast_ne
  obtain ⟨I, hI, hIcop⟩ :=
    NarrowClassGroup.exists_integralRep_isCoprime C Mideal hMideal_ne
  have hI_ne : (I : Ideal OK) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hcop : Nat.Coprime (Ideal.absNorm (I : Ideal OK)) M :=
    Ideal.absNorm_coprime_of_isCoprime_span_natCast (I : Ideal OK) M hI_ne (by
      simpa [Mideal] using hIcop)
  refine ⟨⟨I, by simpa [genusCoprimeIdeals, M] using hcop⟩, ?_⟩
  simpa [narrowMk0OnGenusCoprimeIdeals] using hI

/-- The restricted narrow class map is surjective. -/
theorem narrowMk0OnGenusCoprimeIdeals_surjective :
    Function.Surjective (narrowMk0OnGenusCoprimeIdeals d) :=
  exists_genusCoprimeIdeal_mk0_eq d

end GenusTheory
end ClassGroup
end QuadraticNumberFields
