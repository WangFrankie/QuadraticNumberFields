/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Descent
import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.SignVector
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker

/-!
# The Genus Character Map

This file proves the product-one relation among the descended local genus
characters and assembles them into the genus character map.
-/

open scoped NumberField nonZeroDivisors QuadraticNumberFields.ClassGroup

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

private theorem kroneckerSymNat_discr_absNorm_eq_one
    (I : GenusCoprimeIdeal d) :
    kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ)))
      (Ideal.absNorm (I.1.1 : Ideal OK)) = 1 := by
  have hI_ne : (I.1.1 : Ideal OK) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.1.2
  apply
    Splitting.kroneckerSymNat_discr_absNorm_eq_one_of_forall_prime_dvd_not_isRamifiedIn
      d hI_ne
  intro p hp hp_norm hram
  have hp_ram : p ∈ ramifiedPrimes d :=
    (mem_ramifiedPrimes_iff_isRamifiedIn d p).mpr ⟨hp, hram⟩
  have hp_modulus : p ∣ primeDiscriminantModulus d := by
    rw [primeDiscriminantModulus_eq_discr_natAbs]
    exact Nat.dvd_of_mem_primeFactors ((mem_ramifiedPrimes_iff d p).mp hp_ram)
  exact (hp.coprime_iff_not_dvd.mp
    (Nat.Coprime.coprime_dvd_left hp_norm I.2)) hp_modulus

/-- The local genus characters of a narrow ideal class have coordinate product
equal to one. -/
theorem genusCharacter_product_eq_one (C : Cl⁺(d)) :
    ∏ p : RamifiedPrimeIndex d, genusCharacter d p C = 1 := by
  obtain ⟨I, hI⟩ := exists_genusCoprimeIdeal_mk0_eq d C
  rw [← hI]
  have hn : Ideal.absNorm (I.1.1 : Ideal OK) ≠ 0 :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors I.1
  have hprod :
      (∏ p : RamifiedPrimeIndex d,
        kroneckerSymNat (primeDiscriminantFactor d p)
          (Ideal.absNorm (I.1.1 : Ideal OK))) = 1 := by
    calc
      (∏ p : RamifiedPrimeIndex d,
          kroneckerSymNat (primeDiscriminantFactor d p)
            (Ideal.absNorm (I.1.1 : Ideal OK))) =
          kroneckerSymNat
            (∏ p : RamifiedPrimeIndex d, primeDiscriminantFactor d p)
            (Ideal.absNorm (I.1.1 : Ideal OK)) :=
        (kroneckerSymNat_prod_left Finset.univ (primeDiscriminantFactor d) hn).symm
      _ = kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ)))
          (Ideal.absNorm (I.1.1 : Ideal OK)) := by
        rw [prod_primeDiscriminantFactor_eq_discr]
      _ = 1 := kroneckerSymNat_discr_absNorm_eq_one d I
  simp_rw [genusCharacter_apply_mk0]
  apply Units.ext
  change (Units.coeHom ℤ) (∏ p : RamifiedPrimeIndex d, rawGenusCharacter d p I) = 1
  rw [map_prod]
  simpa using hprod

/-- The product-one genus character map on the narrow class group. -/
noncomputable def genusCharacterMap :
    Cl⁺(d) →* AdmissibleGenusSignVector d :=
  (Pi.monoidHom (genusCharacter d)).codRestrict
    (admissibleGenusSignVectors d) (genusCharacter_product_eq_one d)

/-- A coordinate of the genus character map is the corresponding descended
local genus character. -/
@[simp]
theorem genusCharacterMap_apply
    (C : Cl⁺(d)) (p : RamifiedPrimeIndex d) :
    (genusCharacterMap d C : GenusSignVector d) p = genusCharacter d p C :=
  rfl

end GenusTheory
end ClassGroup
end QuadraticNumberFields
