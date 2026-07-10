/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.ClassGroup.GenusTheory.PrimeDiscriminant.Product

/-!
# Raw Genus Characters

This file defines one common monoid of nonzero integral ideals whose absolute
norm is coprime to the field discriminant, then evaluates every local
prime-discriminant character on that monoid.
-/

open scoped NumberField nonZeroDivisors QuadraticNumberFields.Splitting

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- Nonzero integral ideals whose absolute norm is coprime to the field
discriminant. -/
def genusCoprimeIdeals : Submonoid ((Ideal OK)⁰) where
  carrier := {I | Nat.Coprime (Ideal.absNorm (I.1 : Ideal OK))
    (primeDiscriminantModulus d)}
  one_mem' := by simp [primeDiscriminantModulus]
  mul_mem' := by
    intro I J hI hJ
    simpa only [Set.mem_setOf_eq, Submonoid.coe_mul, Ideal.absNorm.map_mul] using
      Nat.Coprime.mul_left hI hJ

/-- A nonzero integral ideal whose norm is coprime to the field discriminant. -/
abbrev GenusCoprimeIdeal : Type :=
  genusCoprimeIdeals d

/-- A genus-coprime ideal has norm coprime to every local
prime-discriminant modulus. -/
theorem genusCoprimeIdeal_coprime_factor
    (I : GenusCoprimeIdeal d) (p : RamifiedPrimeIndex d) :
    Nat.Coprime (Ideal.absNorm (I.1.1 : Ideal OK))
      (primeDiscriminantFactor d p).natAbs := by
  have hI := I.2
  change Nat.Coprime (Ideal.absNorm (I.1.1 : Ideal OK))
    (primeDiscriminantModulus d) at hI
  exact Nat.Coprime.of_dvd_right
    (natAbs_primeDiscriminantFactor_dvd_primeDiscriminantModulus d p) hI

/-- The raw character associated to a ramified rational prime. -/
noncomputable def rawGenusCharacter (p : RamifiedPrimeIndex d) :
    GenusCoprimeIdeal d →* ℤˣ where
  toFun I := kroneckerSymNatUnit (primeDiscriminantFactor d p)
    (genusCoprimeIdeal_coprime_factor d I p)
  map_one' := by
    ext
    simp [kroneckerSymNat]
  map_mul' I J := by
    ext
    simp only [coe_kroneckerSymNatUnit, Units.val_mul]
    change kroneckerSymNat (primeDiscriminantFactor d p)
      (Ideal.absNorm ((I.1.1 : Ideal OK) * (J.1.1 : Ideal OK))) =
        kroneckerSymNat (primeDiscriminantFactor d p)
            (Ideal.absNorm (I.1.1 : Ideal OK)) *
          kroneckerSymNat (primeDiscriminantFactor d p)
            (Ideal.absNorm (J.1.1 : Ideal OK))
    rw [Ideal.absNorm.map_mul, kroneckerSymNat_mul]
    · exact Ideal.absNorm_ne_zero_of_nonZeroDivisors I.1
    · exact Ideal.absNorm_ne_zero_of_nonZeroDivisors J.1

/-- The underlying integer of a raw genus character is its Kronecker-symbol
value. -/
@[simp]
theorem rawGenusCharacter_val (p : RamifiedPrimeIndex d)
    (I : GenusCoprimeIdeal d) :
    (rawGenusCharacter d p I : ℤ) =
      kroneckerSymNat (primeDiscriminantFactor d p)
        (Ideal.absNorm (I.1.1 : Ideal OK)) :=
  rfl

end GenusTheory
end ClassGroup
end QuadraticNumberFields
