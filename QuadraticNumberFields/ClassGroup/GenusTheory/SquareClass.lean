/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index
import QuadraticNumberFields.ClassGroup.Basic
import QuadraticNumberFields.ClassGroup.GenusTheory.CoprimeRepresentatives

/-!
# Genus-Theory Square Classes

This file contains the square-class subgroup `Cl²`, the principal-genus quotient
`Cl / Cl²`, and the descent of odd-prime genus characters to that quotient.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

open RingOfIntegers
open Splitting

local notation "𝓞" => _root_.NumberField.RingOfIntegers

/-! ## Class-number-one sieve (continued) -/

private theorem le_one_of_two_pow_sub_one_dvd_one {t : ℕ} (h : 2 ^ (t - 1) ∣ 1) :
    t ≤ 1 := by
  have hpow : 2 ^ (t - 1) = 1 := Nat.dvd_one.mp h
  by_contra hle
  have hsub_ne : t - 1 ≠ 0 := by omega
  have hpow_gt : 1 < 2 ^ (t - 1) :=
    one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) hsub_ne
  omega

/-- Once genus theory supplies the standard divisibility
`2 ^ (t - 1) ∣ h(d)`, class number one forces `t ≤ 1`. This isolates the
elementary arithmetic endpoint of the genus-theory sieve from the missing
genus-theory divisibility proof. -/
theorem primeDiscriminantFactorCount_le_one_of_genus_divisibility
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hdiv : 2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)))
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    primeDiscriminantFactorCount d ≤ 1 :=
  le_one_of_two_pow_sub_one_dvd_one (by simpa [hclass] using hdiv)

/-- A finite quotient of the ideal class group with cardinality `2 ^ (t - 1)`
gives the standard genus-theory divisibility `2 ^ (t - 1) ∣ h(d)`.

The missing genus-theory construction is exactly the production of such a
surjective quotient map, with `t = primeDiscriminantFactorCount d`. -/
theorem genus_divisibility_of_surjective_quotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (A : Type*) [Group A] [Finite A]
    (hcard : Nat.card A = 2 ^ (primeDiscriminantFactorCount d - 1))
    (φ : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* A) (hφ : Function.Surjective φ) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  rw [← hcard]
  simpa [NumberField.classNumber] using Subgroup.card_dvd_of_surjective φ hφ

/-- The subgroup of ideal classes that are squares. In genus theory this is the
principal genus, and the quotient `Cl / Cl²` is the genus quotient. This is the
generic `ClassGroup.squareSubgroup` specialized to `𝓞(ℚ(√d))`. -/
noncomputable def squareClassSubgroup (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Subgroup (ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :=
  _root_.ClassGroup.squareSubgroup (𝓞 (Qsqrtd (d : ℚ)))

/-- The square-class quotient `Cl / Cl²` for `𝓞(ℚ(√d))`. -/
noncomputable abbrev squareClassQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :=
  ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d

noncomputable instance instFintypeSquareClassSubgroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fintype (squareClassSubgroup d) :=
  Fintype.ofFinite _

noncomputable instance instFintypeSquareClassQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fintype (squareClassQuotient d) :=
  Fintype.ofFinite _

/-- The genus-theory square subgroup is definitionally the generic square-subgroup
API for ideal class groups. -/
theorem squareClassSubgroup_eq_squareSubgroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    squareClassSubgroup d =
      _root_.ClassGroup.squareSubgroup (𝓞 (Qsqrtd (d : ℚ))) :=
  rfl

/-- The quotient `Cl / Cl²` has the same cardinality as the kernel of the square map on
the class group. This is the finite-group algebra behind the two-torsion formulation
of genus theory. -/
theorem card_squareClassSubgroup_quotient_eq_card_powMonoidHom_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
      Nat.card (powMonoidHom (α := ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) 2).ker := by
  letI := _root_.NumberField.RingOfIntegers.instFintypeClassGroup (Qsqrtd (d : ℚ))
  haveI : (powMonoidHom (α := ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) 2).ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite
  rw [← Subgroup.index_eq_card]
  rw [squareClassSubgroup, _root_.ClassGroup.squareSubgroup_eq_powMonoidHom_range]
  rw [Subgroup.index_range]

/-- The square-class quotient `Cl / Cl²` has the same cardinality as the
two-torsion subgroup `Cl[2]`. -/
theorem card_squareClassQuotient_eq_card_twoTorsionSubgroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (squareClassQuotient d) =
      Nat.card (_root_.ClassGroup.twoTorsionSubgroup (𝓞 (Qsqrtd (d : ℚ)))) := by
  letI := _root_.NumberField.RingOfIntegers.instFintypeClassGroup (Qsqrtd (d : ℚ))
  simpa [squareClassQuotient, _root_.ClassGroup.squareQuotient,
    squareClassSubgroup_eq_squareSubgroup d] using
    (_root_.ClassGroup.card_squareQuotient_eq_card_twoTorsionSubgroup
      (𝓞 (Qsqrtd (d : ℚ))))

/-! ## Squares lie in the principal genus -/

/-- The prime-to-`p` raw genus character takes values of order dividing two. -/
theorem genusCharacterRawUnit_sq_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I : absNormCoprimeIdealSubmonoid d p) :
    genusCharacterRawUnit d p I ^ 2 = 1 := by
  ext
  exact genusCharacterRaw_sq_eq_one_of_norm_not_dvd d p I I.2

/-- A descended genus character takes values of order dividing two on every class. -/
theorem genusCharacterOfAbsNormCoprimeIdeals_sq_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnAbsNormCoprimeIdeals d p))
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    genusCharacterOfAbsNormCoprimeIdeals d p hd_neg hp_disc hsurj C ^ 2 = 1 := by
  let I := Classical.choose (hsurj C)
  have hI : mk0OnAbsNormCoprimeIdeals d p I = C := Classical.choose_spec (hsurj C)
  have happly := genusCharacterOfAbsNormCoprimeIdeals_apply_mk0OnAbsNormCoprimeIdeals
    d p hd_neg hp_disc hsurj I
  rw [hI] at happly
  rw [happly]
  exact genusCharacterRawUnit_sq_eq_one d p I

/-- Every descended genus character kills the square-class subgroup `Cl²`. This is the
formal `Cl² ⊆ principal genus` direction for the odd-prime genus characters. -/
theorem squareClassSubgroup_le_genusCharacterOfAbsNormCoprimeIdeals_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d) :
    squareClassSubgroup d ≤
      (genusCharacterOfAbsNormCoprimeIdeals d p hd_neg hp_disc
        (mk0OnAbsNormCoprimeIdeals_surjective_of_mem_oddPrimeDiscriminantDivisors
          d p hp_disc)).ker := by
  intro C hC
  rw [squareClassSubgroup, _root_.ClassGroup.mem_squareSubgroup_iff] at hC
  rcases hC with ⟨D, rfl⟩
  rw [MonoidHom.mem_ker, map_pow]
  exact genusCharacterOfAbsNormCoprimeIdeals_sq_eq_one
    d p hd_neg hp_disc
    (mk0OnAbsNormCoprimeIdeals_surjective_of_mem_oddPrimeDiscriminantDivisors d p hp_disc) D

/-- A descended odd-prime genus character as a character on the principal-genus
quotient `Cl / Cl²`. -/
noncomputable def genusCharacterOnSquareClassQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d →* ℤˣ :=
  QuotientGroup.lift (squareClassSubgroup d)
    (genusCharacterOfAbsNormCoprimeIdeals d p hd_neg hp_disc
      (mk0OnAbsNormCoprimeIdeals_surjective_of_mem_oddPrimeDiscriminantDivisors d p hp_disc))
    (squareClassSubgroup_le_genusCharacterOfAbsNormCoprimeIdeals_ker
      d p hd_neg hp_disc)

/-- The character on `Cl / Cl²` agrees with the descended genus character after
composing with the quotient map. -/
theorem genusCharacterOnSquareClassQuotient_apply
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    genusCharacterOnSquareClassQuotient d p hd_neg hp_disc C =
      genusCharacterOfAbsNormCoprimeIdeals d p hd_neg hp_disc
        (mk0OnAbsNormCoprimeIdeals_surjective_of_mem_oddPrimeDiscriminantDivisors d p hp_disc)
        C := by
  rfl

end ClassGroup
end QuadraticNumberFields
