/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Data.Nat.ChineseRemainder
import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.SignVector
import QuadraticNumberFields.ClassGroup.GenusTheory.PrimeDiscriminant.Product

/-!
# Residues With Prescribed Genus Signs

This file realizes arbitrary local sign vectors by a natural residue coprime to
the product of the signed prime-discriminant moduli. The product-one condition
is deliberately absent here; it enters only when the resulting residue is used
to construct a split prime.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

private theorem exists_nat_kroneckerSymNat_oddPrimeDiscriminantFactor_eq_unit
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (u : ℤˣ) :
    ∃ a : ℕ, a.Coprime (oddPrimeDiscriminantFactor p).natAbs ∧
      kroneckerSymNat (oddPrimeDiscriminantFactor p) a = (u : ℤ) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · refine ⟨1, by simp, ?_⟩
    rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
    simp [legendreSym.at_one]
  · have hchar : ringChar (ZMod p) ≠ 2 := by
      rwa [ZMod.ringChar_zmod_n]
    rcases quadraticChar_exists_neg_one' (F := ZMod p) hchar with ⟨x, hx⟩
    refine ⟨(x : ZMod p).val, by simpa using ZMod.val_coe_unit_coprime x, ?_⟩
    rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
    dsimp [legendreSym]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    simpa using hx

private theorem exists_nat_kroneckerSymNat_twoPrimeDiscriminantFactor_eq_unit
    (d : ℤ) (u : ℤˣ) :
    ∃ a : ℕ, a.Coprime (twoPrimeDiscriminantFactor d).natAbs ∧
      kroneckerSymNat (twoPrimeDiscriminantFactor d) a = (u : ℤ) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · refine ⟨1, ?_, ?_⟩
    · rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with h4 | h8
      · simp [h4]
      · simp [h8]
    · rw [twoPrimeDiscriminantFactor]
      split_ifs <;> norm_num [kroneckerSymNat, kroneckerTwo]
  · rw [twoPrimeDiscriminantFactor]
    by_cases hd2 : d % 2 = 0
    · by_cases hd8 : d % 8 = 2
      · refine ⟨3, ?_, ?_⟩
        · norm_num [Int.dvd_of_emod_eq_zero hd2, hd8]
        · norm_num [hd2, hd8, kroneckerSymNat, kroneckerTwo]
      · refine ⟨5, ?_, ?_⟩
        · norm_num [Int.dvd_of_emod_eq_zero hd2, hd8]
        · norm_num [hd2, hd8, kroneckerSymNat, kroneckerTwo]
    · refine ⟨3, ?_, ?_⟩
      · have hd2ndvd : ¬(2 : ℤ) ∣ d := fun h ↦ hd2 (Int.emod_eq_zero_of_dvd h)
        norm_num [hd2ndvd]
      · norm_num [hd2, kroneckerSymNat, kroneckerTwo]

/-- Every sign occurs as the Kronecker symbol of a residue coprime to one signed
prime-discriminant factor. -/
theorem exists_nat_kroneckerSymNat_primeDiscriminantFactor_eq_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : RamifiedPrimeIndex d) (u : ℤˣ) :
    ∃ a : ℕ, a.Coprime (primeDiscriminantFactor d p).natAbs ∧
      kroneckerSymNat (primeDiscriminantFactor d p) a = (u : ℤ) := by
  by_cases hp2 : p.1 = 2
  · rw [primeDiscriminantFactor_of_val_eq_two d p hp2]
    exact exists_nat_kroneckerSymNat_twoPrimeDiscriminantFactor_eq_unit d u
  · rw [primeDiscriminantFactor_of_val_ne_two d p hp2]
    letI : Fact p.1.Prime := ⟨prime_of_mem_ramifiedPrimeIndex d p⟩
    exact exists_nat_kroneckerSymNat_oddPrimeDiscriminantFactor_eq_unit hp2 u

/-- Every genus sign vector is realized by a natural residue coprime to the
product of the signed prime-discriminant moduli. -/
theorem exists_residue_for_genusSignVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (ε : GenusSignVector d) :
    ∃ a : ℕ, a.Coprime (primeDiscriminantModulus d) ∧
      ∀ p : RamifiedPrimeIndex d,
        kroneckerSymNat (primeDiscriminantFactor d p) a = (ε p : ℤ) := by
  classical
  let residue : RamifiedPrimeIndex d → ℕ := fun p ↦
    Classical.choose (exists_nat_kroneckerSymNat_primeDiscriminantFactor_eq_unit d p (ε p))
  have hres_coprime : ∀ p : RamifiedPrimeIndex d,
      (residue p).Coprime (primeDiscriminantFactor d p).natAbs := fun p ↦
    (Classical.choose_spec
      (exists_nat_kroneckerSymNat_primeDiscriminantFactor_eq_unit d p (ε p))).1
  have hres_symbol : ∀ p : RamifiedPrimeIndex d,
      kroneckerSymNat (primeDiscriminantFactor d p) (residue p) = (ε p : ℤ) := fun p ↦
    (Classical.choose_spec
      (exists_nat_kroneckerSymNat_primeDiscriminantFactor_eq_unit d p (ε p))).2
  let aCRT := Nat.chineseRemainderOfFinset
    (a := residue)
    (s := fun p : RamifiedPrimeIndex d ↦ (primeDiscriminantFactor d p).natAbs)
    Finset.univ
    (fun p _ ↦ natAbs_primeDiscriminantFactor_ne_zero d p)
    (fun p _ q _ hpq ↦ pairwise_coprime_natAbs_primeDiscriminantFactor d hpq)
  refine ⟨aCRT, ?_, ?_⟩
  · rw [primeDiscriminantModulus, Nat.coprime_prod_right_iff]
    intro p _
    have hmod : (aCRT : ℕ) ≡ residue p [MOD (primeDiscriminantFactor d p).natAbs] :=
      aCRT.2 p (by simp)
    have hgcd := hmod.gcd_eq
    have hres_gcd : Nat.gcd (residue p) (primeDiscriminantFactor d p).natAbs = 1 := by
      simpa [Nat.Coprime] using hres_coprime p
    simpa [Nat.Coprime, hres_gcd] using hgcd
  · intro p
    have hmod : (aCRT : ℕ) ≡ residue p [MOD (primeDiscriminantFactor d p).natAbs] :=
      aCRT.2 p (by simp)
    exact (kroneckerSymNat_eq_of_modEq
      (primeDiscriminantFactor_emod_four_eq_zero_or_one d p) (dvd_refl _) hmod).trans
        (hres_symbol p)

end GenusTheory
end ClassGroup
end QuadraticNumberFields
