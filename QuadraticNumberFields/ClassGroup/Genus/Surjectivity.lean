/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.NumberTheory.LSeries.PrimesInAP
import QuadraticNumberFields.ClassGroup.Genus.QuotientMap
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker

/-!
# Surjectivity of Genus Characters

This file records the Dirichlet-plus-CRT lower-bound side of genus theory: every
admissible sign vector is represented by a narrow ideal class.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField nonZeroDivisors QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- For an odd rational prime `p`, every sign `±1` is the Legendre symbol of
some natural number coprime to `p`. -/
theorem exists_nat_legendreSym_eq_unit
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (u : ℤˣ) :
    ∃ a : ℕ, a.Coprime p ∧ legendreSym p (a : ℤ) = (u : ℤ) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, by simp, by simp [legendreSym.at_one]⟩
  · have hchar : ringChar (ZMod p) ≠ 2 := by
      rwa [ZMod.ringChar_zmod_n]
    rcases quadraticChar_exists_neg_one' (F := ZMod p) hchar with ⟨x, hx⟩
    refine ⟨(x : ZMod p).val, ?_, ?_⟩
    · rw [Nat.coprime_comm, (Fact.out : Nat.Prime p).coprime_iff_not_dvd]
      intro hp_dvd_x
      have hx_zero : (x : ZMod p) = 0 := by
        rw [← ZMod.natCast_zmod_val (x : ZMod p)]
        exact (ZMod.natCast_eq_zero_iff (x : ZMod p).val p).mpr hp_dvd_x
      exact x.ne_zero hx_zero
    · dsimp [legendreSym]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      simpa using hx

/-- The odd signed prime-discriminant factor is congruent to `1` modulo `4`. -/
theorem oddPrimeDiscriminantFactor_emod_four_eq_one {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    oddPrimeDiscriminantFactor p % 4 = 1 := by
  have hp_odd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  rw [oddPrimeDiscriminantFactor]
  by_cases hp4 : p % 4 = 1
  · simp [hp4]
    omega
  · have hp4' : p % 4 = 3 := by omega
    simp [hp4]
    omega

/-- Odd signed prime-discriminant factors evaluate as Legendre symbols. -/
theorem kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym
    {p a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    kroneckerSymNat (oddPrimeDiscriminantFactor p) a = legendreSym p (a : ℤ) := by
  have hD4 :=
    oddPrimeDiscriminantFactor_emod_four_eq_one (Fact.out : p.Prime) hp2
  rw [kroneckerSymNat_eq_jacobiSym_natAbs_of_emod_four_eq_one _ hD4,
    natAbs_oddPrimeDiscriminantFactor, ← jacobiSym.legendreSym.to_jacobiSym]

/-- Every sign occurs as an odd signed prime-discriminant Kronecker symbol. -/
theorem exists_nat_kroneckerSymNat_oddPrimeDiscriminantFactor_eq_unit
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (u : ℤˣ) :
    ∃ a : ℕ, a.Coprime (oddPrimeDiscriminantFactor p).natAbs ∧
      kroneckerSymNat (oddPrimeDiscriminantFactor p) a = (u : ℤ) := by
  rcases exists_nat_legendreSym_eq_unit p hp2 u with ⟨a, ha, hleg⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [natAbs_oddPrimeDiscriminantFactor] using ha
  · rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
    exact hleg

/-- Every sign occurs as a `2`-primary signed prime-discriminant Kronecker symbol. -/
theorem exists_nat_kroneckerSymNat_twoPrimeDiscriminantFactor_eq_unit
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
        · have hd2dvd : (2 : ℤ) ∣ d := Int.dvd_of_emod_eq_zero hd2
          simp [hd2dvd, hd8]
          norm_num
        · simp [hd2, hd8]
          norm_num [kroneckerSymNat, kroneckerTwo]
      · refine ⟨5, ?_, ?_⟩
        · have hd2dvd : (2 : ℤ) ∣ d := Int.dvd_of_emod_eq_zero hd2
          simp [hd2dvd, hd8]
          norm_num
        · simp [hd2, hd8]
          norm_num [kroneckerSymNat, kroneckerTwo]
    · refine ⟨3, ?_, ?_⟩
      · have hd2ndvd : ¬ (2 : ℤ) ∣ d := by
          intro h
          exact hd2 (Int.emod_eq_zero_of_dvd h)
        simp [hd2ndvd]
        norm_num
      · simp [hd2]
        norm_num [kroneckerSymNat, kroneckerTwo]

/-- A signed prime-discriminant factor is congruent to `0` or `1` modulo `4`, so
the Kronecker symbol is periodic modulo its absolute value. -/
theorem emod_four_eq_zero_or_one_of_mem_signedPrimeDiscriminantFactors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {q : ℤ} (hq : q ∈ signedPrimeDiscriminantFactors d) :
    q % 4 = 0 ∨ q % 4 = 1 := by
  rw [signedPrimeDiscriminantFactors] at hq
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  have hp_prime : p.Prime := prime_of_mem_ramifiedPrimes hp
  by_cases hp2 : p = 2
  · subst p
    rw [primeDiscriminantFactor, if_pos rfl, twoPrimeDiscriminantFactor]
    split_ifs <;> omega
  · right
    rw [primeDiscriminantFactor, if_neg hp2]
    exact oddPrimeDiscriminantFactor_emod_four_eq_one hp_prime hp2

/-- The signed-factor Kronecker symbol only depends on the denominator modulo the
absolute value of that signed factor. -/
theorem kroneckerSymNat_eq_of_modEq_natAbs
    {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {a b : ℕ}
    (hab : a ≡ b [MOD D.natAbs]) :
    kroneckerSymNat D a = kroneckerSymNat D b := by
  letI : Fact (D % 4 = 0 ∨ D % 4 = 1) := ⟨hD⟩
  have hmod : a % D.natAbs = b % D.natAbs := by
    simpa [Nat.ModEq] using hab
  rw [← kroneckerSymNat_mod_natAbs_eq D a, ← kroneckerSymNat_mod_natAbs_eq D b, hmod]

/-- Every sign occurs as a Kronecker symbol for an arbitrary signed
prime-discriminant factor. -/
theorem exists_nat_kroneckerSymNat_signedPrimeDiscriminantFactor_eq_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors d}) (u : ℤˣ) :
    ∃ a : ℕ, a.Coprime q.1.natAbs ∧ kroneckerSymNat q.1 a = (u : ℤ) := by
  rcases q with ⟨q, hq⟩
  rw [signedPrimeDiscriminantFactors] at hq
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  have hp_prime : p.Prime := prime_of_mem_ramifiedPrimes hp
  by_cases hp2 : p = 2
  · subst p
    simpa [primeDiscriminantFactor] using
      exists_nat_kroneckerSymNat_twoPrimeDiscriminantFactor_eq_unit d u
  · letI : Fact p.Prime := ⟨hp_prime⟩
    simpa [primeDiscriminantFactor, hp2] using
      exists_nat_kroneckerSymNat_oddPrimeDiscriminantFactor_eq_unit hp2 u

/-- The `2`-primary signed factor has absolute value coprime to every odd prime. -/
theorem coprime_natAbs_twoPrimeDiscriminantFactor_of_odd_prime
    (d : ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime (twoPrimeDiscriminantFactor d).natAbs p := by
  have hcop2p : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with h4 | h8
  · rw [h4]
    simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcop2p.pow_left 2
  · rw [h8]
    simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hcop2p.pow_left 3

/-- Distinct signed prime-discriminant factors have coprime absolute values. -/
theorem pairwise_coprime_natAbs_signedPrimeDiscriminantFactors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Set.Pairwise ((Finset.univ : Finset {q // q ∈ signedPrimeDiscriminantFactors d}) :
      Set {q // q ∈ signedPrimeDiscriminantFactors d})
        (fun q r => Nat.Coprime q.1.natAbs r.1.natAbs) := by
  intro q _ r _ hqr
  rcases q with ⟨q, hq⟩
  rcases r with ⟨r, hr⟩
  rw [signedPrimeDiscriminantFactors] at hq hr
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hr with ⟨l, hl, rfl⟩
  have hp_prime : p.Prime := prime_of_mem_ramifiedPrimes hp
  have hl_prime : l.Prime := prime_of_mem_ramifiedPrimes hl
  have hpl : p ≠ l := by
    intro hpl
    apply hqr
    exact Subtype.ext (by simp [hpl])
  by_cases hp2 : p = 2
  · subst p
    by_cases hl2 : l = 2
    · exact (hpl hl2.symm).elim
    · simpa [primeDiscriminantFactor, hl2] using
        coprime_natAbs_twoPrimeDiscriminantFactor_of_odd_prime d hl_prime hl2
  · by_cases hl2 : l = 2
    · subst l
      simpa [primeDiscriminantFactor, hp2] using
        (coprime_natAbs_twoPrimeDiscriminantFactor_of_odd_prime d hp_prime hp2).symm
    · have hcop : Nat.Coprime p l :=
        (Nat.coprime_primes hp_prime hl_prime).mpr hpl
      simpa [primeDiscriminantFactor, hp2, hl2, natAbs_oddPrimeDiscriminantFactor] using hcop

/-- CRT package for a prescribed signed-factor sign vector: one natural residue
class has all prescribed Kronecker symbols and is coprime to the product modulus. -/
theorem exists_nat_residue_with_prescribed_signedFactor_symbols
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (χ : genusCharacterTargetRelation d) :
    ∃ a : ℕ,
      a.Coprime (Finset.univ.prod
        (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => q.1.natAbs)) ∧
      ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
        kroneckerSymNat q.1 a = ((χ : genusCharacterTarget d) q : ℤ) := by
  classical
  let residue : {q // q ∈ signedPrimeDiscriminantFactors d} → ℕ := fun q =>
    Classical.choose
      (exists_nat_kroneckerSymNat_signedPrimeDiscriminantFactor_eq_unit d q
        ((χ : genusCharacterTarget d) q))
  have hres_coprime :
      ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
        (residue q).Coprime q.1.natAbs := by
    intro q
    exact (Classical.choose_spec
      (exists_nat_kroneckerSymNat_signedPrimeDiscriminantFactor_eq_unit d q
        ((χ : genusCharacterTarget d) q))).1
  have hres_symbol :
      ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
        kroneckerSymNat q.1 (residue q) = ((χ : genusCharacterTarget d) q : ℤ) := by
    intro q
    exact (Classical.choose_spec
      (exists_nat_kroneckerSymNat_signedPrimeDiscriminantFactor_eq_unit d q
        ((χ : genusCharacterTarget d) q))).2
  have hs_nonzero :
      ∀ q ∈ (Finset.univ : Finset {q // q ∈ signedPrimeDiscriminantFactors d}),
        q.1.natAbs ≠ 0 := by
    intro q _hq
    exact natAbs_ne_zero_of_mem_signedPrimeDiscriminantFactors d q.property
  let aCRT := Nat.chineseRemainderOfFinset
    (a := residue) (s := fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
      q.1.natAbs)
    Finset.univ hs_nonzero (pairwise_coprime_natAbs_signedPrimeDiscriminantFactors d)
  refine ⟨aCRT, ?_, ?_⟩
  · rw [Nat.coprime_prod_right_iff]
    intro q _hq
    have hmod : (aCRT : ℕ) ≡ residue q [MOD q.1.natAbs] := aCRT.2 q (by simp)
    have hgcd := hmod.gcd_eq
    have hres_gcd : Nat.gcd (residue q) q.1.natAbs = 1 := by
      simpa [Nat.Coprime] using hres_coprime q
    simpa [Nat.Coprime, hres_gcd] using hgcd
  · intro q
    have hmod : (aCRT : ℕ) ≡ residue q [MOD q.1.natAbs] := aCRT.2 q (by simp)
    exact (kroneckerSymNat_eq_of_modEq_natAbs
      (emod_four_eq_zero_or_one_of_mem_signedPrimeDiscriminantFactors d q.property) hmod).trans
        (hres_symbol q)

/-- A rational prime with Kronecker value `1` for the field discriminant gives a
narrow ideal class represented by an integral ideal of absolute norm `p`. -/
theorem exists_narrowClass_absNorm_eq_of_kroneckerSymNat_discr_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : ℕ) [Fact p.Prime]
    (hp : kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ))) p = 1) :
    ∃ C : Cl⁺(d), ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
      NarrowClassGroup.mk0 I = C ∧
        Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = p := by
  rcases Splitting.exists_nonzero_ideal_absNorm_eq_of_kroneckerSymNat_discr_eq_one d p hp with
    ⟨I, hI⟩
  exact ⟨NarrowClassGroup.mk0 I, I, rfl, hI⟩

/-- A common coprime ideal representative realizing every signed-factor coordinate
proves surjectivity of the genus-character map. This isolates the remaining
CRT/Dirichlet/splitting construction from the formal descent step. -/
theorem genusCharacterMap_surjective_of_exists_signedFactorsCoprime_representative
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hrep : ∀ χ : genusCharacterTargetRelation d,
      ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
        ∃ hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
          signedFactorsCoprimeIdealSubmonoid d,
            ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
              genusCharacterOfSignedFactorRaw d q ⟨(I : Ideal
                (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))), hI q⟩ =
                  (χ : genusCharacterTarget d) q) :
    Function.Surjective (genusCharacterMap d) := by
  intro χ
  rcases hrep χ with ⟨I, hI, hχ⟩
  refine ⟨NarrowClassGroup.mk0 I, ?_⟩
  ext q
  rw [genusCharacterMap_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid d I hI q]
  exact congrArg ((↑) : ℤˣ → ℤ) (hχ q)

/-- If a rational prime realizes all coordinates of a target sign vector, then its
field-discriminant Kronecker symbol is `1`. This is where the product-one relation
in `genusCharacterTargetRelation` is used. -/
theorem kroneckerSymNat_discr_eq_one_of_prescribed_signedFactor_symbols
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp_prime : p.Prime) (χ : genusCharacterTargetRelation d)
    (hp_symbols : ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
      kroneckerSymNat q.1 p = ((χ : genusCharacterTarget d) q : ℤ)) :
    kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ))) p = 1 := by
  have hχ_prod_units :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        (χ : genusCharacterTarget d) q) = 1 :=
    (mem_genusCharacterTargetRelation_iff d (χ : genusCharacterTarget d)).mp χ.property
  have hχ_prod_int :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        ((χ : genusCharacterTarget d) q : ℤ)) = 1 := by
    simpa [Units.coe_prod] using congrArg ((↑) : ℤˣ → ℤ) hχ_prod_units
  have hprod_symbols :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        kroneckerSymNat q.1 p) = 1 := by
    calc
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
          kroneckerSymNat q.1 p) =
          Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
            ((χ : genusCharacterTarget d) q : ℤ)) := by
        exact Finset.prod_congr rfl fun q _ => hp_symbols q
      _ = 1 := hχ_prod_int
  have hp_ne_zero : p ≠ 0 := hp_prime.ne_zero
  have hformula :
      kroneckerSymNat (RingOfIntegers.discrFormula d) p = 1 := by
    calc
      kroneckerSymNat (RingOfIntegers.discrFormula d) p =
          kroneckerSymNat ((signedPrimeDiscriminantFactors d).prod id) p := by
        rw [prod_signedPrimeDiscriminantFactors_eq_discrFormula d]
      _ = kroneckerSymNat
          ((signedPrimeDiscriminantFactors d).attach.prod fun q => q.1) p := by
        congr 1
        exact (Finset.prod_attach (signedPrimeDiscriminantFactors d) id).symm
      _ = Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
          kroneckerSymNat q.1 p) := by
        rw [kroneckerSymNat_prod_left _ _ hp_ne_zero]
        simp
      _ = 1 := hprod_symbols
  rw [RingOfIntegers.discr_formula d]
  exact hformula

/-- A rational prime whose signed-factor symbols realize a target sign vector
gives a preimage under the genus-character map.

This is the formal descent from the CRT/Dirichlet/splitting construction to
surjectivity of the signed narrow genus-character map. -/
theorem genusCharacterMap_surjective_of_exists_prime_with_prescribed_signedFactor_symbols
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hprime : ∀ χ : genusCharacterTargetRelation d,
      ∃ p : ℕ, ∃ _ : p.Prime,
        ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
          kroneckerSymNat q.1 p = ((χ : genusCharacterTarget d) q : ℤ)) :
    Function.Surjective (genusCharacterMap d) := by
  refine genusCharacterMap_surjective_of_exists_signedFactorsCoprime_representative d ?_
  intro χ
  rcases hprime χ with ⟨p, hp_prime, hp_symbols⟩
  letI : Fact p.Prime := ⟨hp_prime⟩
  have hp_discr :=
    kroneckerSymNat_discr_eq_one_of_prescribed_signedFactor_symbols d hp_prime χ hp_symbols
  have hp_coprime : ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
      Nat.Coprime p q.1.natAbs := by
    intro q
    by_contra hcop
    have hzero : kroneckerSymNat q.1 p = 0 :=
      kroneckerSymNat_eq_zero_of_not_coprime q.1 (by simpa [Nat.Coprime] using hcop)
    have hnonzero : kroneckerSymNat q.1 p ≠ 0 := by
      rw [hp_symbols q]
      exact ((χ : genusCharacterTarget d) q).ne_zero
    exact hnonzero hzero
  rcases Splitting.exists_nonzero_ideal_absNorm_eq_of_kroneckerSymNat_discr_eq_one d p
      hp_discr with ⟨I, hI_abs⟩
  refine ⟨I, ?_, ?_⟩
  · intro q
    change Nat.Coprime
      (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
        q.1.natAbs
    simpa [hI_abs] using hp_coprime q
  · intro q
    ext
    simp [genusCharacterOfSignedFactorRaw_val, hI_abs, hp_symbols q]

/-- Signed local-symbol realization: every product-one signed genus character is
realized by a rational prime.

This is the remaining CRT plus Dirichlet arithmetic-progression construction. It
must prescribe the Kronecker symbols for all signed prime discriminant factors,
including the `2`-primary signed factor. -/
theorem exists_prime_with_prescribed_signedFactor_symbols
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (χ : genusCharacterTargetRelation d) :
    ∃ p : ℕ, ∃ _ : p.Prime,
      ∀ q : {q // q ∈ signedPrimeDiscriminantFactors d},
        kroneckerSymNat q.1 p = ((χ : genusCharacterTarget d) q : ℤ) := by
  classical
  let M : ℕ := Finset.univ.prod
    (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => q.1.natAbs)
  rcases exists_nat_residue_with_prescribed_signedFactor_symbols d χ with
    ⟨a, ha_coprime, ha_symbols⟩
  have hM0 : M ≠ 0 := by
    dsimp [M]
    exact Finset.prod_ne_zero_iff.mpr fun q _ =>
      natAbs_ne_zero_of_mem_signedPrimeDiscriminantFactors d q.property
  have ha_coprime_M : a.Coprime M := by
    simpa [M] using ha_coprime
  rcases Nat.forall_exists_prime_gt_and_modEq 0 (q := M) (a := a) hM0 ha_coprime_M with
    ⟨p, _hp_gt, hp_prime, hp_mod_M⟩
  refine ⟨p, hp_prime, ?_⟩
  intro q
  have hq_dvd_M : q.1.natAbs ∣ M := by
    dsimp [M]
    exact Finset.dvd_prod_of_mem
      (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} => q.1.natAbs)
      (Finset.mem_univ q)
  have hp_mod_q : p ≡ a [MOD q.1.natAbs] :=
    Nat.ModEq.of_dvd hq_dvd_M hp_mod_M
  exact (kroneckerSymNat_eq_of_modEq_natAbs
    (emod_four_eq_zero_or_one_of_mem_signedPrimeDiscriminantFactors d q.property) hp_mod_q).trans
      (ha_symbols q)

/-- The genus-character map itself is surjective. -/
theorem genusCharacterMap_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (genusCharacterMap d) := by
  exact genusCharacterMap_surjective_of_exists_prime_with_prescribed_signedFactor_symbols d
    (exists_prime_with_prescribed_signedFactor_symbols d)

/-- Direct genus-character surjectivity descends to the square quotient. -/
theorem genusCharacterMapOnSquareQuotient_surjective_of_genusCharacterMap_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (genusCharacterMapOnSquareQuotient d) := by
  intro χ
  obtain ⟨C, hC⟩ := genusCharacterMap_surjective d χ
  refine ⟨QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C, ?_⟩
  simpa [genusCharacterMapOnSquareQuotient_mk'] using hC

/-- Surjectivity gives the lower bound for the narrow square-class quotient. -/
theorem genusBound_le_card_narrowClassGroupSquareQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    2 ^ (ramifiedPrimeCount d - 1) ≤
      Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) := by
  rw [← card_genusCharacterTargetRelation d]
  exact Nat.card_le_card_of_surjective (genusCharacterMapOnSquareQuotient d)
    (genusCharacterMapOnSquareQuotient_surjective_of_genusCharacterMap_surjective d)

/-- Genus-character surjectivity gives the standard genus-theory divisibility for
the narrow class number. -/
theorem genus_divisibility_narrowClassNumber
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    2 ^ (ramifiedPrimeCount d - 1) ∣
      Qsqrtd.narrowClassNumber d := by
  have htarget_dvd_quot :
      Nat.card (genusCharacterTargetRelation d) ∣
        Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) :=
    Subgroup.card_dvd_of_surjective (genusCharacterMapOnSquareQuotient d)
      (genusCharacterMapOnSquareQuotient_surjective_of_genusCharacterMap_surjective d)
  have hquot_dvd :
      Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) ∣
        Qsqrtd.narrowClassNumber d := by
    simpa [Qsqrtd.narrowClassNumber, NarrowClassGroup.classNumber, Subgroup.index_eq_card] using
      (Subgroup.square (Cl⁺(d))).index_dvd_card
  rw [card_genusCharacterTargetRelation d] at htarget_dvd_quot
  exact dvd_trans htarget_dvd_quot hquot_dvd
end Genus
end ClassGroup
end QuadraticNumberFields
