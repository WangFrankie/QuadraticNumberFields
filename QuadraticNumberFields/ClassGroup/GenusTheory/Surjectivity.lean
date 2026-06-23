/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.LSeries.PrimesInAP
import QuadraticNumberFields.ClassGroup.GenusTheory.Formula

/-!
# Genus-Character Surjectivity

This file contains the weak odd-discriminant genus-theory boundary needed by the
class-number-one sieve. It separates the route proving the product genus-character
map is surjective from the stronger principal-genus theorem.

The main mathematical input is the Cox/Gauss surjectivity step translated to
ideal classes: choose primes in arithmetic progressions with prescribed
Legendre symbols, use the splitting criterion in `ℚ(√d)`, and take a prime ideal
above the resulting split rational prime.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

open RingOfIntegers
open Splitting

local notation "𝓞" => _root_.NumberField.RingOfIntegers

/-- A split rational prime has a prime ideal above it with absolute norm `p`. -/
theorem exists_nonzero_ideal_absNorm_eq_of_isSplitIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : ℕ) [Fact p.Prime]
    (hsplit : Ideal.IsSplitIn (𝔭(p)) (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
      Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) = p := by
  have hp0 : (𝔭(p) : Ideal ℤ) ≠ ⊥ := by
    intro hpbot
    have hp_mem : (p : ℤ) ∈ (⊥ : Ideal ℤ) := by
      rw [← hpbot]
      exact Ideal.subset_span (by simp)
    have hp_ne_zero_int : (p : ℤ) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    exact hp_ne_zero_int (by simpa using hp_mem)
  obtain ⟨P, hP⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (𝔭(p)) (𝓞 (Qsqrtd (d : ℚ)))))
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (𝔭(p)) := hP.2
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 hP
  have hinertia : (𝔭(p) : Ideal ℤ).inertiaDeg P = 1 :=
    Ideal.inertiaDeg_eq_one_of_isSplitIn (𝔭(p)) (𝓞 (Qsqrtd (d : ℚ)))
      (by norm_num : ringChar ℤ ≠ 2) hsplit
  refine ⟨⟨P, ?_⟩, ?_⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hP0
  · rw [Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out : Nat.Prime p), hinertia, pow_one]

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

/-- The Legendre symbol of natural numbers only depends on their residue modulo `p`. -/
theorem legendreSym_natCast_eq_of_modEq
    (p : ℕ) [Fact p.Prime] {a b : ℕ} (h : a ≡ b [MOD p]) :
    legendreSym p (a : ℤ) = legendreSym p (b : ℤ) := by
  dsimp [legendreSym]
  have hZ : (a : ZMod p) = (b : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff a b p).mpr h
  simpa only [Int.cast_natCast] using congrArg (quadraticChar (ZMod p)) hZ

/-- CRT package for a prescribed odd-genus sign vector: one natural residue class
has all prescribed Legendre symbols and is coprime to the product modulus. -/
theorem exists_nat_residue_with_prescribed_odd_genus_symbols
    (d : ℤ) (ε : oddGenusSignRelationSubgroup d) :
    ∃ a : ℕ,
      a.Coprime (Finset.univ.prod
        (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} => P.1)) ∧
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        @legendreSym P.1 ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩ (a : ℤ) =
          ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P : ℤ) := by
  classical
  let residue : {p // p ∈ oddPrimeDiscriminantDivisors d} → ℕ := fun P =>
    Classical.choose (@exists_nat_legendreSym_eq_unit P.1
      ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
      (ne_two_of_mem_oddPrimeDiscriminantDivisors P.2)
      ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P))
  have hres_coprime :
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d}, (residue P).Coprime P.1 := by
    intro P
    exact (Classical.choose_spec (@exists_nat_legendreSym_eq_unit P.1
      ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
      (ne_two_of_mem_oddPrimeDiscriminantDivisors P.2)
      ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P))).1
  have hres_leg :
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        @legendreSym P.1 ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
            (residue P : ℤ) =
          ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P : ℤ) := by
    intro P
    exact (Classical.choose_spec (@exists_nat_legendreSym_eq_unit P.1
      ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
      (ne_two_of_mem_oddPrimeDiscriminantDivisors P.2)
      ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P))).2
  have hs_nonzero :
      ∀ P ∈ (Finset.univ : Finset {p // p ∈ oddPrimeDiscriminantDivisors d}),
        P.1 ≠ 0 := by
    intro P _hP
    exact (prime_of_mem_oddPrimeDiscriminantDivisors P.2).ne_zero
  have hpair :
      Set.Pairwise
        ((Finset.univ : Finset {p // p ∈ oddPrimeDiscriminantDivisors d}) :
          Set {p // p ∈ oddPrimeDiscriminantDivisors d})
        (fun P Q : {p // p ∈ oddPrimeDiscriminantDivisors d} => P.1.Coprime Q.1) := by
    intro P _hP Q _hQ hPQ
    exact (Nat.coprime_primes
      (prime_of_mem_oddPrimeDiscriminantDivisors P.2)
      (prime_of_mem_oddPrimeDiscriminantDivisors Q.2)).mpr (by
        intro h
        exact hPQ (Subtype.ext h))
  let aCRT := Nat.chineseRemainderOfFinset
    (a := residue) (s := fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} => P.1)
    Finset.univ hs_nonzero hpair
  refine ⟨aCRT, ?_, ?_⟩
  · rw [Nat.coprime_prod_right_iff]
    intro P _hP
    rw [Nat.coprime_comm,
      (prime_of_mem_oddPrimeDiscriminantDivisors P.2).coprime_iff_not_dvd]
    intro hp_dvd
    have hres_not_dvd : ¬ P.1 ∣ residue P :=
      (prime_of_mem_oddPrimeDiscriminantDivisors P.2).coprime_iff_not_dvd.mp
        (hres_coprime P).symm
    exact hres_not_dvd ((aCRT.2 P (by simp)).dvd_iff dvd_rfl |>.mp hp_dvd)
  · intro P
    exact (@legendreSym_natCast_eq_of_modEq P.1
        ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩ _ _ (aCRT.2 P (by simp))).trans
      (hres_leg P)

/-- **Prescribed split prime.** In the odd fundamental-discriminant branch, every
sign vector satisfying the product-one relation is realized by the Legendre
symbols of some rational prime `q` that splits in `ℚ(√d)`.

The proof is the Dirichlet/CRT/quadratic-reciprocity step: choose a unit residue
class modulo the odd discriminant with prescribed Legendre symbols, use the
product relation and `d % 4 = 1` to force `(d / q) = 1`, and apply
Dirichlet's theorem to find a prime in that class. -/
theorem exists_nat_prime_with_prescribed_odd_genus_symbols
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1) (ε : oddGenusSignRelationSubgroup d) :
    ∃ q : ℕ, ∃ hq_prime : q.Prime,
      q ≠ 2 ∧ ¬ (q : ℤ) ∣ d ∧ @legendreSym q ⟨hq_prime⟩ d = 1 ∧
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        @legendreSym P.1 ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩ (q : ℤ) =
          ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P : ℤ) := by
  classical
  let M : ℕ := Finset.univ.prod
    (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} => P.1)
  rcases exists_nat_residue_with_prescribed_odd_genus_symbols d ε with
    ⟨a, ha_coprime, ha_symbols⟩
  have hM0 : M ≠ 0 := by
    dsimp [M]
    exact Finset.prod_ne_zero_iff.mpr fun P _ =>
      (prime_of_mem_oddPrimeDiscriminantDivisors P.2).ne_zero
  have ha_coprime_M : a.Coprime M := by
    simpa [M] using ha_coprime
  rcases Nat.forall_exists_prime_gt_and_modEq (max d.natAbs 2)
      (q := M) (a := a) hM0 ha_coprime_M with
    ⟨q, hq_gt, hq_prime, hq_mod_M⟩
  letI : Fact q.Prime := ⟨hq_prime⟩
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    omega
  have hq_not_dvd : ¬ (q : ℤ) ∣ d := by
    intro hq_dvd
    have hq_le_abs : q ≤ d.natAbs := by
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_lt hd_neg))
        (Int.natCast_dvd.mp hq_dvd)
    omega
  have hq_symbols :
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        @legendreSym P.1 ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩ (q : ℤ) =
          ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P : ℤ) := by
    intro P
    have hP_dvd_M : P.1 ∣ M := by
      dsimp [M]
      exact Finset.dvd_prod_of_mem
        (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} => P.1) (Finset.mem_univ P)
    have hq_mod_P : q ≡ a [MOD P.1] := Nat.ModEq.of_dvd hP_dvd_M hq_mod_M
    exact (@legendreSym_natCast_eq_of_modEq P.1
      ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩ (a := q) (b := a) hq_mod_P).trans
      (ha_symbols P)
  have hprod_units :
      Finset.univ.prod
          (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} =>
            (ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P) = 1 :=
    (mem_oddGenusSignRelationSubgroup_iff d
      (ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ)).mp ε.property
  have hprod_int :
      Finset.univ.prod
          (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} =>
            ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P : ℤ)) = 1 := by
    simpa [Units.coe_prod] using congrArg (fun u : ℤˣ => (u : ℤ)) hprod_units
  have hprod_leg :
      Finset.univ.prod
          (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} =>
            @legendreSym P.1 ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
              (q : ℤ)) = 1 := by
    calc
      Finset.univ.prod
          (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} =>
            @legendreSym P.1 ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩ (q : ℤ)) =
          Finset.univ.prod
            (fun P : {p // p ∈ oddPrimeDiscriminantDivisors d} =>
              ((ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P : ℤ)) := by
        exact Finset.prod_congr rfl fun P _ => hq_symbols P
      _ = 1 := hprod_int
  have hprod_leg_attach :
      (oddPrimeDiscriminantDivisors d).attach.prod
          (fun P =>
            @legendreSym P.1 ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
              (q : ℤ)) = 1 := by
    rw [Finset.attach_eq_univ]
    exact hprod_leg
  have hjac : jacobiSym (q : ℤ) d.natAbs = 1 := by
    rw [jacobiSym_natAbs_eq_prod_oddPrimeDiscriminantDivisors_of_mod_four_eq_one
      d (q : ℤ) (Fact.out : Squarefree d) hd4]
    rw [← Finset.prod_attach (s := oddPrimeDiscriminantDivisors d)
      (f := fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩ (q : ℤ) else 1)]
    calc
      (oddPrimeDiscriminantDivisors d).attach.prod
          (fun P => if hp : P.1.Prime then @legendreSym P.1 ⟨hp⟩ (q : ℤ) else 1) =
          (oddPrimeDiscriminantDivisors d).attach.prod
            (fun P =>
              @legendreSym P.1 ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩ (q : ℤ)) := by
        apply Finset.prod_congr rfl
        intro P _hP
        simp [prime_of_mem_oddPrimeDiscriminantDivisors P.2]
      _ = 1 := hprod_leg_attach
  have hq_split : @legendreSym q ⟨hq_prime⟩ d = 1 := by
    have hkron : kroneckerSymNat (RingOfIntegers.discrFormula d) q = 1 := by
      rw [← jacobiSym_natAbs_eq_kroneckerSymNat_discrFormula_of_mod_four_eq_one d q hd4]
      exact hjac
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4] at hkron
    rwa [kroneckerSymNat_eq_legendreSym_of_ne_two d hq_ne_two] at hkron
  exact ⟨q, hq_prime, hq_ne_two, hq_not_dvd, hq_split, hq_symbols⟩

/-- **Prescribed odd genus symbols.** In the odd fundamental-discriminant branch,
every sign vector satisfying the single product relation is represented by one
nonzero integral ideal whose absolute norm is prime to every odd discriminant
prime and whose raw genus symbols have the prescribed values.

This is the weak Cox/Gauss genus-theory input needed for divisibility. The proof
uses CRT to prescribe Legendre symbols, Dirichlet's theorem on primes in
arithmetic progressions, the splitting criterion for `ℚ(√d)`, and the
norm calculation for a prime ideal over a split rational prime. -/
theorem exists_ideal_representing_odd_genus_sign_vector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1) (ε : oddGenusSignRelationSubgroup d) :
    ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
      ∃ hI_coprime :
        ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ),
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        letI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
        genusCharacterRawUnit d P.1
          ⟨(I : Ideal (𝓞 (Qsqrtd (d : ℚ)))), hI_coprime P⟩ =
            (ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P := by
  rcases exists_nat_prime_with_prescribed_odd_genus_symbols d hd_neg hd4 ε with
    ⟨q, hq_prime, hq_ne_two, hq_not_dvd, hq_split, hq_symbols⟩
  letI : Fact q.Prime := ⟨hq_prime⟩
  have hsplit : Ideal.IsSplitIn (𝔭(q)) (𝓞 (Qsqrtd (d : ℚ))) :=
    (Splitting.isSplit_iff_legendreSym_eq_one d q hq_ne_two hq_not_dvd).mpr hq_split
  rcases exists_nonzero_ideal_absNorm_eq_of_isSplitIn d q hsplit with ⟨I, hI_abs⟩
  refine ⟨I, ?_, ?_⟩
  · intro P hp_dvd_abs
    have hP_prime : P.1.Prime := prime_of_mem_oddPrimeDiscriminantDivisors P.2
    have hp_dvd_q_int : (P.1 : ℤ) ∣ (q : ℤ) := by
      simpa [hI_abs] using hp_dvd_abs
    have hp_dvd_q : P.1 ∣ q := by
      exact_mod_cast hp_dvd_q_int
    have hP_eq_q : P.1 = q :=
      (Nat.prime_dvd_prime_iff_eq hP_prime hq_prime).mp hp_dvd_q
    exact hq_not_dvd (by simpa [hP_eq_q] using dvd_param_of_mem_oddPrimeDiscriminantDivisors P.2)
  · intro P
    haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
    ext
    simp [genusCharacterRawUnit, genusCharacterRaw, hI_abs, hq_symbols P]

/-- **Odd genus-character surjectivity.** In the odd fundamental-discriminant
branch, every sign vector satisfying the single product relation is realized by
the odd genus-character product of an ideal class. -/
theorem oddGenusCharacterProductToRelationSubgroup_surjective_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1) (hrel : oddGenusProductRelation d hd_neg) :
    Function.Surjective
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel) := by
  intro ε
  rcases exists_ideal_representing_odd_genus_sign_vector d hd_neg hd4 ε with
    ⟨I, hI_coprime, hI_symbols⟩
  refine ⟨(QuotientGroup.mk' (squareClassSubgroup d)) (ClassGroup.mk0 I), ?_⟩
  apply Subtype.ext
  funext P
  haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
  change oddGenusCharacterProductOnSquareClassQuotient d hd_neg
      ((QuotientGroup.mk' (squareClassSubgroup d)) (ClassGroup.mk0 I)) P =
    (ε : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) P
  rw [oddGenusCharacterProductOnSquareClassQuotient_apply_mk']
  let IP : absNormCoprimeIdealSubmonoid d P.1 :=
    ⟨(I : Ideal (𝓞 (Qsqrtd (d : ℚ)))), hI_coprime P⟩
  have hmk : mk0OnAbsNormCoprimeIdeals d P.1 IP = ClassGroup.mk0 I := by
    simp [IP, mk0OnAbsNormCoprimeIdeals, absNormCoprimeIdealNonzeroMonoidHom]
  have happly := genusCharacterOfAbsNormCoprimeIdeals_apply_mk0OnAbsNormCoprimeIdeals
    d P.1 hd_neg P.2 IP
  rw [hmk] at happly
  rw [happly]
  exact hI_symbols P

/-- **Weak odd genus-theory divisibility.** For an imaginary quadratic field with
odd fundamental discriminant (`d % 4 = 1`), the genus-theory factor
`2 ^ (t - 1)` divides the class number.

This is weaker than the full principal-genus cardinality formula
`genusFormula_of_mod_four_eq_one`: it only uses surjectivity of the genus-character
product onto the relation subgroup, not the identification of its kernel with
the square-class subgroup. -/
theorem genus_divisibility_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  let hrel := oddGenusProductRelation_of_mod_four_eq_one d hd_neg hd4
  exact genus_divisibility_of_oddGenusCharacterProduct_surjective_of_discr_odd
    d hd_neg hodd hrel
    (oddGenusCharacterProductToRelationSubgroup_surjective_of_mod_four_eq_one
      d hd_neg hd4 hrel)

end ClassGroup
end QuadraticNumberFields
