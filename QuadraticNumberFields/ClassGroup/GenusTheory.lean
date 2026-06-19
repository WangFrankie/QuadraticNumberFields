/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.LegendreSymbol.Basic
import QuadraticNumberFields.ClassGroup.Torsion
import QuadraticNumberFields.ClassNumber
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker

/-!
# Genus Theory

This file will contain genus-theory infrastructure for quadratic class groups.

The first intended application is the elementary genus-theory sieve in the
imaginary class-number-one problem: class number one forces the fundamental
discriminant to have only one prime-discriminant factor.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

open RingOfIntegers
open Splitting

local notation "𝓞" => _root_.NumberField.RingOfIntegers

/-! ## Class-number-one sieve -/

/-- The number of distinct rational prime factors of the closed discriminant
formula for `ℚ(√d)`. For squarefree `d`, this is the genus-theory parameter
usually denoted `t`, the number of prime-discriminant factors of the fundamental
discriminant. -/
def primeDiscriminantFactorCount (d : ℤ) : ℕ :=
  (RingOfIntegers.discrFormula d).natAbs.primeFactors.card

/-! ## Discriminant prime factors -/

/-- The set of odd rational primes dividing the discriminant of `ℚ(√d)`.
These are precisely the odd primes at which the Kronecker symbol of the discriminant
vanishes — i.e., the ramified odd primes. By `isRamified_iff_kroneckerSymNat_discr_eq_zero`
and the odd-prime bridge `legendreSym_discFormula_eq_legendreSym_param_of_ne_two`,
for an odd prime `p` this is equivalent to `p ∣ d`. -/
def oddPrimeDiscriminantDivisors (d : ℤ) : Finset ℕ :=
  ((RingOfIntegers.discrFormula d).natAbs.primeFactors).filter fun p => p ≠ 2

/-- Cardinality bound: the number of odd prime discriminant divisors is at most
`primeDiscriminantFactorCount d`. -/
theorem card_oddPrimeDiscriminantDivisors_le (d : ℤ) :
    (oddPrimeDiscriminantDivisors d).card ≤ primeDiscriminantFactorCount d := by
  dsimp [oddPrimeDiscriminantDivisors, primeDiscriminantFactorCount]
  exact Finset.card_filter_le _ _

/-- If the field discriminant is odd, the odd discriminant divisors are all
prime discriminant divisors. -/
theorem oddPrimeDiscriminantDivisors_eq_primeFactors_of_discr_odd
    (d : ℤ) (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0) :
    oddPrimeDiscriminantDivisors d =
      (RingOfIntegers.discrFormula d).natAbs.primeFactors := by
  apply Finset.filter_true_of_mem
  intro p hp hp2
  subst hp2
  have hmem := Nat.mem_primeFactors.mp hp
  have h2dvd_nat : 2 ∣ (RingOfIntegers.discrFormula d).natAbs := hmem.2.1
  have h2dvd_int : (2 : ℤ) ∣ RingOfIntegers.discrFormula d := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast h2dvd_nat
  obtain ⟨k, hk⟩ := h2dvd_int
  apply hodd
  rw [hk]
  omega

/-- In the odd field-discriminant branch, the number of odd discriminant divisors
is exactly the genus-theory prime-discriminant count. -/
theorem card_oddPrimeDiscriminantDivisors_eq_primeDiscriminantFactorCount_of_discr_odd
    (d : ℤ) (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0) :
    (oddPrimeDiscriminantDivisors d).card = primeDiscriminantFactorCount d := by
  rw [oddPrimeDiscriminantDivisors_eq_primeFactors_of_discr_odd d hodd]
  rfl

/-- Characterization of membership in `oddPrimeDiscriminantDivisors`. -/
theorem mem_oddPrimeDiscriminantDivisors_iff (d : ℤ) (p : ℕ) :
    p ∈ oddPrimeDiscriminantDivisors d ↔
      p ∈ ((RingOfIntegers.discrFormula d).natAbs.primeFactors) ∧ p ≠ 2 :=
  Finset.mem_filter

/-- Members of `oddPrimeDiscriminantDivisors d` are prime. -/
theorem prime_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) : Nat.Prime p :=
  Nat.prime_of_mem_primeFactors ((Finset.mem_filter.mp hp).left)

/-- Members of `oddPrimeDiscriminantDivisors d` are not `2`. -/
theorem ne_two_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) : p ≠ 2 :=
  (Finset.mem_filter.mp hp).right

/-- Members of `oddPrimeDiscriminantDivisors d` divide the discriminant formula. -/
theorem dvd_discr_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) :
    (p : ℤ) ∣ RingOfIntegers.discrFormula d := by
  have hmem := (Finset.mem_filter.mp hp).left
  have hmem' := Nat.mem_primeFactors.mp hmem
  have hdvd : p ∣ (RingOfIntegers.discrFormula d).natAbs := hmem'.2.1
  rw [← Int.dvd_natAbs]
  exact mod_cast hdvd

/-! ## Genus characters at odd primes

At each odd prime `p` dividing the discriminant, the genus character
`χ_p : Cl(K) → {±1}` sends an ideal class represented by an ideal `I` coprime to `p`
to `legendreSym p (absNorm I)`. The value is independent of the choice of ideal
representative because the norm of a principal ideal `(α)` coprime to `p` is a
quadratic residue modulo `p` when `p` ramifies in `ℚ(√d)`. -/

/-- Raw genus character at an odd prime `p` dividing the discriminant, defined on
ideals of `𝓞(ℚ(√d))`. For an ideal `I`, returns `legendreSym p (absNorm I)`.
This is multiplicative in `I` via `legendreSym.mul`. -/
noncomputable def genusCharacterRaw (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ)
    [Fact p.Prime] (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ :=
  legendreSym p (Ideal.absNorm I : ℤ)

/-- The raw genus character is multiplicative: `χ_p(I·J) = χ_p(I)·χ_p(J)`. -/
theorem genusCharacterRaw_mul
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I J : Ideal (𝓞 (Qsqrtd (d : ℚ)))) :
    genusCharacterRaw d p (I * J) = genusCharacterRaw d p I * genusCharacterRaw d p J := by
  dsimp [genusCharacterRaw]
  rw [Ideal.absNorm.map_mul, Nat.cast_mul, legendreSym.mul]

/-- If `p` does not divide the absolute norm of `I`, the raw genus character is
nonzero. -/
theorem genusCharacterRaw_ne_zero_of_norm_not_dvd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I : Ideal (𝓞 (Qsqrtd (d : ℚ))))
    (hp_norm : ¬ (p : ℤ) ∣ (Ideal.absNorm I : ℤ)) :
    genusCharacterRaw d p I ≠ 0 := by
  dsimp [genusCharacterRaw]
  rw [legendreSym.eq_zero_iff]
  intro hzero
  exact hp_norm ((ZMod.intCast_zmod_eq_zero_iff_dvd (Ideal.absNorm I : ℤ) p).mp hzero)

/-- If `p` does not divide the absolute norm of `I`, the raw genus character has
order dividing two. -/
theorem genusCharacterRaw_sq_eq_one_of_norm_not_dvd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I : Ideal (𝓞 (Qsqrtd (d : ℚ))))
    (hp_norm : ¬ (p : ℤ) ∣ (Ideal.absNorm I : ℤ)) :
    genusCharacterRaw d p I ^ 2 = 1 := by
  dsimp [genusCharacterRaw]
  have hnorm_ne : (((Ideal.absNorm I : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hp_norm ((ZMod.intCast_zmod_eq_zero_iff_dvd (Ideal.absNorm I : ℤ) p).mp hzero)
  exact legendreSym.sq_one p hnorm_ne

/-- The unit ideal has absolute norm prime to any rational prime `p`. -/
theorem not_dvd_absNorm_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    ¬ (p : ℤ) ∣ (Ideal.absNorm (1 : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ) := by
  simpa [Ideal.absNorm_top] using
    (show ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ) by
      exact_mod_cast (Nat.Prime.not_dvd_one (Fact.out : p.Prime)))

/-- Ideals whose absolute norms are prime to `p` are closed under multiplication. -/
theorem not_dvd_absNorm_mul_of_not_dvd_absNorm
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    {I J : Ideal (𝓞 (Qsqrtd (d : ℚ)))}
    (hI : ¬ (p : ℤ) ∣ (Ideal.absNorm I : ℤ))
    (hJ : ¬ (p : ℤ) ∣ (Ideal.absNorm J : ℤ)) :
    ¬ (p : ℤ) ∣ (Ideal.absNorm (I * J) : ℤ) := by
  intro hmul
  have hmul_nat : p ∣ Ideal.absNorm I * Ideal.absNorm J := by
    have hmul' : (p : ℤ) ∣ ((Ideal.absNorm I * Ideal.absNorm J : ℕ) : ℤ) := by
      simpa [Ideal.absNorm.map_mul, Nat.cast_mul] using hmul
    exact_mod_cast hmul'
  rcases (Fact.out : p.Prime).dvd_mul.mp hmul_nat with hpI | hpJ
  · exact hI (by exact_mod_cast hpI)
  · exact hJ (by exact_mod_cast hpJ)

/-- Ideals of `𝓞(ℚ(√d))` whose absolute norm is prime to `p`, as a multiplicative
submonoid. This is the honest domain on which the raw genus character takes
values in the integer units. -/
def idealsPrimeToNormSubmonoid
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    Submonoid (Ideal (𝓞 (Qsqrtd (d : ℚ)))) where
  carrier := {I | ¬ (p : ℤ) ∣ (Ideal.absNorm I : ℤ)}
  one_mem' := not_dvd_absNorm_one d p
  mul_mem' := by
    intro I J hI hJ
    exact not_dvd_absNorm_mul_of_not_dvd_absNorm d p hI hJ

/-- Membership in the prime-to-norm ideal submonoid can be checked as
coprimality of the absolute norm with `p`. This is the shape used by many
mathlib ideal-theoretic APIs. -/
theorem mem_idealsPrimeToNormSubmonoid_iff_absNorm_coprime
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) :
    I ∈ idealsPrimeToNormSubmonoid d p ↔ (Ideal.absNorm I).Coprime p := by
  dsimp [idealsPrimeToNormSubmonoid]
  constructor
  · intro hI
    rw [Nat.coprime_comm]
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by
      intro hp
      exact hI (by exact_mod_cast hp))
  · intro hI hp
    have hp_nat : p ∣ Ideal.absNorm I := by
      exact_mod_cast hp
    rw [Nat.coprime_comm] at hI
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hI) hp_nat

/-- The raw genus character, restricted to ideals whose norm is prime to `p`,
as an integer unit. The inverse is the same value because the character squares
to `1` on this domain. -/
noncomputable def genusCharacterRawUnit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I : idealsPrimeToNormSubmonoid d p) : ℤˣ :=
  let x := genusCharacterRaw d p (I : Ideal (𝓞 (Qsqrtd (d : ℚ))))
  { val := x
    inv := x
    val_inv := by
      simpa [x, pow_two] using genusCharacterRaw_sq_eq_one_of_norm_not_dvd d p I I.2
    inv_val := by
      simpa [x, pow_two] using genusCharacterRaw_sq_eq_one_of_norm_not_dvd d p I I.2 }

/-- The raw genus character as a monoid homomorphism on ideals whose absolute
norm is prime to `p`. This records the multiplicative part of genus theory before
quotienting by principal ideals. -/
noncomputable def genusCharacterRawOnPrimeToNormIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    idealsPrimeToNormSubmonoid d p →* ℤˣ where
  toFun I := genusCharacterRawUnit d p I
  map_one' := by
    ext
    simp [genusCharacterRawUnit, genusCharacterRaw, Ideal.absNorm_top, legendreSym.at_one]
  map_mul' I J := by
    ext
    exact genusCharacterRaw_mul d p (I : Ideal (𝓞 (Qsqrtd (d : ℚ))))
      (J : Ideal (𝓞 (Qsqrtd (d : ℚ))))

/-- If `p` does not divide the absolute norm of an ideal, then the ideal is nonzero. -/
theorem mem_nonZeroDivisors_of_not_dvd_absNorm
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    {I : Ideal (𝓞 (Qsqrtd (d : ℚ)))}
    (hI : ¬ (p : ℤ) ∣ (Ideal.absNorm I : ℤ)) :
    I ∈ (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  exact hI (by simp [hzero, Ideal.absNorm_bot])

/-- The forgetful monoid hom from ideals with norm prime to `p` to nonzero ideals. -/
def primeToNormIdealNonzeroMonoidHom
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    idealsPrimeToNormSubmonoid d p →* (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰ where
  toFun I := ⟨I, mem_nonZeroDivisors_of_not_dvd_absNorm d p I.2⟩
  map_one' := by
    ext
    rfl
  map_mul' I J := by
    ext
    rfl

/-- The class-group map restricted to ideals whose absolute norm is prime to `p`. -/
noncomputable def mk0OnPrimeToNormIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    idealsPrimeToNormSubmonoid d p →* ClassGroup (𝓞 (Qsqrtd (d : ℚ))) :=
  ClassGroup.mk0.comp (primeToNormIdealNonzeroMonoidHom d p)

/-- The raw genus character descends along the restricted `mk0` map if it is constant
on the fibers of `mk0OnPrimeToNormIdeals`. -/
def genusCharacterRawDescendsOnPrimeToNormIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ I J : idealsPrimeToNormSubmonoid d p,
    mk0OnPrimeToNormIdeals d p I = mk0OnPrimeToNormIdeals d p J →
      genusCharacterRawUnit d p I = genusCharacterRawUnit d p J

/-- Principal-multiplier data sufficient for the raw genus character to descend along
`mk0OnPrimeToNormIdeals`: whenever two prime-to-`p` integral ideals have the same
class, they can be related by principal multipliers whose norms are also prime to `p`. -/
def HasPrimeToNormPrincipalMultiplierData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ I J : idealsPrimeToNormSubmonoid d p,
    mk0OnPrimeToNormIdeals d p I = mk0OnPrimeToNormIdeals d p J →
      ∃ x y : 𝓞 (Qsqrtd (d : ℚ)),
        ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {x}) : ℤ) ∧
        ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {y}) : ℤ) ∧
        Ideal.span {x} * (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) =
          Ideal.span {y} * (J : Ideal (𝓞 (Qsqrtd (d : ℚ))))

/-- If the restricted `mk0` map is surjective and the raw genus character is constant
on its fibers, then the raw genus character induces a genuine class-group character. -/
noncomputable def genusCharacterOfPrimeToNormDescent
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hsurj : Function.Surjective (mk0OnPrimeToNormIdeals d p))
    (hdesc : genusCharacterRawDescendsOnPrimeToNormIdeals d p) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* ℤˣ where
  toFun C := genusCharacterRawUnit d p (Classical.choose (hsurj C))
  map_one' := by
    have hmk : mk0OnPrimeToNormIdeals d p (Classical.choose (hsurj 1)) =
        mk0OnPrimeToNormIdeals d p 1 := by
      rw [Classical.choose_spec (hsurj 1)]
      simp
    calc
      genusCharacterRawUnit d p (Classical.choose (hsurj 1)) =
          genusCharacterRawUnit d p 1 :=
        hdesc (Classical.choose (hsurj 1)) 1 hmk
      _ = 1 := by
        exact map_one (genusCharacterRawOnPrimeToNormIdeals d p)
  map_mul' C D := by
    have hmk : mk0OnPrimeToNormIdeals d p (Classical.choose (hsurj (C * D))) =
        mk0OnPrimeToNormIdeals d p
          (Classical.choose (hsurj C) * Classical.choose (hsurj D)) := by
      rw [Classical.choose_spec (hsurj (C * D))]
      rw [map_mul]
      rw [Classical.choose_spec (hsurj C), Classical.choose_spec (hsurj D)]
    calc
      genusCharacterRawUnit d p (Classical.choose (hsurj (C * D))) =
          genusCharacterRawUnit d p
            (Classical.choose (hsurj C) * Classical.choose (hsurj D)) :=
        hdesc (Classical.choose (hsurj (C * D)))
          (Classical.choose (hsurj C) * Classical.choose (hsurj D)) hmk
      _ = genusCharacterRawUnit d p (Classical.choose (hsurj C)) *
          genusCharacterRawUnit d p (Classical.choose (hsurj D)) := by
        exact map_mul (genusCharacterRawOnPrimeToNormIdeals d p)
          (Classical.choose (hsurj C)) (Classical.choose (hsurj D))

/-- The descended genus character agrees with the raw genus character on the
class represented by a prime-to-`p` ideal. -/
theorem genusCharacterOfPrimeToNormDescent_apply_mk0OnPrimeToNormIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hsurj : Function.Surjective (mk0OnPrimeToNormIdeals d p))
    (hdesc : genusCharacterRawDescendsOnPrimeToNormIdeals d p)
    (I : idealsPrimeToNormSubmonoid d p) :
    genusCharacterOfPrimeToNormDescent d p hsurj hdesc (mk0OnPrimeToNormIdeals d p I) =
      genusCharacterRawUnit d p I := by
  exact hdesc (Classical.choose (hsurj (mk0OnPrimeToNormIdeals d p I))) I
    (Classical.choose_spec (hsurj (mk0OnPrimeToNormIdeals d p I)))

/-- From `p ∈ oddPrimeDiscriminantDivisors d` (so `p` is an odd prime), deduce
`(p : ℤ) ∣ d`. For `d % 4 = 1`, `discrFormula d = d` directly. For `d % 4 ≠ 1`,
`discrFormula d = 4*d`; since `p` is an odd prime, `p ∤ 4`, so `p ∣ d`. -/
private theorem dvd_param_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ} [Fact p.Prime]
    (hp_mem : p ∈ oddPrimeDiscriminantDivisors d) : (p : ℤ) ∣ d := by
  have hp_ne_two : p ≠ 2 := ne_two_of_mem_oddPrimeDiscriminantDivisors hp_mem
  have hp_prime : Nat.Prime p := Fact.out
  have hp_dvd_disc : (p : ℤ) ∣ RingOfIntegers.discrFormula d :=
    dvd_discr_of_mem_oddPrimeDiscriminantDivisors hp_mem
  by_cases hd4 : d % 4 = 1
  · rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4] at hp_dvd_disc
    exact hp_dvd_disc
  · rw [RingOfIntegers.discrFormula_of_mod_four_ne_one hd4] at hp_dvd_disc
    -- (p:ℤ) ∣ 4*d and p is prime; if p ∣ 4 then p=2, contradiction
    have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
    rcases hp_prime_int.dvd_or_dvd hp_dvd_disc with (h4 | hd')
    · -- (p : ℤ) ∣ 4 → p = 2 in ℕ, contradiction with p ≠ 2
      exfalso
      have hp_dvd_four_nat : p ∣ (4 : ℕ) := by exact_mod_cast h4
      have h_four_eq_two_sq : (4 : ℕ) = (2 : ℕ)^2 := by norm_num
      have hp_dvd_two_sq : p ∣ (2 : ℕ)^2 := by rwa [← h_four_eq_two_sq]
      have hp_dvd_two : p ∣ (2 : ℕ) := hp_prime.dvd_of_dvd_pow hp_dvd_two_sq
      have hp_eq_two : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp hp_dvd_two
      exact hp_ne_two hp_eq_two
    · exact hd'

/-- If `p ∣ d`, the explicit `ℤ[√d]` norm is congruent to `re ^ 2` modulo `p`.
Consequently its Legendre symbol is `1` whenever the norm is not divisible by `p`. -/
theorem legendreSym_zsqrtd_norm_eq_one_of_dvd_param
    {d : ℤ} {p : ℕ} [Fact p.Prime] (hpd : (p : ℤ) ∣ d) (z : Zsqrtd d)
    (hz : ¬ (p : ℤ) ∣ Zsqrtd.norm z) :
    legendreSym p (Zsqrtd.norm z) = 1 := by
  have hnorm_ne : ((Zsqrtd.norm z : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd (Zsqrtd.norm z) p).mp hzero)
  refine (legendreSym.eq_one_iff p hnorm_ne).mpr ?_
  refine ⟨(z.re : ZMod p), ?_⟩
  have hd_zero : ((d : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hpd
  rw [RingOfIntegers.norm_zsqrtd]
  push_cast
  rw [hd_zero]
  ring

/-- If an odd prime `p` divides the half-integral discriminant `1 + 4 * k`, then
the explicit `ℤ[(1+√(1+4k))/2]` norm is a square modulo `p`. Consequently its
Legendre symbol is `1` whenever the norm is not divisible by `p`. -/
theorem legendreSym_zOnePlusSqrtOverTwo_norm_eq_one_of_dvd_discr
    {k : ℤ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : (p : ℤ) ∣ 1 + 4 * k) (z : ZOnePlusSqrtdOverTwo k)
    (hz : ¬ (p : ℤ) ∣ QuadraticAlgebra.norm z) :
    legendreSym p (QuadraticAlgebra.norm z) = 1 := by
  have hnorm_ne : ((QuadraticAlgebra.norm z : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd (QuadraticAlgebra.norm z) p).mp hzero)
  refine (legendreSym.eq_one_iff p hnorm_ne).mpr ?_
  let w : ZMod p := (2 : ZMod p) * (z.re : ZMod p) + (z.im : ZMod p)
  refine ⟨(2 : ZMod p)⁻¹ * w, ?_⟩
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero_of_prime_ne_two p hp2
  have hD : (1 : ZMod p) + 4 * (k : ZMod p) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (1 + 4 * k) p).mpr hpd
    simpa using h
  have hk : (k : ZMod p) * 4 = -1 := by
    linear_combination hD
  rw [RingOfIntegers.norm_zOnePlusSqrtOverTwo]
  push_cast
  field_simp [w, h2]
  ring_nf
  rw [show (z.im : ZMod p) ^ 2 * (k : ZMod p) * 4 =
      ((k : ZMod p) * 4) * (z.im : ZMod p) ^ 2 by ring]
  rw [hk]
  ring

/-- For a principal ideal generated by an algebraic integer whose algebra norm is
nonnegative, the raw genus character at an odd discriminant prime is `1`.

This is the formal bridge from the local coordinate norm computations above to
principal ideals. The remaining imaginary-quadratic input is the positivity of
the algebra norm of a generator. -/
theorem genusCharacterRaw_span_eq_one_of_algebraNorm_nonneg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    {α : 𝓞 (Qsqrtd (d : ℚ))} (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hp_norm : ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {α}) : ℤ)) :
    genusCharacterRaw d p (Ideal.span {α}) = 1 := by
  have hp_param : (p : ℤ) ∣ d := dvd_param_of_mem_oddPrimeDiscriminantDivisors hp_disc
  have hp_ne_two : p ≠ 2 := ne_two_of_mem_oddPrimeDiscriminantDivisors hp_disc
  have h_absnorm_int : (Ideal.absNorm (Ideal.span {α}) : ℤ) = Algebra.norm ℤ α := by
    rw [Ideal.absNorm_span_singleton]
    exact Int.natAbs_of_nonneg hN_nonneg
  have hp_alg_norm : ¬ (p : ℤ) ∣ Algebra.norm ℤ α := by
    intro hdiv
    exact hp_norm (by rwa [h_absnorm_int])
  dsimp [genusCharacterRaw]
  rw [h_absnorm_int]
  by_cases hd4 : d % 4 = 1
  · obtain ⟨k, hk⟩ := exists_k_of_mod_four_eq_one hd4
    subst hk
    rw [RingOfIntegers.algebraNorm_eq_zOnePlusSqrtOverTwo_norm_of_eq
      (d := 1 + 4 * k) k rfl]
    apply legendreSym_zOnePlusSqrtOverTwo_norm_eq_one_of_dvd_discr hp_ne_two
    · simpa using hp_param
    · rw [← RingOfIntegers.algebraNorm_eq_zOnePlusSqrtOverTwo_norm_of_eq
        (d := 1 + 4 * k) k rfl]
      exact hp_alg_norm
  · rw [RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one d hd4]
    apply legendreSym_zsqrtd_norm_eq_one_of_dvd_param
    · exact hp_param
    · rw [← RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one d hd4]
      exact hp_alg_norm

/-- The key well-definedness lemma: for an imaginary quadratic field `ℚ(√d)` (`d < 0`),
an odd prime `p` dividing the discriminant, and a principal ideal `I = (α)` with
`p ∤ absNorm I`, the genus character `χ_p(I)` equals `1`. -/
theorem genusCharacterRaw_eq_one_of_isPrincipal_of_norm_not_dvd_of_neg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    {I : Ideal (𝓞 (Qsqrtd (d : ℚ)))}
    (hI_principal : I.IsPrincipal) (hp_norm : ¬ (p : ℤ) ∣ (Ideal.absNorm I : ℤ)) :
    genusCharacterRaw d p I = 1 := by
  obtain ⟨α, hspan, _⟩ :=
    RingOfIntegers.exists_generator_norm_not_dvd_of_isPrincipal (d := d) hI_principal hp_norm
  have hp_span : ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {α}) : ℤ) := by
    simpa [← hspan] using hp_norm
  rw [hspan]
  exact genusCharacterRaw_span_eq_one_of_algebraNorm_nonneg d p hp_disc
    (RingOfIntegers.algebraNorm_nonneg_of_neg (d := d) hd_neg α) hp_span

/-- Right multiplication by a principal ideal whose norm is prime to `p` does not
change the raw genus character. -/
theorem genusCharacterRaw_mul_isPrincipal_of_norm_not_dvd_of_neg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (I P : Ideal (𝓞 (Qsqrtd (d : ℚ))))
    (hP_principal : P.IsPrincipal) (hp_P : ¬ (p : ℤ) ∣ (Ideal.absNorm P : ℤ)) :
    genusCharacterRaw d p (I * P) = genusCharacterRaw d p I := by
  rw [genusCharacterRaw_mul]
  rw [genusCharacterRaw_eq_one_of_isPrincipal_of_norm_not_dvd_of_neg d p hd_neg hp_disc
    hP_principal hp_P]
  ring

/-- Left multiplication by a principal ideal whose norm is prime to `p` does not
change the raw genus character. -/
theorem genusCharacterRaw_isPrincipal_mul_of_norm_not_dvd_of_neg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (P I : Ideal (𝓞 (Qsqrtd (d : ℚ))))
    (hP_principal : P.IsPrincipal) (hp_P : ¬ (p : ℤ) ∣ (Ideal.absNorm P : ℤ)) :
    genusCharacterRaw d p (P * I) = genusCharacterRaw d p I := by
  rw [mul_comm P I]
  exact genusCharacterRaw_mul_isPrincipal_of_norm_not_dvd_of_neg d p hd_neg hp_disc I P
    hP_principal hp_P

/-- If two ideal representatives become equal after multiplying by principal ideals
whose norms are prime to `p`, then they have the same raw genus character. -/
theorem genusCharacterRaw_eq_of_span_mul_eq_span_mul_of_norm_not_dvd_of_neg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    {I J : Ideal (𝓞 (Qsqrtd (d : ℚ)))} {x y : 𝓞 (Qsqrtd (d : ℚ))}
    (hx : ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {x}) : ℤ))
    (hy : ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {y}) : ℤ))
    (hxy : Ideal.span {x} * I = Ideal.span {y} * J) :
    genusCharacterRaw d p I = genusCharacterRaw d p J := by
  have hleft := genusCharacterRaw_isPrincipal_mul_of_norm_not_dvd_of_neg d p hd_neg hp_disc
    (Ideal.span {x}) I ⟨x, rfl⟩ hx
  have hright := genusCharacterRaw_isPrincipal_mul_of_norm_not_dvd_of_neg d p hd_neg hp_disc
    (Ideal.span {y}) J ⟨y, rfl⟩ hy
  calc
    genusCharacterRaw d p I = genusCharacterRaw d p (Ideal.span {x} * I) := hleft.symm
    _ = genusCharacterRaw d p (Ideal.span {y} * J) := by rw [hxy]
    _ = genusCharacterRaw d p J := hright

/-- Prime-to-`p` principal-multiplier data is enough to make the raw genus character
constant on the fibers of the restricted class-group map. -/
theorem genusCharacterRawDescendsOnPrimeToNormIdeals_of_principalMultiplierData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hdata : HasPrimeToNormPrincipalMultiplierData d p) :
    genusCharacterRawDescendsOnPrimeToNormIdeals d p := by
  intro I J hmk
  obtain ⟨x, y, hx, hy, hxy⟩ := hdata I J hmk
  ext
  exact genusCharacterRaw_eq_of_span_mul_eq_span_mul_of_norm_not_dvd_of_neg d p hd_neg hp_disc
    hx hy hxy

/-- A genuine genus character on the class group, conditional on the two remaining
ideal-avoidance inputs: every class has a representative whose norm is prime to `p`,
and equal classes have prime-to-`p` principal multipliers. -/
noncomputable def genusCharacterOfPrincipalMultiplierData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnPrimeToNormIdeals d p))
    (hdata : HasPrimeToNormPrincipalMultiplierData d p) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* ℤˣ :=
  genusCharacterOfPrimeToNormDescent d p hsurj
    (genusCharacterRawDescendsOnPrimeToNormIdeals_of_principalMultiplierData d p hd_neg hp_disc
      hdata)

/-- The genus character obtained from principal-multiplier descent agrees with
the raw genus character on prime-to-`p` ideal representatives. -/
theorem genusCharacterOfPrincipalMultiplierData_apply_mk0OnPrimeToNormIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnPrimeToNormIdeals d p))
    (hdata : HasPrimeToNormPrincipalMultiplierData d p)
    (I : idealsPrimeToNormSubmonoid d p) :
    genusCharacterOfPrincipalMultiplierData d p hd_neg hp_disc hsurj hdata
        (mk0OnPrimeToNormIdeals d p I) =
      genusCharacterRawUnit d p I := by
  exact genusCharacterOfPrimeToNormDescent_apply_mk0OnPrimeToNormIdeals d p hsurj
    (genusCharacterRawDescendsOnPrimeToNormIdeals_of_principalMultiplierData d p hd_neg hp_disc
      hdata) I

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
principal genus, and the quotient `Cl / Cl²` is the genus quotient. -/
noncomputable def squareClassSubgroup (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Subgroup (ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :=
  (powMonoidHom (α := ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) 2).range

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
  rw [squareClassSubgroup]
  rw [Subgroup.index_range]

/-! ## Squares lie in the principal genus -/

/-- The prime-to-`p` raw genus character takes values of order dividing two. -/
theorem genusCharacterRawUnit_sq_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I : idealsPrimeToNormSubmonoid d p) :
    genusCharacterRawUnit d p I ^ 2 = 1 := by
  ext
  exact genusCharacterRaw_sq_eq_one_of_norm_not_dvd d p I I.2

/-- A descended genus character takes values of order dividing two on every class. -/
theorem genusCharacterOfPrincipalMultiplierData_sq_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnPrimeToNormIdeals d p))
    (hdata : HasPrimeToNormPrincipalMultiplierData d p)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    genusCharacterOfPrincipalMultiplierData d p hd_neg hp_disc hsurj hdata C ^ 2 = 1 := by
  let I := Classical.choose (hsurj C)
  have hI : mk0OnPrimeToNormIdeals d p I = C := Classical.choose_spec (hsurj C)
  have happly := genusCharacterOfPrincipalMultiplierData_apply_mk0OnPrimeToNormIdeals
    d p hd_neg hp_disc hsurj hdata I
  rw [hI] at happly
  rw [happly]
  exact genusCharacterRawUnit_sq_eq_one d p I

/-- Every descended genus character kills the square-class subgroup `Cl²`. This is the
formal `Cl² ⊆ principal genus` direction for the odd-prime genus characters. -/
theorem squareClassSubgroup_le_genusCharacterOfPrincipalMultiplierData_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnPrimeToNormIdeals d p))
    (hdata : HasPrimeToNormPrincipalMultiplierData d p) :
    squareClassSubgroup d ≤
      (genusCharacterOfPrincipalMultiplierData d p hd_neg hp_disc hsurj hdata).ker := by
  intro C hC
  rcases hC with ⟨D, rfl⟩
  rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
  exact genusCharacterOfPrincipalMultiplierData_sq_eq_one d p hd_neg hp_disc hsurj hdata D

/-- A descended odd-prime genus character as a character on the principal-genus
quotient `Cl / Cl²`. -/
noncomputable def genusCharacterOnSquareClassQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnPrimeToNormIdeals d p))
    (hdata : HasPrimeToNormPrincipalMultiplierData d p) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d →* ℤˣ :=
  QuotientGroup.lift (squareClassSubgroup d)
    (genusCharacterOfPrincipalMultiplierData d p hd_neg hp_disc hsurj hdata)
    (squareClassSubgroup_le_genusCharacterOfPrincipalMultiplierData_ker
      d p hd_neg hp_disc hsurj hdata)

/-- The character on `Cl / Cl²` agrees with the descended genus character after
composing with the quotient map. -/
theorem genusCharacterOnSquareClassQuotient_apply
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnPrimeToNormIdeals d p))
    (hdata : HasPrimeToNormPrincipalMultiplierData d p)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    genusCharacterOnSquareClassQuotient d p hd_neg hp_disc hsurj hdata C =
      genusCharacterOfPrincipalMultiplierData d p hd_neg hp_disc hsurj hdata C := by
  rfl

/-- Ideal-avoidance data needed to construct all odd-prime genus characters.

The two fields are the remaining local inputs not supplied by the raw Legendre-symbol
calculation: every class must have a representative whose norm is prime to `p`, and
equal such representatives must have principal multipliers still prime to `p`. -/
structure OddGenusCharacterData (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] where
  /-- Every ideal class has a representative whose norm is prime to `p`. -/
  surjective : ∀ (p : ℕ) [Fact p.Prime], p ∈ oddPrimeDiscriminantDivisors d →
    Function.Surjective (mk0OnPrimeToNormIdeals d p)
  /-- Equal prime-to-`p` representatives have a compatible principal multiplier
  whose norm stays prime to `p`. -/
  principalMultiplier :
    ∀ (p : ℕ) [Fact p.Prime], p ∈ oddPrimeDiscriminantDivisors d →
      HasPrimeToNormPrincipalMultiplierData d p

/-- The product of all odd-prime genus characters on the principal-genus quotient.

The remaining genus-theory relation and independence statements identify the image of
this map with the sign vectors satisfying the single product relation. -/
noncomputable def oddGenusCharacterProductOnSquareClassQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d →*
      ((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) :=
  Pi.monoidHom fun P => by
    haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
    exact genusCharacterOnSquareClassQuotient d P.1 hd_neg P.2
      (hdata.surjective P.1 P.2) (hdata.principalMultiplier P.1 P.2)

/-- The product character evaluates componentwise to the corresponding odd-prime
genus character. -/
theorem oddGenusCharacterProductOnSquareClassQuotient_apply
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d)
    (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) :
    oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = by
      haveI : Fact P.1.Prime := ⟨prime_of_mem_oddPrimeDiscriminantDivisors P.2⟩
      exact genusCharacterOnSquareClassQuotient d P.1 hd_neg P.2
        (hdata.surjective P.1 P.2) (hdata.principalMultiplier P.1 P.2) C := by
  rfl

/-- Product of all coordinates of an odd-prime sign vector. -/
noncomputable def oddGenusSignProductHom (d : ℤ) :
    (((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) →* ℤˣ) where
  toFun v := Finset.univ.prod fun P => v P
  map_one' := by simp
  map_mul' v w := by
    change Finset.univ.prod (fun P => v P * w P) =
      Finset.univ.prod (fun P => v P) * Finset.univ.prod (fun P => w P)
    rw [Finset.prod_mul_distrib]

/-- The subgroup of sign vectors whose component product is `1`. In the odd
fundamental-discriminant branch this is the expected target of the genus-character map:
all odd-prime genus characters satisfy one product relation. -/
noncomputable def oddGenusSignRelationSubgroup (d : ℤ) :
    Subgroup ((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) :=
  (oddGenusSignProductHom d).ker

/-- Membership in the odd-genus sign relation subgroup is the product-one relation. -/
theorem mem_oddGenusSignRelationSubgroup_iff (d : ℤ)
    (v : (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) :
    v ∈ oddGenusSignRelationSubgroup d ↔ Finset.univ.prod (fun P => v P) = 1 :=
  Iff.rfl

/-- If there is at least one odd discriminant divisor, the coordinate-product map
from sign vectors to `ℤˣ` is surjective. -/
theorem oddGenusSignProductHom_surjective_of_nonempty
    (d : ℤ) (hS : (oddPrimeDiscriminantDivisors d).Nonempty) :
    Function.Surjective (oddGenusSignProductHom d) := by
  classical
  obtain ⟨p, hp⟩ := hS
  let P : {p // p ∈ oddPrimeDiscriminantDivisors d} := ⟨p, hp⟩
  intro u
  refine ⟨fun Q => if Q = P then u else 1, ?_⟩
  dsimp [oddGenusSignProductHom]
  rw [Finset.prod_ite_eq']
  simp

/-- The full odd-prime sign-vector space has cardinality `2 ^ #S`, where `S` is
the set of odd discriminant divisors. -/
theorem card_oddGenusSignVectors (d : ℤ) :
    Nat.card ((P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) =
      2 ^ (oddPrimeDiscriminantDivisors d).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  rw [Fintype.card_units_int, Fintype.card_coe]

/-- If the odd discriminant-divisor set is nonempty, the product-one sign
relation subgroup has cardinality `2 ^ (#S - 1)`. -/
theorem card_oddGenusSignRelationSubgroup_of_nonempty
    (d : ℤ) (hS : (oddPrimeDiscriminantDivisors d).Nonempty) :
    Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ ((oddPrimeDiscriminantDivisors d).card - 1) := by
  classical
  have hsurj := oddGenusSignProductHom_surjective_of_nonempty d hS
  have hindex : (oddGenusSignRelationSubgroup d).index = 2 := by
    calc
      (oddGenusSignRelationSubgroup d).index = Nat.card (oddGenusSignProductHom d).range := by
        rw [oddGenusSignRelationSubgroup, Subgroup.index_ker]
      _ = Nat.card (⊤ : Subgroup ℤˣ) := by
        rw [MonoidHom.range_eq_top.mpr hsurj]
      _ = 2 := by
        rw [Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hmul := (oddGenusSignRelationSubgroup d).card_mul_index
  rw [hindex, card_oddGenusSignVectors d] at hmul
  have hcard_pos : 0 < (oddPrimeDiscriminantDivisors d).card := Finset.card_pos.mpr hS
  have hpow : 2 ^ (oddPrimeDiscriminantDivisors d).card =
      2 ^ ((oddPrimeDiscriminantDivisors d).card - 1) * 2 := by
    have hsucc : (oddPrimeDiscriminantDivisors d).card =
        ((oddPrimeDiscriminantDivisors d).card - 1) + 1 := by omega
    calc
      2 ^ (oddPrimeDiscriminantDivisors d).card =
          2 ^ (((oddPrimeDiscriminantDivisors d).card - 1) + 1) := by rw [← hsucc]
      _ = 2 ^ ((oddPrimeDiscriminantDivisors d).card - 1) * 2 := by rw [pow_succ]
  rw [hpow] at hmul
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) hmul

/-- The product-one sign relation subgroup has cardinality `2 ^ (#S - 1)`, also
covering the empty-index case by natural-number subtraction. -/
theorem card_oddGenusSignRelationSubgroup (d : ℤ) :
    Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ ((oddPrimeDiscriminantDivisors d).card - 1) := by
  classical
  by_cases hS : (oddPrimeDiscriminantDivisors d).Nonempty
  · exact card_oddGenusSignRelationSubgroup_of_nonempty d hS
  · have hempty : oddPrimeDiscriminantDivisors d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hrel_top : oddGenusSignRelationSubgroup d = ⊤ := by
      haveI : IsEmpty {p // p ∈ oddPrimeDiscriminantDivisors d} := by
        refine ⟨?_⟩
        intro P
        have hp_empty : P.1 ∈ (∅ : Finset ℕ) := by
          simpa [hempty] using P.property
        simp at hp_empty
      ext v
      simp [oddGenusSignRelationSubgroup, oddGenusSignProductHom]
    rw [hrel_top, Subgroup.card_top, card_oddGenusSignVectors d, hempty]
    norm_num

/-- In the odd field-discriminant branch, the product-one sign relation subgroup
has the genus-theory cardinality `2 ^ (t - 1)`. -/
theorem card_oddGenusSignRelationSubgroup_of_discr_odd
    (d : ℤ) (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0) :
    Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1) := by
  rw [card_oddGenusSignRelationSubgroup,
    card_oddPrimeDiscriminantDivisors_eq_primeDiscriminantFactorCount_of_discr_odd d hodd]

/-- The product-relation assertion for the odd-prime genus characters. This is one
of the remaining genus-theory inputs after constructing the individual characters. -/
def oddGenusProductRelation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d) : Prop :=
  ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
    oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C ∈
      oddGenusSignRelationSubgroup d

/-- The product of the odd-prime genus characters, with codomain restricted to the
single-relation sign subgroup. -/
noncomputable def oddGenusCharacterProductToRelationSubgroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d →*
      oddGenusSignRelationSubgroup d where
  toFun C := ⟨oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C, hrel C⟩
  map_one' := by
    ext P
    simp
  map_mul' C D := by
    ext P
    simp

/-- The relation-subgroup-valued product character forgets to the raw product
character. -/
theorem oddGenusCharacterProductToRelationSubgroup_apply
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) :
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel C :
      (P : {p // p ∈ oddPrimeDiscriminantDivisors d}) → ℤˣ) =
      oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C := by
  rfl

/-- Membership in the kernel of the relation-subgroup-valued product character is
equivalent to every odd-prime genus character being trivial. -/
theorem mem_oddGenusCharacterProductToRelationSubgroup_ker_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) :
    C ∈ (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker ↔
      ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1 := by
  constructor
  · intro hC P
    have hmap : oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel C = 1 := by
      simpa [MonoidHom.mem_ker] using hC
    have hval := congr_arg Subtype.val hmap
    exact congr_fun hval P
  · intro hC
    rw [MonoidHom.mem_ker]
    ext P
    simpa [oddGenusCharacterProductToRelationSubgroup_apply] using hC P

/-- The product character has trivial kernel exactly when the only class whose
odd-prime genus characters are all trivial is the trivial class of `Cl / Cl²`. -/
theorem oddGenusCharacterProductToRelationSubgroup_ker_eq_bot_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata) :
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥ ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1) → C = 1 := by
  constructor
  · intro hker C hC
    have hinj :
        Function.Injective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel) :=
      (MonoidHom.ker_eq_bot_iff
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)).mp hker
    rw [injective_iff_map_eq_one] at hinj
    apply hinj
    ext P
    simpa [oddGenusCharacterProductToRelationSubgroup_apply] using hC P
  · intro h
    apply (MonoidHom.ker_eq_bot_iff
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)).mpr
    rw [injective_iff_map_eq_one]
    intro C hC
    apply h C
    intro P
    have hval := congr_arg Subtype.val hC
    exact congr_fun hval P

/-- Complete odd-discriminant genus-theory data for the current class-group interface.

This bundles the individual odd-prime genus characters, the single product relation,
surjectivity onto the relation subgroup, and the principal-kernel theorem saying that a
class in `Cl / Cl²` with all odd-prime genus characters trivial is itself trivial. -/
structure OddGenusFormulaData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0) where
  /-- Individual odd-prime genus characters. -/
  character : OddGenusCharacterData d
  /-- The single product relation among the odd-prime genus characters. -/
  relation : oddGenusProductRelation d hd_neg character
  /-- Every sign vector satisfying the product relation occurs as an odd genus character. -/
  surjective :
    Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg character relation)
  /-- The principal-kernel theorem for the odd-prime genus characters. -/
  principalKernel :
    ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
      (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
        oddGenusCharacterProductOnSquareClassQuotient d hd_neg character C P = 1) → C = 1

/-- Surjectivity of the odd genus-character product together with trivial product
kernel packages the complete odd genus-formula data. -/
theorem OddGenusFormulaData.of_surjective_of_ker_eq_bot
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hker : (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥) :
    OddGenusFormulaData d hd_neg where
  character := hdata
  relation := hrel
  surjective := hsurj
  principalKernel :=
    (oddGenusCharacterProductToRelationSubgroup_ker_eq_bot_iff d hd_neg hdata hrel).mp hker

/-- Bijectivity of the relation-subgroup-valued odd genus-character product packages
the complete odd genus-formula data. -/
theorem OddGenusFormulaData.of_bijective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij :
      Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    OddGenusFormulaData d hd_neg where
  character := hdata
  relation := hrel
  surjective := hbij.2
  principalKernel := by
    have hker :
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff
        (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)).mpr hbij.1
    exact
      (oddGenusCharacterProductToRelationSubgroup_ker_eq_bot_iff d hd_neg hdata hrel).mp hker

/-- Surjectivity of the relation-subgroup-valued odd genus-character product gives
the genus-theory divisibility needed by the class-number-one sieve. -/
theorem genus_divisibility_of_oddGenusCharacterProduct_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj : Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hcard : Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  let φ : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* oddGenusSignRelationSubgroup d :=
    (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).comp
      (QuotientGroup.mk' (squareClassSubgroup d))
  refine genus_divisibility_of_surjective_quotient d (oddGenusSignRelationSubgroup d)
    hcard φ ?_
  exact hsurj.comp (QuotientGroup.mk'_surjective (squareClassSubgroup d))

/-- In the odd field-discriminant branch, surjectivity of the odd genus-character product
already gives the genus-theory divisibility needed by the class-number-one sieve. -/
theorem genus_divisibility_of_oddGenusCharacterProduct_surjective_of_discr_odd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) :=
  genus_divisibility_of_oddGenusCharacterProduct_surjective d hd_neg hdata hrel hsurj
    (card_oddGenusSignRelationSubgroup_of_discr_odd d hodd)

/-- The standard genus formula for the principal-genus quotient
`Cl(𝓞(ℚ(√d))) / Cl(𝓞(ℚ(√d)))²`: its cardinality is `2 ^ (t - 1)`, where `t` is the
number of prime-discriminant factors. In the literature this is the statement that
`Cl / Cl²` is the genus group and each genus contains exactly `2 ^ (t - 1)` classes,
or equivalently `#Cl[2] = 2 ^ (t - 1)`. -/
def genusFormula (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : Prop :=
  Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
    2 ^ (primeDiscriminantFactorCount d - 1)

/-- The genus formula is equivalent to the corresponding cardinality statement for
the kernel of the square map on the ideal class group. -/
theorem genusFormula_iff_card_powMonoidHom_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    genusFormula d ↔
      Nat.card (powMonoidHom (α := ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) 2).ker =
        2 ^ (primeDiscriminantFactorCount d - 1) := by
  rw [genusFormula, card_squareClassSubgroup_quotient_eq_card_powMonoidHom_ker d]

/-- If the relation-subgroup-valued odd genus-character product is bijective and
the relation subgroup has the expected cardinality, then the standard genus
formula follows. -/
theorem genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij :
      Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hcard : Nat.card (oddGenusSignRelationSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1)) :
    genusFormula d := by
  dsimp [genusFormula]
  rw [← hcard]
  exact Nat.card_congr (Equiv.ofBijective _ hbij)

/-- In the odd field-discriminant branch, bijectivity of the relation-subgroup-valued
odd genus-character product implies the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective_of_discr_odd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij :
      Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d :=
  genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective d hd_neg hdata hrel hbij
    (card_oddGenusSignRelationSubgroup_of_discr_odd d hodd)

/-- In the odd field-discriminant branch, surjectivity of the relation-subgroup-valued
odd genus-character product proves the standard genus formula once the reverse
cardinality inequality for the principal-genus quotient is known. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_card_le
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hle : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) ≤
      Nat.card (oddGenusSignRelationSubgroup d)) :
    genusFormula d := by
  letI := _root_.NumberField.RingOfIntegers.instFintypeClassGroup (Qsqrtd (d : ℚ))
  have htarget_le : Nat.card (oddGenusSignRelationSubgroup d) ≤
      Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) :=
    Nat.card_le_card_of_surjective _ hsurj
  have hcard : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
      Nat.card (oddGenusSignRelationSubgroup d) :=
    le_antisymm hle htarget_le
  dsimp [genusFormula]
  rw [hcard, card_oddGenusSignRelationSubgroup_of_discr_odd d hodd]

/-- In the odd field-discriminant branch, surjectivity and injectivity of the
relation-subgroup-valued odd genus-character product prove the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_injective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hinj :
      Function.Injective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d := by
  exact genusFormula_of_oddGenusCharacterProduct_surjective_of_card_le
    d hd_neg hodd hdata hrel hsurj (Nat.card_le_card_of_injective _ hinj)

/-- In the odd field-discriminant branch, the standard genus formula follows once the
odd genus-character product is surjective and has trivial kernel on `Cl / Cl²`. This
is the kernel form of the principal-genus theorem for the odd-prime characters. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_ker_eq_bot
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hker : (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥) :
    genusFormula d := by
  have hinj :
      Function.Injective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel) :=
    (MonoidHom.ker_eq_bot_iff
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)).mp hker
  exact genusFormula_of_oddGenusCharacterProduct_surjective_of_injective
    d hd_neg hodd hdata hrel hsurj hinj

/-- In the odd field-discriminant branch, once the relation-subgroup-valued odd
genus-character product is surjective, the standard genus formula is equivalent to
triviality of its kernel on `Cl / Cl²`. -/
theorem genusFormula_iff_oddGenusCharacterProduct_ker_eq_bot_of_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d ↔
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥ := by
  constructor
  · intro hgenus
    have hcard :
        Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
          Nat.card (oddGenusSignRelationSubgroup d) := by
      dsimp [genusFormula] at hgenus
      rw [hgenus, card_oddGenusSignRelationSubgroup_of_discr_odd d hodd]
    have hbij :
        Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel) :=
      hsurj.bijective_of_nat_card_le (le_of_eq hcard)
    exact (MonoidHom.ker_eq_bot_iff
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)).mpr hbij.1
  · intro hker
    exact genusFormula_of_oddGenusCharacterProduct_surjective_of_ker_eq_bot
      d hd_neg hodd hdata hrel hsurj hker

/-- In the odd field-discriminant branch, once the relation-subgroup-valued odd
genus-character product is surjective, the standard genus formula is equivalent to
the principal-kernel statement: a class in `Cl / Cl²` whose odd-prime genus characters
are all trivial is itself trivial. -/
theorem genusFormula_iff_oddGenusPrincipalKernel_of_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1) → C = 1 := by
  rw [genusFormula_iff_oddGenusCharacterProduct_ker_eq_bot_of_surjective
    d hd_neg hodd hdata hrel hsurj]
  rw [oddGenusCharacterProductToRelationSubgroup_ker_eq_bot_iff]

/-- In the odd field-discriminant branch, complete odd genus-formula data proves
the standard genus formula. -/
theorem genusFormula_of_oddGenusFormulaData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusFormulaData d hd_neg) :
    genusFormula d :=
  (genusFormula_iff_oddGenusPrincipalKernel_of_surjective d hd_neg hodd
    hdata.character hdata.relation hdata.surjective).2 hdata.principalKernel

/-- For odd fundamental discriminants (`d % 4 = 1`), surjectivity of the
relation-subgroup-valued odd genus-character product proves the standard genus formula
once the reverse cardinality inequality for the principal-genus quotient is known. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hle : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) ≤
      Nat.card (oddGenusSignRelationSubgroup d)) :
    genusFormula d := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_of_oddGenusCharacterProduct_surjective_of_card_le
    d hd_neg hodd hdata hrel hsurj hle

/-- For odd fundamental discriminants (`d % 4 = 1`), the standard genus formula follows
once the odd genus-character product is surjective and has trivial kernel on `Cl / Cl²`. -/
theorem genusFormula_of_oddGenusCharacterProduct_surjective_of_ker_eq_bot_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel))
    (hker : (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥) :
    genusFormula d := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_of_oddGenusCharacterProduct_surjective_of_ker_eq_bot
    d hd_neg hodd hdata hrel hsurj hker

/-- For odd fundamental discriminants (`d % 4 = 1`), once the odd genus-character
product is surjective, the standard genus formula is equivalent to triviality of
its kernel on `Cl / Cl²`. -/
theorem genusFormula_iff_oddGenusCharacterProduct_ker_eq_bot_of_surjective_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d ↔
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel).ker = ⊥ := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_iff_oddGenusCharacterProduct_ker_eq_bot_of_surjective
    d hd_neg hodd hdata hrel hsurj

/-- For odd fundamental discriminants (`d % 4 = 1`), once the odd genus-character
product is surjective, the standard genus formula is equivalent to the principal-kernel
statement for the odd-prime genus characters. -/
theorem genusFormula_iff_oddGenusPrincipalKernel_of_surjective_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hsurj :
      Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d ↔
      ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d,
        (∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          oddGenusCharacterProductOnSquareClassQuotient d hd_neg hdata C P = 1) → C = 1 := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_iff_oddGenusPrincipalKernel_of_surjective
    d hd_neg hodd hdata hrel hsurj

/-- For odd fundamental discriminants (`d % 4 = 1`), complete odd genus-formula data
proves the standard genus formula. -/
theorem genusFormula_of_oddGenusFormulaData_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusFormulaData d hd_neg) :
    genusFormula d := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_of_oddGenusFormulaData d hd_neg hodd hdata

/-- In the odd field-discriminant branch, the existing odd-prime genus-character
interface implies the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij : Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d :=
  genusFormula_of_oddGenusCharacterProductToRelationSubgroup_bijective_of_discr_odd
    d hd_neg hodd hdata hrel hbij

/-- For odd fundamental discriminants (`d % 4 = 1`), the existing odd-prime
genus-character interface implies the standard genus formula. -/
theorem genusFormula_of_oddGenusCharacterData_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd_neg hdata)
    (hbij : Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd_neg hdata hrel)) :
    genusFormula d := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact genusFormula_of_oddGenusCharacterData d hd_neg hodd hdata hrel hbij

/-- If the principal-genus quotient has the standard genus-theory cardinality,
then the standard genus-theory divisibility follows from Lagrange's theorem. -/
theorem genus_divisibility_of_squareClassSubgroup_quotient_card
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcard : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  rw [← hcard]
  simpa [NumberField.classNumber, Subgroup.index_eq_card] using
    (squareClassSubgroup d).index_dvd_card

private theorem nat_eq_one_or_prime_of_squarefree_of_primeFactors_card_le_one {n : ℕ}
    (hsq : Squarefree n) (hcard : n.primeFactors.card ≤ 1) :
    n = 1 ∨ n.Prime := by
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  by_cases hnonempty : n.primeFactors.Nonempty
  · right
    obtain ⟨p, hpmem⟩ := hnonempty
    have huniq : n.primeFactors = {p} := by
      exact Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hpmem, fun q hqmem => (Finset.card_le_one_iff.mp hcard) hqmem hpmem⟩
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hn_eq : n = p := by
      rw [huniq] at hprod
      simpa using hprod.symm
    simpa [hn_eq] using hpprime
  · left
    have hcard0 : n.primeFactors.card = 0 := by
      rwa [Finset.not_nonempty_iff_eq_empty, ← Finset.card_eq_zero] at hnonempty
    have hpf_empty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard0
    rw [hpf_empty] at hprod
    simpa using hprod.symm

private theorem nat_eq_one_or_eq_two_of_squarefree_of_forall_primeFactors_eq_two {n : ℕ}
    (hsq : Squarefree n) (hfactor : ∀ p ∈ n.primeFactors, p = 2) :
    n = 1 ∨ n = 2 := by
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  by_cases hnonempty : n.primeFactors.Nonempty
  · right
    obtain ⟨p, hpmem⟩ := hnonempty
    have huniq : n.primeFactors = {2} := by
      exact Finset.eq_singleton_iff_unique_mem.mpr
        ⟨by simpa [hfactor p hpmem] using hpmem,
          fun q hqmem => hfactor q hqmem⟩
    rw [huniq] at hprod
    simpa using hprod.symm
  · left
    have hcard0 : n.primeFactors.card = 0 := by
      rwa [Finset.not_nonempty_iff_eq_empty, ← Finset.card_eq_zero] at hnonempty
    have hpf_empty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard0
    rw [hpf_empty] at hprod
    simpa using hprod.symm

private theorem two_mem_primeFactors_natAbs_four_mul_of_neg {d : ℤ} (hdneg : d < 0) :
    2 ∈ (4 * d).natAbs.primeFactors := by
  rw [Int.natAbs_mul]
  rw [Nat.mem_primeFactors]
  constructor
  · exact Nat.prime_two
  constructor
  · exact ⟨2 * d.natAbs, by ring⟩
  · exact mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr (by omega))

private theorem mem_primeFactors_natAbs_four_mul_of_mem_primeFactors_natAbs {d : ℤ} {p : ℕ}
    (hp : p ∈ d.natAbs.primeFactors) :
    p ∈ (4 * d).natAbs.primeFactors := by
  rw [Int.natAbs_mul]
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, dvd_mul_of_dvd_right hp.2.1 4, mul_ne_zero (by decide) hp.2.2⟩

private theorem prime_shape_of_mod_four_eq_one
    (d : ℤ) (hsq : Squarefree d) (hdneg : d < 0) (hd4 : d % 4 = 1)
    (hcount : primeDiscriminantFactorCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hcard : d.natAbs.primeFactors.card ≤ 1 := by
    simpa [primeDiscriminantFactorCount, RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
      using hcount
  have hsq_nat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
  rcases nat_eq_one_or_prime_of_squarefree_of_primeFactors_card_le_one hsq_nat hcard with
    h1 | hp
  · left
    omega
  · right
    right
    refine ⟨d.natAbs, hp, ?_, ?_⟩
    · omega
    · omega

private theorem prime_shape_of_mod_four_ne_one
    (d : ℤ) (hsq : Squarefree d) (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (hcount : primeDiscriminantFactorCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hcardD : (4 * d).natAbs.primeFactors.card ≤ 1 := by
    simpa [primeDiscriminantFactorCount, RingOfIntegers.discrFormula_of_mod_four_ne_one hd4]
      using hcount
  have htwoD : 2 ∈ (4 * d).natAbs.primeFactors :=
    two_mem_primeFactors_natAbs_four_mul_of_neg hdneg
  have hfactor : ∀ p ∈ d.natAbs.primeFactors, p = 2 := by
    intro p hp
    exact (Finset.card_le_one_iff.mp hcardD)
      (mem_primeFactors_natAbs_four_mul_of_mem_primeFactors_natAbs hp) htwoD
  have hsq_nat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
  rcases nat_eq_one_or_eq_two_of_squarefree_of_forall_primeFactors_eq_two hsq_nat hfactor with
    h1 | h2
  · left
    omega
  · right
    left
    omega

/-- The elementary arithmetic endpoint of the genus-theory sieve. For squarefree
negative `d`, if the field-discriminant prime-factor count is at most one, then
`d` has the class-number-one prime shape. -/
theorem discriminant_prime_shape_of_primeDiscriminantFactorCount_le_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hcount : primeDiscriminantFactorCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  by_cases hd4 : d % 4 = 1
  · exact prime_shape_of_mod_four_eq_one d (Fact.out : Squarefree d) hd hd4 hcount
  · exact prime_shape_of_mod_four_ne_one d (Fact.out : Squarefree d) hd hd4 hcount

/-- Genus divisibility plus class number one implies the prime-shape conclusion.
This is the reusable interface for the future genus-theory calculation
`2 ^ (t - 1) ∣ h(d)`. -/
theorem discriminant_prime_shape_of_genus_divisibility
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hdiv : 2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)))
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) :=
  discriminant_prime_shape_of_primeDiscriminantFactorCount_le_one d hd
    (primeDiscriminantFactorCount_le_one_of_genus_divisibility d hdiv hclass)

/-- In the odd field-discriminant branch, genus divisibility plus class number one
leaves only the prime-discriminant family. -/
theorem classNumber_eq_one_imp_exists_prime_of_odd_discr_of_genus_divisibility
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdiv : 2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  rcases discriminant_prime_shape_of_genus_divisibility d hd hdiv h with
    hneg1 | hneg2 | hprime
  · exfalso
    subst hneg1
    have hd4 := (RingOfIntegers.discrFormula_odd_iff_mod_four_eq_one (-1)).mp hodd
    norm_num at hd4
  · exfalso
    subst hneg2
    have hd4 := (RingOfIntegers.discrFormula_odd_iff_mod_four_eq_one (-2)).mp hodd
    norm_num at hd4
  · exact hprime

/-- **Genus-theory sieve for class number one.** Assuming the standard genus
cardinality formula `genusFormula d`, if an imaginary quadratic field
`ℚ(√d)` has class number one, then its squarefree parameter has prime shape:
`d = -1`, `d = -2`, or `d = -p` for a rational prime `p ≡ 3 (mod 4)`.

The remaining genus-theory construction is the proof of `genusFormula d`,
namely the cardinality formula for the principal-genus quotient `Cl / Cl²`. -/
theorem classNumber_eq_one_imp_discriminant_prime_shape
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hgenus : genusFormula d)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hdiv : 2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) :=
    genus_divisibility_of_squareClassSubgroup_quotient_card d hgenus
  exact discriminant_prime_shape_of_genus_divisibility d hd hdiv h

/-- In the odd field-discriminant branch, the genus-theory sieve leaves only
the prime-discriminant family: `d = -p` for a rational prime `p ≡ 3 (mod 4)`.

This is the part of Cox Theorem 12.34 where genus theory is used.  The even
field-discriminant branch is handled separately by Landau's reduced-form
classification of the discriminants `-4n` with class number one. -/
theorem classNumber_eq_one_imp_exists_prime_of_odd_discr
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hgenus : genusFormula d)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  exact classNumber_eq_one_imp_exists_prime_of_odd_discr_of_genus_divisibility d hd hodd
    (genus_divisibility_of_squareClassSubgroup_quotient_card d hgenus) h

/-- In the odd field-discriminant branch, surjectivity of the odd-prime genus-character
product already reduces class number one to the prime-discriminant family. -/
theorem classNumber_eq_one_imp_exists_prime_of_oddGenusCharacterProduct_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd hdata)
    (hsurj : Function.Surjective (oddGenusCharacterProductToRelationSubgroup d hd hdata hrel))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) :=
  classNumber_eq_one_imp_exists_prime_of_odd_discr_of_genus_divisibility d hd hodd
    (genus_divisibility_of_oddGenusCharacterProduct_surjective_of_discr_odd
      d hd hodd hdata hrel hsurj) h

/-- In the odd field-discriminant branch, the odd-prime genus-character interface
is enough to reduce class number one to the prime-discriminant family. -/
theorem classNumber_eq_one_imp_exists_prime_of_oddGenusCharacterData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd hdata)
    (hbij : Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd hdata hrel))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) :=
  classNumber_eq_one_imp_exists_prime_of_odd_discr d hd hodd
    (genusFormula_of_oddGenusCharacterData d hd hodd hdata hrel hbij) h

/-- For odd fundamental discriminants (`d % 4 = 1`), the odd-prime genus-character
interface is enough to reduce class number one to the prime-discriminant family. -/
theorem classNumber_eq_one_imp_exists_prime_of_oddGenusCharacterData_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusCharacterData d)
    (hrel : oddGenusProductRelation d hd hdata)
    (hbij : Function.Bijective (oddGenusCharacterProductToRelationSubgroup d hd hdata hrel))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact classNumber_eq_one_imp_exists_prime_of_oddGenusCharacterData
    d hd hodd hdata hrel hbij h

/-- In the odd field-discriminant branch, complete odd genus-formula data is enough
to reduce class number one to the prime-discriminant family. -/
theorem classNumber_eq_one_imp_exists_prime_of_oddGenusFormulaData
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdata : OddGenusFormulaData d hd)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) :=
  classNumber_eq_one_imp_exists_prime_of_odd_discr d hd hodd
    (genusFormula_of_oddGenusFormulaData d hd hodd hdata) h

/-- For odd fundamental discriminants (`d % 4 = 1`), complete odd genus-formula
data reduces class number one to the prime-discriminant family. -/
theorem classNumber_eq_one_imp_exists_prime_of_oddGenusFormulaData_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hd4 : d % 4 = 1)
    (hdata : OddGenusFormulaData d hd)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact classNumber_eq_one_imp_exists_prime_of_oddGenusFormulaData d hd hodd hdata h

end ClassGroup
end QuadraticNumberFields
