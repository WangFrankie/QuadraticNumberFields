/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.ClassGroup.ClassNumber
import QuadraticNumberFields.ClassGroup.GenusTheory.Discriminant
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker

/-!
# Odd-Prime Genus Characters

This file constructs the raw odd-prime genus characters, their absolute-norm-coprime
restriction, and the conditional descent data needed to obtain class-group
characters.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

open RingOfIntegers
open Splitting

local notation "𝓞" => _root_.NumberField.RingOfIntegers

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

local notation "χ" => genusCharacterRaw
-- valuable [GenusCharacterRaw] -- for `χ` notation
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
def absNormCoprimeIdealSubmonoid
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    Submonoid (Ideal (𝓞 (Qsqrtd (d : ℚ)))) where
  carrier := {I | ¬ (p : ℤ) ∣ (Ideal.absNorm I : ℤ)}
  one_mem' := not_dvd_absNorm_one d p
  mul_mem' := by
    intro I J hI hJ
    exact not_dvd_absNorm_mul_of_not_dvd_absNorm d p hI hJ

/-- Membership in the absolute-norm-coprime ideal submonoid can be checked as
coprimality of the absolute norm with `p`. This is the shape used by many
mathlib ideal-theoretic APIs. -/
theorem mem_absNormCoprimeIdealSubmonoid_iff_absNorm_coprime
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) :
    I ∈ absNormCoprimeIdealSubmonoid d p ↔ (Ideal.absNorm I).Coprime p := by
  dsimp [absNormCoprimeIdealSubmonoid]
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

/-- If an ideal is nonzero and coprime to the rational prime ideal `(p)`, then
it lies in the absolute-norm-coprime submonoid used by the raw genus character. -/
theorem mem_absNormCoprimeIdealSubmonoid_of_sup_span_natCast_eq_top
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    {I : Ideal (𝓞 (Qsqrtd (d : ℚ)))}
    (hI_ne : I ≠ ⊥)
    (hcop :
      I ⊔ Ideal.span ({(p : 𝓞 (Qsqrtd (d : ℚ)))} : Set (𝓞 (Qsqrtd (d : ℚ)))) = ⊤) :
    I ∈ absNormCoprimeIdealSubmonoid d p := by
  rw [mem_absNormCoprimeIdealSubmonoid_iff_absNorm_coprime]
  exact Ideal.absNorm_coprime_of_sup_span_natCast_eq_top I p hI_ne hcop

/-- The raw genus character, restricted to ideals whose norm is prime to `p`,
as an integer unit. The inverse is the same value because the character squares
to `1` on this domain. -/
noncomputable def genusCharacterRawUnit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I : absNormCoprimeIdealSubmonoid d p) : ℤˣ :=
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
noncomputable def genusCharacterRawOnAbsNormCoprimeIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    absNormCoprimeIdealSubmonoid d p →* ℤˣ where
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
def absNormCoprimeIdealNonzeroMonoidHom
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    absNormCoprimeIdealSubmonoid d p →* (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰ where
  toFun I := ⟨I, mem_nonZeroDivisors_of_not_dvd_absNorm d p I.2⟩
  map_one' := by
    ext
    rfl
  map_mul' I J := by
    ext
    rfl

/-- The class-group map restricted to ideals whose absolute norm is prime to `p`. -/
noncomputable def mk0OnAbsNormCoprimeIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] :
    absNormCoprimeIdealSubmonoid d p →* ClassGroup (𝓞 (Qsqrtd (d : ℚ))) :=
  ClassGroup.mk0.comp (absNormCoprimeIdealNonzeroMonoidHom d p)

/-- To prove surjectivity of the restricted class-group map, it suffices to
choose, in every class, a nonzero integral ideal representative whose absolute
norm is prime to `p`. -/
theorem mk0OnAbsNormCoprimeIdeals_surjective_of_exists_absNorm_coprime_representative
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hrep : ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))),
      ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
        ClassGroup.mk0 I = C ∧
          ¬ (p : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ)) :
    Function.Surjective (mk0OnAbsNormCoprimeIdeals d p) := by
  intro C
  rcases hrep C with ⟨I, hC, hI⟩
  refine ⟨⟨(I : Ideal (𝓞 (Qsqrtd (d : ℚ)))), hI⟩, ?_⟩
  simpa [mk0OnAbsNormCoprimeIdeals, absNormCoprimeIdealNonzeroMonoidHom] using hC

/-- Equality in the restricted class-group map is exactly the usual principal-multiplier
relation between the underlying nonzero integral ideals.

The remaining approximation content is the extra requirement that the multipliers can
be chosen with norms still prime to `p`. -/
theorem mk0OnAbsNormCoprimeIdeals_eq_iff_exists_principal_multipliers
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I J : absNormCoprimeIdealSubmonoid d p) :
    mk0OnAbsNormCoprimeIdeals d p I = mk0OnAbsNormCoprimeIdeals d p J ↔
      ∃ x y : 𝓞 (Qsqrtd (d : ℚ)), x ≠ 0 ∧ y ≠ 0 ∧
        Ideal.span {x} * (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) =
          Ideal.span {y} * (J : Ideal (𝓞 (Qsqrtd (d : ℚ)))) := by
  constructor
  · intro hmk
    change ClassGroup.mk0 (absNormCoprimeIdealNonzeroMonoidHom d p I) =
      ClassGroup.mk0 (absNormCoprimeIdealNonzeroMonoidHom d p J) at hmk
    rw [ClassGroup.mk0_eq_mk0_iff] at hmk
    rcases hmk with ⟨x, y, hx, hy, hxy⟩
    exact ⟨x, y, hx, hy, hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    change ClassGroup.mk0 (absNormCoprimeIdealNonzeroMonoidHom d p I) =
      ClassGroup.mk0 (absNormCoprimeIdealNonzeroMonoidHom d p J)
    rw [ClassGroup.mk0_eq_mk0_iff]
    exact ⟨x, y, hx, hy, hxy⟩

/-- The raw genus character descends along the restricted `mk0` map if it is constant
on the fibers of `mk0OnAbsNormCoprimeIdeals`. -/
def genusCharacterRawDescendsOnAbsNormCoprimeIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ I J : absNormCoprimeIdealSubmonoid d p,
    mk0OnAbsNormCoprimeIdeals d p I = mk0OnAbsNormCoprimeIdeals d p J →
      genusCharacterRawUnit d p I = genusCharacterRawUnit d p J

/-- If the restricted `mk0` map is surjective and the raw genus character is constant
on its fibers, then the raw genus character induces a genuine class-group character. -/
noncomputable def genusCharacterOfAbsNormCoprimeDescent
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hsurj : Function.Surjective (mk0OnAbsNormCoprimeIdeals d p))
    (hdesc : genusCharacterRawDescendsOnAbsNormCoprimeIdeals d p) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* ℤˣ where
  toFun C := genusCharacterRawUnit d p (Classical.choose (hsurj C))
  map_one' := by
    have hmk : mk0OnAbsNormCoprimeIdeals d p (Classical.choose (hsurj 1)) =
        mk0OnAbsNormCoprimeIdeals d p 1 := by
      rw [Classical.choose_spec (hsurj 1)]
      simp
    calc
      genusCharacterRawUnit d p (Classical.choose (hsurj 1)) =
          genusCharacterRawUnit d p 1 :=
        hdesc (Classical.choose (hsurj 1)) 1 hmk
      _ = 1 := by
        exact map_one (genusCharacterRawOnAbsNormCoprimeIdeals d p)
  map_mul' C D := by
    have hmk : mk0OnAbsNormCoprimeIdeals d p (Classical.choose (hsurj (C * D))) =
        mk0OnAbsNormCoprimeIdeals d p
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
        exact map_mul (genusCharacterRawOnAbsNormCoprimeIdeals d p)
          (Classical.choose (hsurj C)) (Classical.choose (hsurj D))

/-- The descended genus character agrees with the raw genus character on the
class represented by a prime-to-`p` ideal. -/
theorem genusCharacterOfAbsNormCoprimeDescent_apply_mk0OnAbsNormCoprimeIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hsurj : Function.Surjective (mk0OnAbsNormCoprimeIdeals d p))
    (hdesc : genusCharacterRawDescendsOnAbsNormCoprimeIdeals d p)
    (I : absNormCoprimeIdealSubmonoid d p) :
    genusCharacterOfAbsNormCoprimeDescent d p hsurj hdesc (mk0OnAbsNormCoprimeIdeals d p I) =
      genusCharacterRawUnit d p I := by
  exact hdesc (Classical.choose (hsurj (mk0OnAbsNormCoprimeIdeals d p I))) I
    (Classical.choose_spec (hsurj (mk0OnAbsNormCoprimeIdeals d p I)))

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

/-- Principal multipliers with norms prime to `p` are enough to make the raw genus
character constant on the fibers of the restricted class-group map. -/
theorem genusCharacterRawDescendsOnAbsNormCoprimeIdeals_of_principal_multipliers
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hprincipal :
      ∀ I J : absNormCoprimeIdealSubmonoid d p,
        mk0OnAbsNormCoprimeIdeals d p I = mk0OnAbsNormCoprimeIdeals d p J →
          ∃ x y : 𝓞 (Qsqrtd (d : ℚ)),
            ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {x}) : ℤ) ∧
            ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {y}) : ℤ) ∧
            Ideal.span {x} * (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) =
              Ideal.span {y} * (J : Ideal (𝓞 (Qsqrtd (d : ℚ))))) :
    genusCharacterRawDescendsOnAbsNormCoprimeIdeals d p := by
  intro I J hmk
  obtain ⟨x, y, hx, hy, hxy⟩ := hprincipal I J hmk
  ext
  exact genusCharacterRaw_eq_of_span_mul_eq_span_mul_of_norm_not_dvd_of_neg d p hd_neg hp_disc
    hx hy hxy

end ClassGroup
end QuadraticNumberFields
