/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.QuotientEquiv
import QuadraticNumberFields.ClassGroup.Narrow

/-!
# Genus Formula

This file states the genus formula for the new narrow-class-group genus-theory
layer.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

private noncomputable def powTorsionMulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (n : ℕ) (e : G ≃* H) :
    Subgroup.powTorsion G n ≃* Subgroup.powTorsion H n where
  toFun x := ⟨e x, by
    rw [Subgroup.mem_powTorsion_iff]
    rw [← map_pow, (Subgroup.mem_powTorsion_iff G n x).mp x.2, map_one]⟩
  invFun y := ⟨e.symm y, by
    rw [Subgroup.mem_powTorsion_iff]
    rw [← map_pow, (Subgroup.mem_powTorsion_iff H n y).mp y.2, map_one]⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

private theorem comap_square_eq_square_sup_ker_of_surjective
    {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) (hf : Function.Surjective f) :
    (Subgroup.square H).comap f = Subgroup.square G ⊔ f.ker := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_square] at hx
    rcases hx with ⟨y, hy⟩
    obtain ⟨a, ha⟩ := hf y
    rw [Subgroup.mem_sup]
    refine ⟨a * a, ?_, x * (a * a)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_square]
      exact ⟨a, rfl⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, ha, hy]
      group
    · simp [mul_assoc, mul_left_comm]
  · intro x hx
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_sup] at hx
    rcases hx with ⟨y, hy, z, hz, hxy⟩
    rw [← hxy, map_mul, MonoidHom.mem_ker.mp hz, mul_one]
    exact (Subgroup.mem_square.mp hy).map f

private theorem squareQuotientMap_ker_eq_map_ker_of_surjective
    {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) (hf : Function.Surjective f)
    (hmap : Subgroup.square G ≤ (Subgroup.square H).comap f) :
    (QuotientGroup.map (Subgroup.square G) (Subgroup.square H) f hmap).ker =
      Subgroup.map (QuotientGroup.mk' (Subgroup.square G)) f.ker := by
  rw [QuotientGroup.ker_map]
  rw [comap_square_eq_square_sup_ker_of_surjective f hf]
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

private theorem card_map_mk'_eq_of_inf_square_eq_bot
    {G : Type*} [CommGroup G] (K : Subgroup G)
    (hdisj : K ⊓ Subgroup.square G = ⊥) :
    Nat.card (Subgroup.map (QuotientGroup.mk' (Subgroup.square G)) K) = Nat.card K := by
  let q : G →* G ⧸ Subgroup.square G := QuotientGroup.mk' (Subgroup.square G)
  have hker : (q.subgroupMap K).ker = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hquot : q (x : G) = 1 := congrArg Subtype.val hx
      have hsq : (x : G) ∈ Subgroup.square G := by
        simpa [q] using (QuotientGroup.eq_one_iff (x : G)).mp hquot
      have hxinf : (x : G) ∈ K ⊓ Subgroup.square G := ⟨x.2, hsq⟩
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by simpa [hdisj] using hxinf
      rw [Subgroup.mem_bot] at hxbot
      exact Subtype.ext hxbot
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx]
  exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap K)
    ⟨(MonoidHom.ker_eq_bot_iff (q.subgroupMap K)).mp hker,
      q.subgroupMap_surjective K⟩).toEquiv).symm

/-- The genus formula for quadratic fields, stated on the narrow class group. -/
theorem genusFormula
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    numberOfGenera d = 2 ^ (ramifiedPrimeCount d - 1) :=
  card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one d

/-- If the narrow and ordinary class groups are isomorphic, the ordinary
class-group square quotient satisfies the genus formula. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_of_nonempty_narrowMulEquivClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : Nonempty (Cl⁺(d) ≃* Cl(d))) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  rcases h with ⟨e⟩
  rw [_root_.ClassGroup.card_squareQuotient_eq_card_twoTorsion]
  rw [← Nat.card_congr (powTorsionMulEquiv 2 e).toEquiv]
  rw [← NarrowClassGroup.card_squareQuotient_eq_card_twoTorsion]
  exact card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one d

/-- For imaginary quadratic fields, the ordinary class-group square quotient
satisfies the genus formula. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_of_neg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  exact card_classGroupSquareQuotient_eq_two_pow_sub_one_of_nonempty_narrowMulEquivClassGroup
    d (Qsqrtd.Imaginary.nonempty_narrowMulEquivClassGroup d hd)

/-- The map on square quotients induced by the natural map `Cl⁺(d) → Cl(d)`. -/
noncomputable def narrowSquareQuotientToClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)) →* Cl(d) ⧸ Subgroup.square (Cl(d)) :=
  QuotientGroup.map (Subgroup.square (Cl⁺(d))) (Subgroup.square (Cl(d)))
    (Qsqrtd.narrowToClassGroup d) (by
      intro C hC
      rw [Subgroup.mem_comap]
      rw [Subgroup.mem_square] at hC ⊢
      rcases hC with ⟨D, rfl⟩
      exact ⟨Qsqrtd.narrowToClassGroup d D, by simp [map_mul]⟩)

@[simp]
theorem narrowSquareQuotientToClassGroup_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (C : Cl⁺(d)) :
    narrowSquareQuotientToClassGroup d
        (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C) =
      QuotientGroup.mk' (Subgroup.square (Cl(d))) (Qsqrtd.narrowToClassGroup d C) :=
  QuotientGroup.map_mk' (Subgroup.square (Cl⁺(d))) (Subgroup.square (Cl(d)))
    (Qsqrtd.narrowToClassGroup d) _ C

/-- The map on square quotients induced by `Cl⁺(d) → Cl(d)` is surjective. -/
theorem narrowSquareQuotientToClassGroup_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (narrowSquareQuotientToClassGroup d) := by
  apply QuotientGroup.map_surjective_of_surjective
  intro C
  obtain ⟨D, hD⟩ := QuotientGroup.mk'_surjective (Subgroup.square (Cl(d))) C
  rcases Qsqrtd.narrowToClassGroup_surjective d D with ⟨Dplus, hDplus⟩
  exact ⟨Dplus, by
    rw [Function.comp_apply, hDplus]
    exact hD⟩

/-- The correction kernel on square quotients is the image of the kernel of
`Cl⁺(d) → Cl(d)` in the narrow square quotient. -/
theorem narrowSquareQuotientToClassGroup_ker_eq_map_narrowToClassGroup_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (narrowSquareQuotientToClassGroup d).ker =
      Subgroup.map (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))))
        (Qsqrtd.narrowToClassGroup d).ker :=
  squareQuotientMap_ker_eq_map_ker_of_surjective
    (Qsqrtd.narrowToClassGroup d) (Qsqrtd.narrowToClassGroup_surjective d) _

/-- The square-quotient correction kernel has cardinality dividing the
narrow-to-wide kernel. -/
theorem card_narrowSquareQuotientToClassGroup_ker_dvd_card_narrowToClassGroup_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotientToClassGroup d).ker ∣
      Nat.card (Qsqrtd.narrowToClassGroup d).ker := by
  rw [narrowSquareQuotientToClassGroup_ker_eq_map_narrowToClassGroup_ker]
  exact Subgroup.card_map_dvd
    (H := (Qsqrtd.narrowToClassGroup d).ker)
    (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))))

/-- The square-quotient correction kernel is also bounded by the realized sign
vectors of the fraction field. -/
theorem card_narrowSquareQuotientToClassGroup_ker_dvd_card_signVectorRange
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotientToClassGroup d).ker ∣
      Nat.card (NarrowClassGroup.signVectorHom
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).range :=
  (card_narrowSquareQuotientToClassGroup_ker_dvd_card_narrowToClassGroup_ker d).trans
    (Qsqrtd.card_narrowToClassGroup_ker_dvd_card_signVectorRange d)

/-- The square-quotient correction kernel is bounded by the sign quotient after
quotienting by the diagonal sign represented by `-1`. -/
theorem card_narrowSquareQuotientToClassGroup_ker_dvd_card_signQuotientModuloNegOne
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotientToClassGroup d).ker ∣
      Nat.card (NarrowClassGroup.signQuotientModuloNegOne
        (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :=
  (card_narrowSquareQuotientToClassGroup_ker_dvd_card_narrowToClassGroup_ker d).trans
    (Qsqrtd.card_narrowToClassGroup_ker_dvd_card_signQuotientModuloNegOne d)

/-- If the sign quotient modulo the class of `-1` has cardinality dividing `2`,
then so does the square-quotient correction kernel. -/
theorem card_narrowSquareQuotientToClassGroup_ker_dvd_two_of_signQuotient_dvd_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hsign : Nat.card (NarrowClassGroup.signQuotientModuloNegOne
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∣ 2) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker ∣ 2 :=
  (card_narrowSquareQuotientToClassGroup_ker_dvd_card_signQuotientModuloNegOne d).trans
    hsign

/-- If the sign quotient modulo the class of `-1` has cardinality dividing `2`,
the correction factor on square quotients is either trivial or of order `2`. -/
theorem card_narrowSquareQuotientToClassGroup_ker_eq_one_or_eq_two_of_signQuotient_dvd_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hsign : Nat.card (NarrowClassGroup.signQuotientModuloNegOne
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∣ 2) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker = 1 ∨
      Nat.card (narrowSquareQuotientToClassGroup d).ker = 2 :=
  (Nat.dvd_prime Nat.prime_two).mp
    (card_narrowSquareQuotientToClassGroup_ker_dvd_two_of_signQuotient_dvd_two
      d hsign)

/-- If the sign quotient modulo the class of `-1` has cardinality dividing `2`,
nontriviality of the square-quotient correction kernel identifies the correction
factor as `2`. -/
theorem card_narrowSquareQuotientToClassGroup_ker_eq_two_of_signQuotient_dvd_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hsign : Nat.card (NarrowClassGroup.signQuotientModuloNegOne
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∣ 2)
    (hne : Nat.card (narrowSquareQuotientToClassGroup d).ker ≠ 1) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker = 2 := by
  rcases
    card_narrowSquareQuotientToClassGroup_ker_eq_one_or_eq_two_of_signQuotient_dvd_two
      d hsign with h | h
  · exact absurd h hne
  · exact h

/-- For positive discriminant, the square-quotient correction kernel has
cardinality dividing `2`. -/
theorem card_narrowSquareQuotientToClassGroup_ker_dvd_two_of_pos
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker ∣ 2 :=
  card_narrowSquareQuotientToClassGroup_ker_dvd_two_of_signQuotient_dvd_two d
    (by simp [Qsqrtd.Real.card_signQuotientModuloNegOne_eq_two d hd])

/-- For positive discriminant, the square-quotient correction factor is either
trivial or of order `2`. -/
theorem card_narrowSquareQuotientToClassGroup_ker_eq_one_or_eq_two_of_pos
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker = 1 ∨
      Nat.card (narrowSquareQuotientToClassGroup d).ker = 2 :=
  (Nat.dvd_prime Nat.prime_two).mp
    (card_narrowSquareQuotientToClassGroup_ker_dvd_two_of_pos d hd)

/-- If no nontrivial element of `ker(Cl⁺(d) → Cl(d))` is a square in `Cl⁺(d)`,
then the square-quotient correction has the same cardinality as the
narrow-to-wide kernel. -/
theorem card_narrowSquareQuotientToClassGroup_ker_eq_card_narrowToClassGroup_ker_of_disjoint_square
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hdisj : (Qsqrtd.narrowToClassGroup d).ker ⊓ Subgroup.square (Cl⁺(d)) = ⊥) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker =
      Nat.card (Qsqrtd.narrowToClassGroup d).ker := by
  rw [narrowSquareQuotientToClassGroup_ker_eq_map_narrowToClassGroup_ker]
  exact card_map_mk'_eq_of_inf_square_eq_bot (Qsqrtd.narrowToClassGroup d).ker hdisj

/-- A `2`-element narrow-to-wide kernel gives correction factor `2` on square
quotients once its nontrivial element is not a square narrow class. -/
theorem card_narrowSquareQuotientToClassGroup_ker_eq_two_of_narrowToClassGroup_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker = 2)
    (hdisj : (Qsqrtd.narrowToClassGroup d).ker ⊓ Subgroup.square (Cl⁺(d)) = ⊥) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker = 2 := by
  rw [card_narrowSquareQuotientToClassGroup_ker_eq_card_narrowToClassGroup_ker_of_disjoint_square
    d hdisj, hker]

private theorem two_pow_sub_one_eq_two_mul_two_pow_sub_two {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
  have hs : n - 1 = n - 2 + 1 := by omega
  rw [hs, pow_succ, mul_comm]

/-- Exact correction formula comparing the narrow and ordinary class-group
square-quotient genus formulas.

The correction term is the kernel of the map
`Cl⁺(d) / Cl⁺(d)^2 → Cl(d) / Cl(d)^2`. The later real-quadratic sign exact
sequence should identify this kernel as trivial or of order `2` in the positive
discriminant branches. -/
theorem card_classGroupSquareQuotient_mul_correction_eq_two_pow_sub_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotientToClassGroup d).ker *
        Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  have hcard := (narrowSquareQuotientToClassGroup d).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (narrowSquareQuotientToClassGroup_surjective d),
    Subgroup.card_top] at hcard
  rw [hcard, card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one]

/-- Division form of the ordinary class-group square-quotient genus formula.

The denominator is the narrow-to-wide correction kernel on square quotients. In
the imaginary case this correction is trivial; in the real case it records the
unit/sign distinction between ordinary and narrow principal ideals. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_div_correction
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) /
        Nat.card (narrowSquareQuotientToClassGroup d).ker := by
  have hmain := card_classGroupSquareQuotient_mul_correction_eq_two_pow_sub_one d
  rw [← hmain]
  rw [Nat.mul_div_right _ (Nat.card_pos :
    0 < Nat.card (narrowSquareQuotientToClassGroup d).ker)]

/-- Division form of the ordinary class-group square-quotient genus formula,
written with the signed prime-discriminant factors.

The factors include the `2`-primary factor `-4`, `8`, or `-8` according to the
usual congruence cases. The only extra term in the ordinary class group is the
narrow-to-wide correction kernel. -/
theorem card_classGroupSquareQuotient_eq_two_pow_signedFactors_card_sub_one_div_correction
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ ((signedPrimeDiscriminantFactors d).card - 1) /
        Nat.card (narrowSquareQuotientToClassGroup d).ker := by
  rw [card_classGroupSquareQuotient_eq_two_pow_sub_one_div_correction,
    card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount]

/-- If the narrow-to-wide map on square quotients has trivial kernel, the ordinary
class-group square quotient has the same genus-formula size as the narrow one. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcor : Nat.card (narrowSquareQuotientToClassGroup d).ker = 1) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  have hmain := card_classGroupSquareQuotient_mul_correction_eq_two_pow_sub_one d
  rw [hcor, one_mul] at hmain
  exact hmain

/-- If the narrow-to-wide map on square quotients has correction factor `2`, the
ordinary square quotient has the expected corrected genus-formula factor. -/
theorem two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcor : Nat.card (narrowSquareQuotientToClassGroup d).ker = 2) :
    2 * Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  calc
    2 * Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
        Nat.card (narrowSquareQuotientToClassGroup d).ker *
          Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) := by rw [hcor]
    _ = 2 ^ (ramifiedPrimeCount d - 1) :=
        card_classGroupSquareQuotient_mul_correction_eq_two_pow_sub_one d

/-- A nontrivial ordinary square-quotient correction can occur only when there
are at least two ramified prime-discriminant factors. -/
theorem two_le_ramifiedPrimeCount_of_correction_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcor : Nat.card (narrowSquareQuotientToClassGroup d).ker = 2) :
    2 ≤ ramifiedPrimeCount d := by
  have hmain :=
    two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_two d hcor
  by_contra hlt
  have hcount : ramifiedPrimeCount d = 1 := by
    have hone := one_le_ramifiedPrimeCount d
    omega
  rw [hcount] at hmain
  norm_num at hmain

/-- In the nontrivial correction branch, the ordinary class-group square quotient
has cardinality `2 ^ (t - 2)`, where `t = ramifiedPrimeCount d`. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_two_of_correction_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcor : Nat.card (narrowSquareQuotientToClassGroup d).ker = 2) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 2) := by
  have hcount := two_le_ramifiedPrimeCount_of_correction_eq_two d hcor
  have hmain :=
    two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_two d hcor
  rw [two_pow_sub_one_eq_two_mul_two_pow_sub_two hcount] at hmain
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmain

/-- In the positive-discriminant branch where the sign correction kernel has
order `2`, the induced ordinary square-quotient correction is trivial, so the
ordinary class-group square quotient keeps the narrow genus-formula size. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_of_signCorrection_ker_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d)
    (hsign : Nat.card
      (NarrowClassGroup.signQuotientModuloNegOneToPrincipalIdealQuotient
        (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))).ker = 2) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  have hprod := Qsqrtd.Real.card_signCorrection_ker_mul_card_narrowToClassGroup_ker_eq_two
    d hd
  have hnarrow : Nat.card (Qsqrtd.narrowToClassGroup d).ker = 1 := by
    rw [hsign] at hprod
    omega
  have hdvd := card_narrowSquareQuotientToClassGroup_ker_dvd_card_narrowToClassGroup_ker d
  have hcor : Nat.card (narrowSquareQuotientToClassGroup d).ker = 1 := by
    rw [hnarrow] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  have hmain := card_classGroupSquareQuotient_mul_correction_eq_two_pow_sub_one d
  rw [hcor, one_mul] at hmain
  exact hmain

/-- In the real quadratic branch, a negative-norm integral unit removes the
narrow-to-wide correction, so the ordinary square quotient keeps the narrow
genus-formula size. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_of_pos_of_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d)
    (hnegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) :=
  card_classGroupSquareQuotient_eq_two_pow_sub_one_of_signCorrection_ker_eq_two d hd
    (Qsqrtd.Real.card_signCorrection_ker_eq_two_of_negative_norm_unit d hd hnegUnit)

/-- In the positive-discriminant branch, the ordinary square quotient has one of
the two sign-corrected genus-theory sizes. The finite prime-discriminant part is
`ramifiedPrimeCount d`; the remaining distinction is the narrow-to-wide sign
correction, not another `2`-adic ramification case. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_or_eq_two_pow_sub_two_of_pos
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
        2 ^ (ramifiedPrimeCount d - 1) ∨
      Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
        2 ^ (ramifiedPrimeCount d - 2) := by
  rcases card_narrowSquareQuotientToClassGroup_ker_eq_one_or_eq_two_of_pos d hd with
    hcor | hcor
  · exact Or.inl (card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_one d hcor)
  · exact Or.inr (card_classGroupSquareQuotient_eq_two_pow_sub_two_of_correction_eq_two
      d hcor)

/-- For every quadratic field in this family, the ordinary class-group square
quotient has one of the two sign-corrected genus-theory sizes.

The finite prime-discriminant count is uniform; only the narrow-to-wide
correction can reduce the ordinary quotient by one factor of `2`. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_or_eq_two_pow_sub_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
        2 ^ (ramifiedPrimeCount d - 1) ∨
      Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
        2 ^ (ramifiedPrimeCount d - 2) := by
  by_cases hdneg : d < 0
  · exact Or.inl (card_classGroupSquareQuotient_eq_two_pow_sub_one_of_neg d hdneg)
  · have hd0 : d ≠ 0 := (Fact.out : Squarefree d).ne_zero
    have hdpos : 0 < d := by omega
    exact card_classGroupSquareQuotient_eq_two_pow_sub_one_or_eq_two_pow_sub_two_of_pos
      d hdpos

/-- The ordinary class-group square quotient has one of the two sign-corrected
genus-theory sizes, written in terms of signed prime-discriminant factors.

These factors encode the finite congruence split, including the `2`-primary
cases `-4`, `8`, and `-8`; the remaining alternative is only the narrow-to-wide
sign correction. -/
theorem card_classGroupSquareQuotient_eq_two_pow_signedFactors_card_sub_one_or_sub_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
        2 ^ ((signedPrimeDiscriminantFactors d).card - 1) ∨
      Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
        2 ^ ((signedPrimeDiscriminantFactors d).card - 2) := by
  rw [card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount]
  exact card_classGroupSquareQuotient_eq_two_pow_sub_one_or_eq_two_pow_sub_two d

/-- The genus formula is equivalent to the principal-genus kernel statement for the
genus-character map. -/
theorem genusFormula_iff_genusCharacterMap_ker_eq_square
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    numberOfGenera d = 2 ^ (ramifiedPrimeCount d - 1) ↔
      (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d)) := by
  constructor
  · intro _
    apply (genusCharacterMapOnSquareQuotient_ker_eq_bot_iff d).mp
    exact (MonoidHom.ker_eq_bot_iff (genusCharacterMapOnSquareQuotient d)).mpr
      (genusQuotientEquiv d).injective
  · intro _
    exact genusFormula d

/-- The square-disjoint condition for `ker(Cl⁺(d) → Cl(d))` is equivalent to
genus characters detecting that kernel. This is the group-theoretic form of the
remaining positive-discriminant correction input. -/
theorem narrowToClassGroup_ker_inf_square_eq_bot_iff_genusCharacterMap_subgroupMap_injective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (Qsqrtd.narrowToClassGroup d).ker ⊓ Subgroup.square (Cl⁺(d)) = ⊥ ↔
      Function.Injective
        ((genusCharacterMap d).subgroupMap (Qsqrtd.narrowToClassGroup d).ker) := by
  let K := (Qsqrtd.narrowToClassGroup d).ker
  change K ⊓ Subgroup.square (Cl⁺(d)) = ⊥ ↔
    Function.Injective ((genusCharacterMap d).subgroupMap K)
  have hsq : (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d)) :=
    (genusFormula_iff_genusCharacterMap_ker_eq_square d).mp (genusFormula d)
  rw [← hsq, ← MonoidHom.ker_eq_bot_iff]
  constructor
  · intro hdisj
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxφ : genusCharacterMap d (x : Cl⁺(d)) = 1 := congrArg Subtype.val hx
      have hxinf : (x : Cl⁺(d)) ∈ K ⊓ (genusCharacterMap d).ker := by
        exact ⟨x.2, hxφ⟩
      have hxbot : (x : Cl⁺(d)) ∈ (⊥ : Subgroup (Cl⁺(d))) := by
        simpa [hdisj] using hxinf
      rw [Subgroup.mem_bot] at hxbot
      exact Subtype.ext hxbot
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx]
  · intro hker
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_bot]
      have hxker : (⟨x, hx.1⟩ : K) ∈ ((genusCharacterMap d).subgroupMap K).ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext (MonoidHom.mem_ker.mp hx.2)
      have hxbot : (⟨x, hx.1⟩ : K) ∈ (⊥ : Subgroup K) := by
        simpa [hker] using hxker
      rw [Subgroup.mem_bot] at hxbot
      exact congrArg Subtype.val hxbot
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx]

/-- In the real no-negative-unit branch, the explicit ordinary-principal narrow
kernel class generated by `√d` is not a square in the narrow class group.

This is the direct square-quotient form of the ordinary/narrow sign correction:
the canonical real narrow/wide correction class survives in `Cl⁺(d) / Cl⁺(d)^2`. -/
theorem sqrtdPrincipalNarrowClassKer_not_mem_square_of_no_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    (Qsqrtd.Real.sqrtdPrincipalNarrowClassKer d : Cl⁺(d)) ∉
      Subgroup.square (Cl⁺(d)) := by
  sorry

/-- In the real no-negative-unit branch, the narrow-to-wide kernel is disjoint
from the square subgroup of the narrow class group. -/
theorem narrowToClassGroup_ker_inf_square_eq_bot_of_no_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    (Qsqrtd.narrowToClassGroup d).ker ⊓ Subgroup.square (Cl⁺(d)) = ⊥ := by
  let K := (Qsqrtd.narrowToClassGroup d).ker
  let S : Subgroup (Cl⁺(d)) := K ⊓ Subgroup.square (Cl⁺(d))
  have hsqrtd_not_square :=
    sqrtdPrincipalNarrowClassKer_not_mem_square_of_no_negative_norm_unit d hd hnoNegUnit
  have hKcard : Nat.card K = 2 :=
    Qsqrtd.Real.card_narrowToClassGroup_ker_eq_two_of_no_negative_norm_unit
      d hd hnoNegUnit
  have hS_le_K : S ≤ K := fun x hx => hx.1
  have hS_card_equiv : Nat.card (S.subgroupOf K) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le_K).toEquiv
  by_contra hS_ne_bot
  have hS_card_ne_one : Nat.card S ≠ 1 := by
    intro hS_card
    have hsub : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hS_card).1
    have hS_eq_bot : S = ⊥ := by
      ext x
      constructor
      · intro hx
        have hx_eq_one : (⟨x, hx⟩ : S) = 1 := Subsingleton.elim _ _
        simpa [Subgroup.mem_bot] using congrArg Subtype.val hx_eq_one
      · intro hx
        rw [Subgroup.mem_bot] at hx
        simp [hx]
    exact hS_ne_bot hS_eq_bot
  have hS_dvd_two : Nat.card S ∣ 2 := by
    rw [← hKcard]
    rw [← hS_card_equiv]
    exact Subgroup.card_subgroup_dvd_card (S.subgroupOf K)
  have hS_card : Nat.card S = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hS_dvd_two with hS_card | hS_card
    · exact False.elim (hS_card_ne_one hS_card)
    · exact hS_card
  have hS_top : S.subgroupOf K = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hS_card_equiv, hS_card, hKcard]
  have hsqrtd_mem_S : (Qsqrtd.Real.sqrtdPrincipalNarrowClassKer d : Cl⁺(d)) ∈ S := by
    have hsqrtd_mem_subgroupOf :
        (Qsqrtd.Real.sqrtdPrincipalNarrowClassKer d : K) ∈ S.subgroupOf K := by
      rw [hS_top]
      exact Subgroup.mem_top _
    simpa [Subgroup.mem_subgroupOf] using hsqrtd_mem_subgroupOf
  exact hsqrtd_not_square hsqrtd_mem_S.2

/- In the positive-discriminant branch where the sign correction kernel is
trivial, disjointness from narrow squares gives the nontrivial ordinary
square-quotient correction factor. -/
private theorem
    card_classGroupSquareQuotient_eq_two_pow_sub_two_of_signCorrection_ker_eq_one_of_disjoint_square
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d)
    (hsign : Nat.card
      (NarrowClassGroup.signQuotientModuloNegOneToPrincipalIdealQuotient
        (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))).ker = 1)
    (hdisj : (Qsqrtd.narrowToClassGroup d).ker ⊓ Subgroup.square (Cl⁺(d)) = ⊥) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 2) := by
  have hprod := Qsqrtd.Real.card_signCorrection_ker_mul_card_narrowToClassGroup_ker_eq_two
    d hd
  have hnarrow : Nat.card (Qsqrtd.narrowToClassGroup d).ker = 2 := by
    rw [hsign, one_mul] at hprod
    exact hprod
  exact card_classGroupSquareQuotient_eq_two_pow_sub_two_of_correction_eq_two d
    (card_narrowSquareQuotientToClassGroup_ker_eq_two_of_narrowToClassGroup_ker d
      hnarrow hdisj)

/- In the real quadratic branch with no negative-norm integral unit, the
sign-correction kernel is trivial and the remaining kernel of `Cl⁺(d) → Cl(d)`
is disjoint from narrow squares, so the ordinary square quotient has the
corrected size `2 ^ (t - 2)`. -/
private theorem card_classGroupSquareQuotient_eq_two_pow_sub_two_of_noNegUnit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 2) :=
  card_classGroupSquareQuotient_eq_two_pow_sub_two_of_signCorrection_ker_eq_one_of_disjoint_square
    d hd (Qsqrtd.Real.card_signCorrection_ker_eq_one_of_no_negative_norm_unit d hd hnoNegUnit)
    (narrowToClassGroup_ker_inf_square_eq_bot_of_no_negative_norm_unit d hd hnoNegUnit)

/-- In the real quadratic branch with no negative-norm integral unit, the
ordinary square quotient has the corrected genus-theory size `2 ^ (t - 2)`. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_two_of_pos_of_no_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 2) :=
  card_classGroupSquareQuotient_eq_two_pow_sub_two_of_noNegUnit d hd hnoNegUnit

/-- No-negative-unit branch of the ordinary square-quotient genus formula,
written with signed prime-discriminant factors. -/
theorem
    card_classGroupSquareQuotient_eq_two_pow_signedFactors_sub_two_of_pos_of_no_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ ((signedPrimeDiscriminantFactors d).card - 2) := by
  rw [card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount]
  exact card_classGroupSquareQuotient_eq_two_pow_sub_two_of_pos_of_no_negative_norm_unit
    d hd hnoNegUnit

/-- The narrow two-torsion has cardinality equal to the number of genera. -/
theorem card_narrowClassGroupTwoTorsion_eq_numberOfGenera
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = numberOfGenera d :=
  (card_narrowClassGroupSquareQuotient_eq_card_narrowClassGroupTwoTorsion d).symm

end GenusTheory
end ClassGroup
end QuadraticNumberFields
