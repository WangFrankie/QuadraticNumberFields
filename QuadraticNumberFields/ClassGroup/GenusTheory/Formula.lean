/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.QuotientEquiv

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

/-- If the narrow-to-wide kernel has cardinality dividing `2`, then so does the
square-quotient correction kernel. -/
theorem card_narrowSquareQuotientToClassGroup_ker_dvd_two_of_narrowToClassGroup_ker_dvd_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker ∣ 2) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker ∣ 2 :=
  (card_narrowSquareQuotientToClassGroup_ker_dvd_card_narrowToClassGroup_ker d).trans hker

/-- If the narrow-to-wide kernel has cardinality dividing `2`, the correction
factor on square quotients is either trivial or of order `2`. -/
theorem card_narrowSquareQuotientToClassGroup_ker_eq_one_or_eq_two_of_narrowToClassGroup_ker_dvd_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker ∣ 2) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker = 1 ∨
      Nat.card (narrowSquareQuotientToClassGroup d).ker = 2 :=
  (Nat.dvd_prime Nat.prime_two).mp
    (card_narrowSquareQuotientToClassGroup_ker_dvd_two_of_narrowToClassGroup_ker_dvd_two
      d hker)

/-- If the narrow-to-wide kernel has cardinality dividing `2`, nontriviality of
the square-quotient correction kernel identifies the correction factor as `2`. -/
theorem card_narrowSquareQuotientToClassGroup_ker_eq_two_of_narrowToClassGroup_ker_dvd_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker ∣ 2)
    (hne : Nat.card (narrowSquareQuotientToClassGroup d).ker ≠ 1) :
    Nat.card (narrowSquareQuotientToClassGroup d).ker = 2 := by
  rcases
    card_narrowSquareQuotientToClassGroup_ker_eq_one_or_eq_two_of_narrowToClassGroup_ker_dvd_two
      d hker with h | h
  · exact absurd h hne
  · exact h

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

/-- If the narrow-to-wide kernel has cardinality `2` and its nontrivial element
is not a square narrow class, the ordinary square quotient satisfies the
corrected genus formula before dividing by `2`. -/
theorem two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_narrowToClassGroup_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker = 2)
    (hdisj : (Qsqrtd.narrowToClassGroup d).ker ⊓ Subgroup.square (Cl⁺(d)) = ⊥) :
    2 * Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) :=
  two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_two d
    (card_narrowSquareQuotientToClassGroup_ker_eq_two_of_narrowToClassGroup_ker d hker
      hdisj)

/-- If the narrow-to-wide kernel is at most `2` and the square-quotient
correction is nontrivial, the ordinary square quotient satisfies the corrected
genus formula before dividing by `2`. -/
theorem two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_narrowToClassGroup_ker_dvd_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker ∣ 2)
    (hne : Nat.card (narrowSquareQuotientToClassGroup d).ker ≠ 1) :
    2 * Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) :=
  two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_two d
    (card_narrowSquareQuotientToClassGroup_ker_eq_two_of_narrowToClassGroup_ker_dvd_two
      d hker hne)

/-- In the nontrivial correction branch, the ordinary class-group square quotient
has cardinality `2 ^ (t - 2)`, where `t = ramifiedPrimeCount d`. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_two_of_correction_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcor : Nat.card (narrowSquareQuotientToClassGroup d).ker = 2)
    (hcount : 2 ≤ ramifiedPrimeCount d) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 2) := by
  have hmain :=
    two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_two d hcor
  have hpow : 2 ^ (ramifiedPrimeCount d - 1) = 2 * 2 ^ (ramifiedPrimeCount d - 2) := by
    have hs : ramifiedPrimeCount d - 1 = ramifiedPrimeCount d - 2 + 1 := by omega
    rw [hs, pow_succ, mul_comm]
  rw [hpow] at hmain
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmain

/-- If the narrow-to-wide kernel has cardinality `2` and its nontrivial element
is not a square narrow class, the ordinary class-group square quotient has
cardinality `2 ^ (t - 2)`, where `t = ramifiedPrimeCount d`. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_two_of_narrowToClassGroup_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker = 2)
    (hdisj : (Qsqrtd.narrowToClassGroup d).ker ⊓ Subgroup.square (Cl⁺(d)) = ⊥)
    (hcount : 2 ≤ ramifiedPrimeCount d) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 2) :=
  card_classGroupSquareQuotient_eq_two_pow_sub_two_of_correction_eq_two d
    (card_narrowSquareQuotientToClassGroup_ker_eq_two_of_narrowToClassGroup_ker d hker
      hdisj)
    hcount

/-- If the narrow-to-wide kernel is at most `2` and the square-quotient
correction is nontrivial, the ordinary class-group square quotient has
cardinality `2 ^ (t - 2)`, where `t = ramifiedPrimeCount d`. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_two_of_narrowToClassGroup_ker_dvd_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hker : Nat.card (Qsqrtd.narrowToClassGroup d).ker ∣ 2)
    (hne : Nat.card (narrowSquareQuotientToClassGroup d).ker ≠ 1)
    (hcount : 2 ≤ ramifiedPrimeCount d) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 2) :=
  card_classGroupSquareQuotient_eq_two_pow_sub_two_of_correction_eq_two d
    (card_narrowSquareQuotientToClassGroup_ker_eq_two_of_narrowToClassGroup_ker_dvd_two
      d hker hne)
    hcount

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

/-- The narrow two-torsion has cardinality equal to the number of genera. -/
theorem card_narrowClassGroupTwoTorsion_eq_numberOfGenera
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = numberOfGenera d :=
  (card_narrowClassGroupSquareQuotient_eq_card_narrowClassGroupTwoTorsion d).symm

end GenusTheory
end ClassGroup
end QuadraticNumberFields
