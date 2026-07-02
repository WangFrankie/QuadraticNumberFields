/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.PositivePrincipal.Generators

/-!
# Ramified-Parity Exact Sequence

This file contains the exact-sequence layer used by the ambiguous-ideal upper
bound.  It stays in the quadratic-field setting: the full ramified-parity map is
the homomorphism from `Fin 2`-valued ramified-prime parity vectors to the narrow
class group, and the positive-principal input supplies a nonzero kernel vector.

The main use is the kernel action on full parity products: translating by a
kernel vector does not change the narrow class, so any coordinate in the support
of that vector can be erased.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

/-- If the distinguished coordinate is zero, the full ramified parity ideal
product is literally the erased ramified parity ideal product obtained by
restricting the vector away from that coordinate. -/
theorem fullRamifiedParityIdealProduct_eq_ramifiedParityIdealProduct_of_apply_p0_eq_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hv0 : v ⟨p0, hp0⟩ = 0) :
    fullRamifiedParityIdealProduct d v =
      ramifiedParityIdealProduct d hp0
        (fun p : {p // p ∈ (ramifiedPrimes d).erase p0} =>
          v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let F : {p // p ∈ ramifiedPrimes d} → (Ideal R)⁰ :=
    fun p =>
      if v p = 0 then 1 else
        ⟨ramifiedPrimeIdeal d p.2,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d p.2)⟩
  let G : {p // p ∈ (ramifiedPrimes d).erase p0} → (Ideal R)⁰ :=
    fun p =>
      if v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩ = 0 then 1 else
        ⟨ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2),
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using
              ramifiedPrimeIdeal_ne_bot d ((Finset.mem_erase.mp p.2).2))⟩
  change Finset.univ.prod F = Finset.univ.prod G
  have hterm : F ⟨p0, hp0⟩ = 1 := by
    simp [F, hv0]
  rw [← Finset.prod_erase (s := Finset.univ) (a := ⟨p0, hp0⟩) (f := F) hterm]
  symm
  refine Finset.prod_bij
    (fun p _hp => (⟨p.1, (Finset.mem_erase.mp p.2).2⟩ :
      {p // p ∈ ramifiedPrimes d})) ?_ ?_ ?_ ?_
  · intro p _hp
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hp
    exact (Finset.mem_erase.mp p.2).1 (Subtype.ext_iff.mp hp)
  · intro p _hp q _hq hpq
    apply Subtype.ext
    exact congrArg (fun x : {p // p ∈ ramifiedPrimes d} => (x : ℕ)) hpq
  · intro q hq
    rw [Finset.mem_erase] at hq
    refine ⟨⟨q.1, Finset.mem_erase.mpr ⟨?_, q.2⟩⟩, Finset.mem_univ _, ?_⟩
    · intro hq0
      exact hq.1 (Subtype.ext hq0)
    · apply Subtype.ext
      rfl
  · intro p _hp
    simp [F]

/-- If the distinguished coordinate is zero, the full ramified parity narrow
class product is the erased product obtained by restricting away from that
coordinate. -/
theorem fullRamifiedParityNarrowClassProduct_eq_erased_of_apply_p0_eq_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hv0 : v ⟨p0, hp0⟩ = 0) :
    fullRamifiedParityNarrowClassProduct d v =
      ramifiedParityNarrowClassProduct d hp0
        (fun p : {p // p ∈ (ramifiedPrimes d).erase p0} =>
          v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩) := by
  classical
  let F : {p // p ∈ ramifiedPrimes d} →
      NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
    fun p => if v p = 0 then 1 else ramifiedPrimeNarrowClass d p.2
  let G : {p // p ∈ (ramifiedPrimes d).erase p0} →
      NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
    fun p =>
      if v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩ = 0 then 1 else
        ramifiedPrimeNarrowClass d ((Finset.mem_erase.mp p.2).2)
  change Finset.univ.prod F = Finset.univ.prod G
  have hterm : F ⟨p0, hp0⟩ = 1 := by
    simp [F, hv0]
  rw [← Finset.prod_erase (s := Finset.univ) (a := ⟨p0, hp0⟩) (f := F) hterm]
  symm
  refine Finset.prod_bij
    (fun p _hp => (⟨p.1, (Finset.mem_erase.mp p.2).2⟩ :
      {p // p ∈ ramifiedPrimes d})) ?_ ?_ ?_ ?_
  · intro p _hp
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hp
    exact (Finset.mem_erase.mp p.2).1 (Subtype.ext_iff.mp hp)
  · intro p _hp q _hq hpq
    apply Subtype.ext
    exact congrArg (fun x : {p // p ∈ ramifiedPrimes d} => (x : ℕ)) hpq
  · intro q hq
    rw [Finset.mem_erase] at hq
    refine ⟨⟨q.1, Finset.mem_erase.mpr ⟨?_, q.2⟩⟩, Finset.mem_univ _, ?_⟩
    · intro hq0
      exact hq.1 (Subtype.ext hq0)
    · apply Subtype.ext
      rfl
  · intro p _hp
    simp [F]

/-- In `Fin 2`, two nonzero elements add to zero. -/
theorem fin_two_add_eq_zero_of_ne_zero_of_ne_zero {a b : Fin 2}
    (ha : a ≠ 0) (hb : b ≠ 0) : a + b = 0 := by
  have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
  have hb1 : b = 1 := Fin.eq_one_of_ne_zero b hb
  simp [ha1, hb1]

/-- A full ramified parity vector lies in the kernel of the narrow-class map
exactly when the corresponding integral ideal product is killed by a totally
positive principal fractional ideal. -/
theorem fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker ↔
      ∃ x : (FractionRing R)ˣ,
        NarrowClassGroup.IsTotallyPositive (x : FractionRing R) ∧
          FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) *
            toPrincipalIdeal R (FractionRing R) x = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  rw [fullRamifiedParityNarrowClassHom_mem_ker_iff]
  rw [← mk0_fullRamifiedParityIdealProduct d r]
  exact NarrowClassGroup.mk0_eq_one_iff_exists_fraction_ring

/-- Kernel membership is exactly the translation relation on full ramified
parity products. This is the local exactness statement used to quotient the
full parity space by one nonzero relation. -/
theorem fullRamifiedParityNarrowClassHom_mem_ker_iff_mk0_add_relation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker ↔
      ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
          NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v) := by
  constructor
  · intro hr v
    have hprod :
        fullRamifiedParityNarrowClassProduct d r = 1 :=
      (fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mp hr
    rw [mk0_fullRamifiedParityIdealProduct, mk0_fullRamifiedParityIdealProduct]
    rw [fullRamifiedParityNarrowClassProduct_add, hprod, mul_one]
  · intro hrel
    apply (fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mpr
    have hzero := hrel 0
    rw [mk0_fullRamifiedParityIdealProduct, mk0_fullRamifiedParityIdealProduct] at hzero
    rw [fullRamifiedParityNarrowClassProduct_add,
      fullRamifiedParityNarrowClassProduct_zero, one_mul] at hzero
    simpa [fullRamifiedParityNarrowClassProduct_zero] using hzero

/-- Kernel vectors are exactly full ramified parity products generated by a
totally positive element of the fraction field.

This is the principal-generator form of
`fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal`: the
positive principal multiplier killing the integral product is inverted so that
the generator itself cuts out the ramified parity product. -/
theorem fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_tp_generator
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker ↔
      ∃ γ : (FractionRing R)ˣ,
        NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
          toPrincipalIdeal R (FractionRing R) γ =
            FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  constructor
  · intro hr
    obtain ⟨x, hxpos, hx⟩ :=
      (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mp hr
    refine ⟨x⁻¹, ?_, ?_⟩
    · exact (NarrowClassGroup.totallyPositiveUnits (FractionRing R)).inv_mem hxpos
    · rw [map_inv]
      exact (eq_inv_of_mul_eq_one_left hx).symm
  · rintro ⟨γ, hγpos, hγ⟩
    apply (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mpr
    refine ⟨γ⁻¹, ?_, ?_⟩
    · exact (NarrowClassGroup.totallyPositiveUnits (FractionRing R)).inv_mem hγpos
    · rw [map_inv, hγ, mul_inv_cancel]

/-- Product-form version of
`fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_tp_generator`. -/
theorem fullRamifiedParityNarrowClassProduct_eq_one_iff_exists_tp_generator
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    fullRamifiedParityNarrowClassProduct d r = 1 ↔
      ∃ γ : (FractionRing R)ˣ,
        NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
          toPrincipalIdeal R (FractionRing R) γ =
            FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  rw [← fullRamifiedParityNarrowClassHom_mem_ker_iff]
  exact fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_tp_generator d r

/-- Chevalley's narrow genus relation, in the only form needed for the upper
bound.

This is the genuine global mathematical boundary: the full ramified parity map
has a nonzero kernel vector. Equivalently, the narrow-principal ambiguous ideals
form a codimension-one subspace of the ramified parity space, the `-1` in
`|Am⁺| = 2 ^ (t - 1)`. This statement is uniform in `d`; the witness vector is
not. In particular, the constant-one vector is not a valid uniform shortcut:
the relation depends on the prime-discriminant/sign contribution for `d`. -/
theorem exists_nonzero_fullRamifiedParityNarrowClassHom_ker_of_chevalley
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker := by
  classical
  obtain ⟨r, hrnonzero, γ, hγpos, hγ⟩ := exists_nonzero_ramifiedParity_tp_generator d
  refine ⟨r, hrnonzero, ?_⟩
  exact (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_tp_generator d r).mpr
    ⟨γ, hγpos, hγ⟩

/-- Weak positive-principal ramified relation needed for the upper bound, stated
as a nonzero kernel vector of the full ramified-parity map. -/
theorem exists_nonzero_fullRamifiedParityNarrowClassHom_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker :=
  exists_nonzero_fullRamifiedParityNarrowClassHom_ker_of_chevalley d

/-- Product-form compatibility for the nonzero kernel vector. -/
theorem exists_nonzero_fullRamifiedParityNarrowClassProduct_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧ fullRamifiedParityNarrowClassProduct d r = 1 := by
  obtain ⟨r, hrnonzero, hrker⟩ := exists_nonzero_fullRamifiedParityNarrowClassHom_ker d
  exact ⟨r, hrnonzero, (fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mp hrker⟩

/-- A nonzero kernel vector lets one coordinate in its support be erased. This is
the exact-sequence step behind the ambiguous-ideal upper bound. -/
theorem exists_erasedRamifiedParityProduct_mk0_eq_full_of_mem_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker)
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) :
    ∃ w : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2),
      NarrowClassGroup.mk0
          (ramifiedParityIdealProduct d hp0 w) =
        NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) := by
  let v := fullRamifiedParityVector d J
  by_cases hv0 : v ⟨p0, hp0⟩ = 0
  · refine ⟨fun p => v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩, ?_⟩
    rw [fullRamifiedParityIdealProduct_eq_ramifiedParityIdealProduct_of_apply_p0_eq_zero
      d hp0 v hv0]
  · let v' : {p // p ∈ ramifiedPrimes d} → Fin 2 := fun p => v p + r p
    have hv'p0 : v' ⟨p0, hp0⟩ = 0 := by
      simpa [v'] using fin_two_add_eq_zero_of_ne_zero_of_ne_zero hv0 hrp0
    refine ⟨fun p => v' ⟨p.1, (Finset.mem_erase.mp p.2).2⟩, ?_⟩
    rw [← fullRamifiedParityIdealProduct_eq_ramifiedParityIdealProduct_of_apply_p0_eq_zero
      d hp0 v' hv'p0]
    exact (fullRamifiedParityNarrowClassHom_mem_ker_iff_mk0_add_relation d r).mp hrker v

end Internal
end GenusTheory
end ClassGroup
end QuadraticNumberFields
