/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Units.Imaginary

/-!
# Fundamental Units

A unit `u` of a ring is *fundamental* if every unit is, up to sign, an integer
power of `u`. For the ring of integers of a real quadratic field this is the
classical notion of a fundamental unit; Dirichlet's unit theorem guarantees
its existence (not yet formalized here).

## Main definitions

* `IsFundamentalUnit u`: every unit is `±u^n` for some `n : ℤ`.

## Main results

* `IsFundamentalUnit.inv`, `IsFundamentalUnit.neg`: fundamental units are
  closed under inverse and negation.
* `IsFundamentalUnit.map`, `IsFundamentalUnit.map_ringEquiv`: transport along
  (ring) isomorphisms, used to move fundamental units between `𝓞(Q(√d))` and
  the concrete coordinate models.
* `isFundamentalUnit_one_zsqrtd`, `isFundamentalUnit_one_zOnePlusSqrtOverTwo`:
  in the imaginary cases with unit group `{±1}` the unit `1` is fundamental.
* `isFundamentalUnit_gaussianUnit`: `i = √-1` is a fundamental unit of the
  Gaussian integers.
* `isFundamentalUnit_eisensteinUnit`: `ω = (1+√-3)/2` is a fundamental unit of
  the Eisenstein integers.
-/

namespace QuadraticNumberFields
namespace Units

section Monoid

variable {R S : Type*} [Monoid R] [HasDistribNeg R] [Monoid S] [HasDistribNeg S]

/-- A unit `u` is *fundamental* if every unit is, up to sign, an integer power
of `u`. -/
def IsFundamentalUnit (u : Rˣ) : Prop :=
  ∀ v : Rˣ, ∃ n : ℤ, v = u ^ n ∨ v = -u ^ n

/-- The inverse of a fundamental unit is fundamental. -/
theorem IsFundamentalUnit.inv {u : Rˣ} (hu : IsFundamentalUnit u) :
    IsFundamentalUnit u⁻¹ := by
  intro v
  obtain ⟨n, hn | hn⟩ := hu v
  · exact ⟨-n, Or.inl (by rw [hn, zpow_neg, inv_zpow, inv_inv])⟩
  · exact ⟨-n, Or.inr (by rw [hn, zpow_neg, inv_zpow, inv_inv])⟩

private theorem neg_zpow_even (u : Rˣ) {n : ℤ} (hn : Even n) : (-u) ^ n = u ^ n := by
  have hnat : Even n.natAbs := Int.natAbs_even.mpr hn
  rcases Int.natAbs_eq n with h | h
  · rw [h, zpow_natCast, zpow_natCast, hnat.neg_pow]
  · rw [h, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, hnat.neg_pow]

private theorem neg_zpow_odd (u : Rˣ) {n : ℤ} (hn : Odd n) : (-u) ^ n = -u ^ n := by
  have hnat : Odd n.natAbs := Int.natAbs_odd.mpr hn
  rcases Int.natAbs_eq n with h | h
  · rw [h, zpow_natCast, zpow_natCast, hnat.neg_pow]
  · rw [h, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, hnat.neg_pow, inv_neg]

/-- The negation of a fundamental unit is fundamental. -/
theorem IsFundamentalUnit.neg {u : Rˣ} (hu : IsFundamentalUnit u) :
    IsFundamentalUnit (-u) := by
  intro v
  obtain ⟨n, hn | hn⟩ := hu v
  · refine ⟨n, ?_⟩
    rcases Int.even_or_odd n with he | ho
    · exact Or.inl (by rw [hn, neg_zpow_even u he])
    · exact Or.inr (by rw [hn, neg_zpow_odd u ho, neg_neg])
  · refine ⟨n, ?_⟩
    rcases Int.even_or_odd n with he | ho
    · exact Or.inr (by rw [hn, neg_zpow_even u he])
    · exact Or.inl (by rw [hn, neg_zpow_odd u ho])

/-- Transport a fundamental unit along a multiplicative equivalence that
preserves negation, e.g. (the multiplicative part of) a ring isomorphism. -/
theorem IsFundamentalUnit.map {u : Rˣ} (e : R ≃* S) (he : ∀ x : R, e (-x) = -e x)
    (hu : IsFundamentalUnit u) : IsFundamentalUnit (Units.mapEquiv e u) := by
  have hneg : ∀ w : Rˣ, Units.mapEquiv e (-w) = -Units.mapEquiv e w := fun w =>
    Units.ext (by simp [Units.coe_mapEquiv, he])
  intro v
  obtain ⟨n, hn | hn⟩ := hu ((Units.mapEquiv e).symm v)
  · refine ⟨n, Or.inl ?_⟩
    have hv := congrArg (Units.mapEquiv e) hn
    rw [MulEquiv.apply_symm_apply] at hv
    rw [hv]
    exact map_zpow _ u n
  · refine ⟨n, Or.inr ?_⟩
    have hv := congrArg (Units.mapEquiv e) hn
    rw [MulEquiv.apply_symm_apply] at hv
    rw [hv, hneg, map_zpow]

end Monoid

/-- Transport a fundamental unit along a ring isomorphism. -/
theorem IsFundamentalUnit.map_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
    {u : Rˣ} (hu : IsFundamentalUnit u) :
    IsFundamentalUnit (Units.mapEquiv (e : R ≃* S) u) :=
  hu.map _ fun x => map_neg e x

/-- For `d < -1` the unit `1` is fundamental in `ℤ[√d]`: the unit group is
`{±1}`. -/
theorem isFundamentalUnit_one_zsqrtd {d : ℤ} (hd : d < -1) :
    IsFundamentalUnit (1 : (Zsqrtd d)ˣ) := by
  intro v
  refine ⟨0, ?_⟩
  rcases (isUnit_zsqrtd_iff_of_lt_neg_one hd (v : Zsqrtd d)).mp v.isUnit with h | h
  · exact Or.inl (Units.ext (by simpa using h))
  · exact Or.inr (Units.ext (by simpa using h))

/-- For `k ≤ -2` the unit `1` is fundamental in `ℤ[(1+√(1+4k))/2]`: the unit
group is `{±1}`. -/
theorem isFundamentalUnit_one_zOnePlusSqrtOverTwo {k : ℤ} (hk : k ≤ -2) :
    IsFundamentalUnit (1 : (ZOnePlusSqrtOverTwo k)ˣ) := by
  intro v
  refine ⟨0, ?_⟩
  rcases (isUnit_zOnePlusSqrtOverTwo_iff_of_le_neg_two hk (v : ZOnePlusSqrtOverTwo k)).mp
      v.isUnit with h | h
  · exact Or.inl (Units.ext (by simpa using h))
  · exact Or.inr (Units.ext (by simpa using h))

/-- `√-1` as a unit of the Gaussian integers `ℤ[√-1]`. -/
def gaussianUnit : (Zsqrtd (-1))ˣ :=
  QuadraticAlgebra.unitOfNormOne Zsqrtd.sqrtd (by simp)

@[simp]
theorem val_gaussianUnit : (gaussianUnit : Zsqrtd (-1)) = Zsqrtd.sqrtd :=
  rfl

/-- `√-1` is a fundamental unit of the Gaussian integers: every unit of
`ℤ[√-1]` is, up to sign, an integer power of `i = √-1`. -/
theorem isFundamentalUnit_gaussianUnit : IsFundamentalUnit gaussianUnit := by
  have hsq : ((gaussianUnit ^ (2 : ℤ) : (Zsqrtd (-1))ˣ) : Zsqrtd (-1)) = -1 := by
    rw [zpow_two, Units.val_mul, val_gaussianUnit]
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  intro v
  rcases (isUnit_zsqrtd_neg_one_iff (v : Zsqrtd (-1))).mp v.isUnit with h | h | h | h
  · exact ⟨0, Or.inl (Units.ext (by simpa using h))⟩
  · refine ⟨2, Or.inl (Units.ext ?_)⟩
    rw [hsq]
    exact h
  · exact ⟨1, Or.inl (Units.ext (by simpa using h))⟩
  · exact ⟨1, Or.inr (Units.ext (by simpa using h))⟩

/-- `ω = (1+√-3)/2` as a unit of the Eisenstein integers `ℤ[(1+√-3)/2]`. -/
def eisensteinUnit : (ZOnePlusSqrtOverTwo (-1))ˣ :=
  QuadraticAlgebra.unitOfNormOne ⟨0, 1⟩ (by simp)

@[simp]
theorem val_eisensteinUnit : (eisensteinUnit : ZOnePlusSqrtOverTwo (-1)) = ⟨0, 1⟩ :=
  rfl

/-- `ω` is a fundamental unit of the Eisenstein integers: every unit of
`ℤ[(1+√-3)/2]` is, up to sign, an integer power of `ω = (1+√-3)/2`. -/
theorem isFundamentalUnit_eisensteinUnit : IsFundamentalUnit eisensteinUnit := by
  have hsq : ((eisensteinUnit ^ (2 : ℤ) : (ZOnePlusSqrtOverTwo (-1))ˣ) :
      ZOnePlusSqrtOverTwo (-1)) = ⟨-1, 1⟩ := by
    rw [zpow_two, Units.val_mul, val_eisensteinUnit]
    ext <;> simp
  intro v
  rcases (isUnit_zOnePlusSqrtOverTwo_neg_one_iff (v : ZOnePlusSqrtOverTwo (-1))).mp v.isUnit
    with h | h | h | h | h | h
  · exact ⟨0, Or.inl (Units.ext (by simpa using h))⟩
  · exact ⟨0, Or.inr (Units.ext (by simpa using h))⟩
  · exact ⟨1, Or.inl (Units.ext (by simpa using h))⟩
  · exact ⟨1, Or.inr (Units.ext (by simpa using h))⟩
  · refine ⟨2, Or.inr (Units.ext ?_)⟩
    rw [Units.val_neg, hsq, h]
    ext <;> simp
  · refine ⟨2, Or.inl (Units.ext ?_)⟩
    rw [hsq]
    exact h

end Units
end QuadraticNumberFields
