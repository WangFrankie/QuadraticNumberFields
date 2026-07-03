/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Exact
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.RingTheory.ClassGroup

/-!
# Narrow Ideal Class Groups

This file defines the narrow ideal class group and its natural map to the usual
class group. The two quotient definitions fit into

`1 → Prin_L⁺ → I_L → Cl_L⁺ → 1`

and

`1 → Prin_L → I_L → Cl_L → 1`.

Since `Prin_L⁺ ≤ Prin_L`, the comparison sequence has kernel
`Prin_L / Prin_L⁺`.

-/

open scoped nonZeroDivisors

open FractionalIdeal

/-! ### Quotient-group exactness helpers -/

namespace QuotientGroup

section SubgroupQuotient

variable {G : Type*} [CommGroup G]

/-- The natural map `M / N → G / N` induced by the inclusion `M ≤ G`. -/
def subgroupQuotientToQuotient (N M : Subgroup G) :
    M ⧸ N.subgroupOf M →* G ⧸ N :=
  QuotientGroup.map (N.subgroupOf M) N M.subtype (by
    intro x hx
    exact Subgroup.mem_subgroupOf.mp hx)

@[simp]
theorem subgroupQuotientToQuotient_mk (N M : Subgroup G) (x : M) :
    subgroupQuotientToQuotient N M (QuotientGroup.mk' (N.subgroupOf M) x) =
      QuotientGroup.mk' N (x : G) :=
  QuotientGroup.map_mk' _ _ _ _ x

/-- For `N ≤ M ≤ G`, the sequence `M / N → G / N → G / M` is exact at `G / N`. -/
theorem mulExact_subgroupQuotientToQuotient_mapOfLE (N M : Subgroup G) (hNM : N ≤ M) :
    Function.MulExact (subgroupQuotientToQuotient N M)
      (QuotientGroup.map N M (MonoidHom.id G) hNM) := by
  rw [MonoidHom.mulExact_iff]
  ext q
  constructor
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [MonoidHom.mem_ker, QuotientGroup.map_mk'] at hq
    have hgM : g ∈ M := (QuotientGroup.eq_one_iff (N := M) g).mp hq
    exact ⟨QuotientGroup.mk' (N.subgroupOf M) ⟨g, hgM⟩, by
      simpa using subgroupQuotientToQuotient_mk N M ⟨g, hgM⟩⟩
  · rintro ⟨qM, rfl⟩
    rw [MonoidHom.mem_ker]
    induction qM using QuotientGroup.induction_on with
    | _ x =>
        change QuotientGroup.map N M (MonoidHom.id G) hNM
            (subgroupQuotientToQuotient N M (QuotientGroup.mk' (N.subgroupOf M) x)) = 1
        rw [subgroupQuotientToQuotient_mk]
        rw [QuotientGroup.map_mk']
        exact (QuotientGroup.eq_one_iff (N := M) (x : G)).mpr x.2

end SubgroupQuotient

end QuotientGroup

noncomputable section

namespace NarrowClassGroup

/-! ### Totally positive field elements -/

section TotallyPositive

variable {K : Type*} [Field K]

/-- An element of a field is totally positive if it is positive under every real
embedding. For fields with no real embeddings, this condition is vacuous. -/
def IsTotallyPositive (x : K) : Prop :=
  ∀ σ : K →+* ℝ, 0 < σ x

/-- The subgroup of totally positive units of a field. That is K₊ˣ -/
def totallyPositiveUnits (K : Type*) [Field K] : Subgroup Kˣ where
  carrier := {x | IsTotallyPositive (x : K)}
  one_mem' := by
    intro σ
    simp
  mul_mem' := by
    intro x y hx hy σ
    simpa using mul_pos (hx σ) (hy σ)
  inv_mem' := by
    intro x hx σ
    simpa using inv_pos.mpr (hx σ)

/-- Membership in the subgroup of totally positive units. -/
theorem mem_totallyPositiveUnits_iff (x : Kˣ) :
    x ∈ totallyPositiveUnits K ↔ IsTotallyPositive (x : K) :=
  Iff.rfl

/-- If a field has no real embeddings, every element is totally positive by
vacuity. -/
theorem isTotallyPositive_of_isEmpty [IsEmpty (K →+* ℝ)] (x : K) :
    IsTotallyPositive x := by
  intro σ
  exact isEmptyElim σ

/-- A nonzero square in a field is totally positive. -/
theorem isTotallyPositive_sq_of_ne_zero (x : K) (hx : x ≠ 0) :
    IsTotallyPositive (x ^ 2) := by
  intro σ
  have hσx : σ x ≠ 0 := (_root_.map_ne_zero σ).mpr hx
  simpa using sq_pos_of_ne_zero hσx

end TotallyPositive

/-! ### Narrow principal ideals -/

section NarrowPrincipalIdeals

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The principal-ideal map restricted to totally positive field elements:
`K₊ˣ ↪ Kˣ → I_K`. Its image is `P_K⁺ ≤ P_K ≤ I_K`, the subgroup used in the
narrow quotient. -/
noncomputable def toNarrowPrincipalIdeal (R K : Type*) [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    totallyPositiveUnits K →* (FractionalIdeal R⁰ K)ˣ :=
  (toPrincipalIdeal R K).comp (totallyPositiveUnits K).subtype

/-- Principal fractional ideals with a totally positive generator, usually denoted `P_K⁺`. -/
noncomputable def narrowPrincipalIdeals (R K : Type*) [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Subgroup ((FractionalIdeal R⁰ K)ˣ) :=
  (toNarrowPrincipalIdeal R K).range

/-- Narrow principal ideals are ordinary principal ideals. -/
theorem narrowPrincipalIdeals_le_principalIdeals :
    narrowPrincipalIdeals R K ≤ (toPrincipalIdeal R K).range := by
  intro I hI
  rcases hI with ⟨x, rfl⟩
  exact ⟨x.1, rfl⟩

/-- If every field unit is totally positive, the narrow and usual principal
fractional ideals are the same subgroup. -/
theorem narrowPrincipalIdeals_eq_principalIdeals_of_forall_isTotallyPositive
    (hpos : ∀ x : Kˣ, IsTotallyPositive (x : K)) :
    narrowPrincipalIdeals R K = (toPrincipalIdeal R K).range := by
  apply le_antisymm
  · exact narrowPrincipalIdeals_le_principalIdeals
  · intro I hI
    rcases hI with ⟨x, rfl⟩
    exact ⟨⟨x, hpos x⟩, rfl⟩

/-- If there are no real embeddings, the positivity condition disappears, so
the narrow and usual principal fractional ideals coincide. -/
theorem narrowPrincipalIdeals_eq_principalIdeals_of_isEmpty [IsEmpty (K →+* ℝ)] :
    narrowPrincipalIdeals R K = (toPrincipalIdeal R K).range :=
  narrowPrincipalIdeals_eq_principalIdeals_of_forall_isTotallyPositive
    (fun x => isTotallyPositive_of_isEmpty (x : K))

end NarrowPrincipalIdeals

end NarrowClassGroup

/-! ### The narrow class group -/

/-- The narrow ideal class group of `R`.

It is the group of invertible fractional ideals modulo principal fractional
ideals generated by totally positive elements of the fraction field.
That is, `Cl⁺(R) = I(R) / P⁺(R)`, where `P⁺(R)` is generated by the totally
positive elements of `FractionRing R`.
-/
def NarrowClassGroup (R : Type*) [CommRing R] [IsDomain R] :=
  (FractionalIdeal R⁰ (FractionRing R))ˣ ⧸
    NarrowClassGroup.narrowPrincipalIdeals R (FractionRing R)
deriving CommGroup, Inhabited

namespace NarrowClassGroup

/-! ### Class number -/

/-- The number of narrow ideal classes of `R`. -/
noncomputable def narrowClassNumber (R : Type*) [CommRing R] [IsDomain R]
    [Fintype (NarrowClassGroup R)] : ℕ :=
  Fintype.card (NarrowClassGroup R)

/-! ### Quotient maps -/

section QuotientMaps

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Send an invertible fractional ideal to its narrow ideal class. -/
noncomputable def mk : (FractionalIdeal R⁰ K)ˣ →* NarrowClassGroup R :=
  (QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R))).comp
    (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)).toMonoidHom)

/-- Unfolding lemma for the narrow ideal-class map. -/
theorem mk_def (I : (FractionalIdeal R⁰ K)ˣ) :
    mk I =
      (QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R)))
        (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)).toMonoidHom I) := rfl

/-- Send a nonzero field element to the narrow class of its principal fractional
ideal. This is the composite `Kˣ → I_K → Cl⁺(K)`. -/
noncomputable def principalToNarrow (R : Type*) [CommRing R] [IsDomain R] :
    (FractionRing R)ˣ →* NarrowClassGroup R :=
  mk.comp (toPrincipalIdeal R (FractionRing R))

/-- The natural map from the narrow ideal class group to the ordinary wide ideal
class group, induced by the inclusion of totally positive principal ideals into
all principal ideals. This is the map `Cl⁺(K) → Cl(K)` induced by `P_K⁺ ≤ P_K`. -/
noncomputable def toClassGroup (R : Type*) [CommRing R] [IsDomain R] :
    NarrowClassGroup R →* ClassGroup R :=
  QuotientGroup.map (narrowPrincipalIdeals R (FractionRing R))
    (toPrincipalIdeal R (FractionRing R)).range (MonoidHom.id _) (by
      intro I hI
      exact narrowPrincipalIdeals_le_principalIdeals (R := R) (K := FractionRing R) hI)

/-- The natural map to the wide class group sends a narrow ideal class to the
corresponding ordinary ideal class. -/
@[simp]
theorem toClassGroup_mk (I : (FractionalIdeal R⁰ K)ˣ) :
    toClassGroup R (mk I) = ClassGroup.mk I := by
  rw [mk_def, ClassGroup.mk_def]
  exact QuotientGroup.map_mk' (narrowPrincipalIdeals R (FractionRing R))
    (toPrincipalIdeal R (FractionRing R)).range (MonoidHom.id _)
    (by
      intro J hJ
      exact narrowPrincipalIdeals_le_principalIdeals (R := R) (K := FractionRing R) hJ)
    (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)).toMonoidHom I)

/-- Send a nonzero integral ideal to its narrow ideal class.

This is the narrow version of `ClassGroup.mk0`, used later for ambiguous ideals
and for the conjugation action on narrow classes. -/
noncomputable def mk0 [IsDedekindDomain R] : (Ideal R)⁰ →* NarrowClassGroup R :=
  mk.comp (FractionalIdeal.mk0 (FractionRing R))

/-- The narrow ideal-class map on an integral ideal agrees with `mk0`. -/
theorem mk_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    mk (FractionalIdeal.mk0 (FractionRing R) I) = mk0 I := by
  rfl

/-- The map to the wide class group sends the narrow class of an integral ideal
to its usual ideal class. -/
@[simp]
theorem toClassGroup_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    toClassGroup R (mk0 I) = ClassGroup.mk0 I := by
  rw [mk0, MonoidHom.comp_apply, toClassGroup_mk, ClassGroup.mk_mk0]

/-- Evaluate `toClassGroup` on a quotient representative: the narrow class of
`J` maps to the usual class of `J`. -/
theorem toClassGroup_mk' (R : Type*) [CommRing R] [IsDomain R]
    (J : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    toClassGroup R (QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R)) J) =
      QuotientGroup.mk' (toPrincipalIdeal R (FractionRing R)).range J :=
  QuotientGroup.map_mk' _ _ _ _ J

end QuotientMaps

section FractionRing

variable {R : Type*} [CommRing R] [IsDomain R]

/-! ### Quotient representatives -/

/-- Over the chosen fraction field, `mk` is just the quotient map. -/
theorem mk_eq_mk' (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    mk I = QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R)) I := by
  rw [mk_def, canonicalEquiv_self]
  rfl

/-! ### Exactness of the narrow-to-wide comparison -/

/-- The map `P_K / P_K⁺ → Cl⁺(K)` coming from the inclusion of principal
fractional ideals into all fractional ideals. -/
noncomputable def principalIdealsQuotientToNarrow (R : Type*) [CommRing R] [IsDomain R] :
    (toPrincipalIdeal R (FractionRing R)).range ⧸
      (narrowPrincipalIdeals R (FractionRing R)).subgroupOf
        (toPrincipalIdeal R (FractionRing R)).range →* NarrowClassGroup R :=
  QuotientGroup.subgroupQuotientToQuotient
    (narrowPrincipalIdeals R (FractionRing R))
    (toPrincipalIdeal R (FractionRing R)).range

/-- The comparison sequence `P_K / P_K⁺ → Cl⁺(K) → Cl(K)` is exact at
`Cl⁺(K)`. -/
theorem mulExact_principalIdealsQuotientToNarrow_toClassGroup
    (R : Type*) [CommRing R] [IsDomain R] :
    Function.MulExact (principalIdealsQuotientToNarrow R) (toClassGroup R) := by
  simpa [principalIdealsQuotientToNarrow, toClassGroup] using
    QuotientGroup.mulExact_subgroupQuotientToQuotient_mapOfLE
      (N := narrowPrincipalIdeals R (FractionRing R))
      (M := (toPrincipalIdeal R (FractionRing R)).range)
      (narrowPrincipalIdeals_le_principalIdeals (R := R) (K := FractionRing R))

/-- The image of principal fractional ideals in the narrow class group is exactly
the kernel of the map `Cl⁺(K) → Cl(K)`. -/
theorem mulExact_principalToNarrow_toClassGroup (R : Type*) [CommRing R] [IsDomain R] :
    Function.MulExact (principalToNarrow R) (toClassGroup R) := by
  rw [MonoidHom.mulExact_iff]
  ext C
  constructor
  · intro hC
    obtain ⟨I, rfl⟩ :=
      QuotientGroup.mk'_surjective (narrowPrincipalIdeals R (FractionRing R)) C
    rw [← mk_eq_mk'] at hC ⊢
    rw [MonoidHom.mem_ker, toClassGroup_mk, ← map_one (ClassGroup.mk (K := FractionRing R)),
      ClassGroup.mk_eq_mk] at hC
    obtain ⟨x, hx⟩ := hC
    refine ⟨x⁻¹, ?_⟩
    have hI : toPrincipalIdeal R (FractionRing R) x⁻¹ = I := by
      rw [map_inv]
      exact inv_eq_of_mul_eq_one_left hx
    change mk (toPrincipalIdeal R (FractionRing R) x⁻¹) = mk I
    rw [hI]
  · rintro ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, principalToNarrow, MonoidHom.comp_apply, toClassGroup_mk,
      ← map_one (ClassGroup.mk (K := FractionRing R)), ClassGroup.mk_eq_mk]
    exact ⟨x⁻¹, by rw [map_inv, mul_inv_cancel]⟩

/-- The kernel of `Cl⁺(K) → Cl(K)` is the image of principal ideals in the
narrow class group. -/
theorem toClassGroup_ker_eq_principalToNarrow_range
    (R : Type*) [CommRing R] [IsDomain R] :
    (toClassGroup R).ker = (principalToNarrow R).range :=
  Function.MulExact.monoidHom_ker_eq (mulExact_principalToNarrow_toClassGroup R)

/-! ### Equality and principal multipliers -/

set_option backward.isDefEq.respectTransparency false in
/-- Two invertible fractional ideals have the same narrow class exactly when
they differ by a totally positive principal fractional ideal. -/
theorem mk_eq_mk {I J : (FractionalIdeal R⁰ (FractionRing R))ˣ} :
    mk I = mk J ↔
      ∃ x : totallyPositiveUnits (FractionRing R),
        I * toNarrowPrincipalIdeal R (FractionRing R) x = J := by
  rw [mk_eq_mk', mk_eq_mk']
  rw [QuotientGroup.mk'_eq_mk' (N := narrowPrincipalIdeals R (FractionRing R))]
  constructor
  · rintro ⟨P, hP, hIP⟩
    rcases hP with ⟨x, rfl⟩
    exact ⟨x, hIP⟩
  · rintro ⟨x, hIP⟩
    exact ⟨toNarrowPrincipalIdeal R (FractionRing R) x, ⟨x, rfl⟩, hIP⟩

/-- Integral-ideal form of `mk_eq_mk`: equality of narrow classes is equality
after multiplying by a totally positive principal fractional ideal. -/
theorem mk0_eq_mk0_iff_exists_fraction_ring [IsDedekindDomain R] {I J : (Ideal R)⁰} :
    mk0 I = mk0 J ↔
      ∃ x : (FractionRing R)ˣ,
        IsTotallyPositive (x : FractionRing R) ∧
          FractionalIdeal.mk0 (FractionRing R) I * toPrincipalIdeal R (FractionRing R) x =
            FractionalIdeal.mk0 (FractionRing R) J := by
  rw [← mk_mk0, ← mk_mk0, mk_eq_mk]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, x.property, hx⟩
  · rintro ⟨x, hxpos, hx⟩
    exact ⟨⟨x, hxpos⟩, hx⟩

/-- A nonzero integral ideal is trivial in the narrow class group exactly when a
totally positive principal fractional ideal makes it equal to `1`. -/
theorem mk0_eq_one_iff_exists_fraction_ring [IsDedekindDomain R] {I : (Ideal R)⁰} :
    mk0 I = 1 ↔
      ∃ x : (FractionRing R)ˣ,
        IsTotallyPositive (x : FractionRing R) ∧
          FractionalIdeal.mk0 (FractionRing R) I * toPrincipalIdeal R (FractionRing R) x =
            1 := by
  simpa using
    (mk0_eq_mk0_iff_exists_fraction_ring (R := R) (I := I) (J := (1 : (Ideal R)⁰)))

/-- Multiplication by a square principal fractional ideal preserves the narrow
ideal class. -/
theorem mk_eq_mk_mul_toPrincipalIdeal_sq
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) (x : FractionRing R) (hx : x ≠ 0) :
    mk I =
      mk (I * toPrincipalIdeal R (FractionRing R) (Units.mk0 (x ^ 2) (pow_ne_zero 2 hx))) := by
  exact (mk_eq_mk.mpr
    ⟨⟨Units.mk0 (x ^ 2) (pow_ne_zero 2 hx), isTotallyPositive_sq_of_ne_zero x hx⟩, rfl⟩)

/-- Integral-ideal version of the preceding square-principal invariance. -/
theorem mk0_eq_mk0_of_mul_toPrincipalIdeal_sq [IsDedekindDomain R]
    {I J : (Ideal R)⁰} {x : FractionRing R} (hx : x ≠ 0)
    (hJ : FractionalIdeal.mk0 (FractionRing R) I *
        toPrincipalIdeal R (FractionRing R) (Units.mk0 (x ^ 2) (pow_ne_zero 2 hx)) =
      FractionalIdeal.mk0 (FractionRing R) J) :
    mk0 I = mk0 J := by
  rw [← mk_mk0, ← mk_mk0]
  exact (mk_eq_mk.mpr
    ⟨⟨Units.mk0 (x ^ 2) (pow_ne_zero 2 hx), isTotallyPositive_sq_of_ne_zero x hx⟩, hJ⟩)

/-! ### Integral representatives -/

/-- An integral ideal representative for a narrow class.

Compared with the usual class-group numerator, this uses one extra denominator.
The change from the original fractional ideal is then generated by a square,
hence by a totally positive element. -/
def integralRep (I : FractionalIdeal R⁰ (FractionRing R)) : Ideal R :=
  Ideal.span ({(I.den : R)} : Set R) * I.num

/-- The narrow integral representative of a nonzero fractional ideal is nonzero. -/
theorem integralRep_mem_nonZeroDivisors
    {I : FractionalIdeal R⁰ (FractionRing R)} (hI : I ≠ 0) :
    integralRep I ∈ (Ideal R)⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero, integralRep]
  apply mul_ne_zero
  · rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.den.prop
  · rwa [ne_eq, FractionalIdeal.num_eq_zero_iff]

/-- The integral representative has the same narrow class as the original
fractional ideal. -/
theorem mk0_integralRep [IsDedekindDomain R]
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    mk0 ⟨integralRep I, integralRep_mem_nonZeroDivisors I.ne_zero⟩ = mk I := by
  rw [← mk_mk0, mk_eq_mk', mk_eq_mk']
  let a : FractionRing R := algebraMap R (FractionRing R) (I.1.den : R)
  have ha0 : a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.1.den.prop
  let u : (FractionRing R)ˣ := Units.mk0 (a ^ 2) (pow_ne_zero 2 ha0)
  have hu_pos : u ∈ totallyPositiveUnits (FractionRing R) := by
    exact isTotallyPositive_sq_of_ne_zero a ha0
  let P : (FractionalIdeal R⁰ (FractionRing R))ˣ :=
    toNarrowPrincipalIdeal R (FractionRing R) ⟨u, hu_pos⟩
  have hP_mem : P ∈ narrowPrincipalIdeals R (FractionRing R) := by
    exact ⟨⟨u, hu_pos⟩, rfl⟩
  have hrep :
      FractionalIdeal.mk0 (FractionRing R)
          ⟨integralRep I, integralRep_mem_nonZeroDivisors I.ne_zero⟩ =
        P * I := by
    apply Units.ext
    change ((integralRep I : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) =
      (P : (FractionalIdeal R⁰ (FractionRing R))ˣ) * I
    calc
      ((integralRep I : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) =
          spanSingleton R⁰ a * (I.1.num : FractionalIdeal R⁰ (FractionRing R)) := by
        rw [integralRep, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
      _ = spanSingleton R⁰ a *
          (spanSingleton R⁰ a * (I : FractionalIdeal R⁰ (FractionRing R))) := by
        rw [FractionalIdeal.den_mul_self_eq_num']
      _ = spanSingleton R⁰ (a ^ 2) * (I : FractionalIdeal R⁰ (FractionRing R)) := by
        rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, pow_two]
      _ = (P : (FractionalIdeal R⁰ (FractionRing R))ˣ) * I := by
        simp [P, u, toNarrowPrincipalIdeal, coe_toPrincipalIdeal]
  rw [hrep, map_mul]
  have hP_one : QuotientGroup.mk' (narrowPrincipalIdeals R (FractionRing R)) P = 1 :=
    (QuotientGroup.eq_one_iff P).mpr hP_mem
  rw [hP_one]
  exact one_mul _

/-- Every narrow ideal class has a nonzero integral ideal representative. -/
theorem mk0_surjective [IsDedekindDomain R] :
    Function.Surjective (mk0 : (Ideal R)⁰ → NarrowClassGroup R) := by
  intro C
  obtain ⟨I, hI⟩ :=
    QuotientGroup.mk'_surjective (narrowPrincipalIdeals R (FractionRing R)) C
  refine ⟨⟨integralRep I, integralRep_mem_nonZeroDivisors I.ne_zero⟩, ?_⟩
  rw [mk0_integralRep]
  simpa [mk_eq_mk'] using hI

/-! ### Comparison with the usual class group -/

/-- If the narrow and usual principal fractional ideals are the same subgroup,
then the narrow and wide class groups are isomorphic. -/
noncomputable def mulEquivClassGroupOfEq (R : Type*) [CommRing R] [IsDomain R]
    (h : narrowPrincipalIdeals R (FractionRing R) =
      (toPrincipalIdeal R (FractionRing R)).range) :
    NarrowClassGroup R ≃* ClassGroup R :=
  QuotientGroup.quotientMulEquivOfEq h

/-- Propositional form of `mulEquivClassGroupOfEq`. -/
theorem nonempty_mulEquivClassGroup_of_eq (R : Type*) [CommRing R] [IsDomain R]
    (h : narrowPrincipalIdeals R (FractionRing R) =
      (toPrincipalIdeal R (FractionRing R)).range) :
    Nonempty (NarrowClassGroup R ≃* ClassGroup R) :=
  ⟨mulEquivClassGroupOfEq R h⟩

/-- If the narrow and usual principal fractional ideals coincide, then
`toClassGroup` is bijective. -/
theorem toClassGroup_bijective_of_eq (R : Type*) [CommRing R] [IsDomain R]
    (h : narrowPrincipalIdeals R (FractionRing R) =
      (toPrincipalIdeal R (FractionRing R)).range) :
    Function.Bijective (toClassGroup R) :=
  (mulEquivClassGroupOfEq R h).bijective

/-- If every unit of the fraction field is totally positive, then the narrow and
wide class groups are isomorphic. -/
noncomputable def mulEquivClassGroupOfForallIsTotallyPositive
    (R : Type*) [CommRing R] [IsDomain R]
    (hpos : ∀ x : (FractionRing R)ˣ, IsTotallyPositive (x : FractionRing R)) :
    NarrowClassGroup R ≃* ClassGroup R :=
  mulEquivClassGroupOfEq R
    (narrowPrincipalIdeals_eq_principalIdeals_of_forall_isTotallyPositive
      (R := R) (K := FractionRing R) hpos)

/-- Nonempty form of `mulEquivClassGroupOfForallIsTotallyPositive`. -/
theorem nonempty_mulEquivClassGroup_of_forall_isTotallyPositive
    (R : Type*) [CommRing R] [IsDomain R]
    (hpos : ∀ x : (FractionRing R)ˣ, IsTotallyPositive (x : FractionRing R)) :
    Nonempty (NarrowClassGroup R ≃* ClassGroup R) :=
  ⟨mulEquivClassGroupOfForallIsTotallyPositive R hpos⟩

/-- If every unit of the fraction field is totally positive, then
`toClassGroup` is bijective. -/
theorem toClassGroup_bijective_of_forall_isTotallyPositive
    (R : Type*) [CommRing R] [IsDomain R]
    (hpos : ∀ x : (FractionRing R)ˣ, IsTotallyPositive (x : FractionRing R)) :
    Function.Bijective (toClassGroup R) :=
  toClassGroup_bijective_of_eq R
    (narrowPrincipalIdeals_eq_principalIdeals_of_forall_isTotallyPositive
      (R := R) (K := FractionRing R) hpos)

/-- If the fraction field has no real embeddings, the narrow and wide class
groups are isomorphic. -/
noncomputable def mulEquivClassGroupOfIsEmpty (R : Type*) [CommRing R] [IsDomain R]
    [IsEmpty (FractionRing R →+* ℝ)] :
    NarrowClassGroup R ≃* ClassGroup R :=
  mulEquivClassGroupOfForallIsTotallyPositive R
    (fun x => isTotallyPositive_of_isEmpty (x : FractionRing R))

/-- Nonempty form of `mulEquivClassGroupOfIsEmpty`. -/
theorem nonempty_mulEquivClassGroup_of_isEmpty (R : Type*) [CommRing R] [IsDomain R]
    [IsEmpty (FractionRing R →+* ℝ)] :
    Nonempty (NarrowClassGroup R ≃* ClassGroup R) :=
  ⟨mulEquivClassGroupOfIsEmpty R⟩

/-- If the fraction field has no real embeddings, then `toClassGroup` is
bijective. -/
theorem toClassGroup_bijective_of_isEmpty (R : Type*) [CommRing R] [IsDomain R]
    [IsEmpty (FractionRing R →+* ℝ)] :
    Function.Bijective (toClassGroup R) :=
  toClassGroup_bijective_of_forall_isTotallyPositive R
    (fun x => isTotallyPositive_of_isEmpty (x : FractionRing R))

end FractionRing

/-! ### Finiteness of the narrow class group

The narrow class group is finite when the wide class group is finite and the
fraction field has finitely many real embeddings. For rings of integers in
number fields, both hypotheses hold. The kernel of `toClassGroup` is controlled
by signs of units at the real embeddings, so it embeds into a finite group of
sign vectors. -/

/-- The sign homomorphism on the units of `ℝ`, valued in the unit group of `SignType`. -/
def realSignUnitHom : ℝˣ →* SignTypeˣ :=
  Units.map (signHom : ℝ →*₀ SignType).toMonoidHom

theorem realSignUnitHom_apply (u : ℝˣ) :
    ((realSignUnitHom u : SignTypeˣ) : SignType) = SignType.sign (u : ℝ) :=
  rfl

/-- Send a unit of `K` to its signs at all real embeddings. The kernel is the
subgroup of totally positive units. -/
def signVectorHom (K : Type*) [Field K] : Kˣ →* ((K →+* ℝ) → SignTypeˣ) where
  toFun x σ := realSignUnitHom (Units.map (σ : K →+* ℝ).toMonoidHom x)
  map_one' := by funext σ; simp
  map_mul' a b := by funext σ; simp [map_mul]

theorem signVectorHom_apply (K : Type*) [Field K] (x : Kˣ) (σ : K →+* ℝ) :
    signVectorHom K x σ = realSignUnitHom (Units.map (σ : K →+* ℝ).toMonoidHom x) :=
  rfl

/-- The subgroup of totally positive units is exactly the kernel of the sign-vector
homomorphism. -/
theorem totallyPositiveUnits_eq_ker (K : Type*) [Field K] :
    totallyPositiveUnits K = (signVectorHom K).ker := by
  ext x
  simp only [mem_totallyPositiveUnits_iff, IsTotallyPositive, MonoidHom.mem_ker]
  constructor
  · intro hx
    funext σ
    ext
    change SignType.sign (σ (x : K)) = 1
    exact sign_eq_one_iff.mpr (hx σ)
  · intro hx σ
    have hxσ : signVectorHom K x σ = 1 := congrFun hx σ
    have hxσ_val : ((signVectorHom K x σ : SignTypeˣ) : SignType) = 1 := by
      simpa using congrArg Units.val hxσ
    change SignType.sign (σ (x : K)) = 1 at hxσ_val
    exact sign_eq_one_iff.mp hxσ_val

/-- If there are finitely many real embeddings, then units modulo totally
positive units form a finite group. -/
instance instFiniteUnitsQuotientTotallyPositiveUnits (K : Type*) [Field K]
    [Finite (K →+* ℝ)] : Finite (Kˣ ⧸ totallyPositiveUnits K) := by
  rw [totallyPositiveUnits_eq_ker]
  exact Finite.of_injective _ (QuotientGroup.kerLift_injective (signVectorHom K))

/-- The image of field units in the narrow class group is finite when the fraction field
has finitely many real embeddings. -/
theorem finite_range_principalToNarrow (R : Type*) [CommRing R] [IsDomain R]
    [Finite (FractionRing R →+* ℝ)] : Finite (principalToNarrow R).range := by
  let φ := principalToNarrow R
  have hker : totallyPositiveUnits (FractionRing R) ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change mk (toPrincipalIdeal R (FractionRing R) x) = 1
    rw [mk_eq_mk']
    exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨x, hx⟩, rfl⟩
  let L := QuotientGroup.lift (totallyPositiveUnits (FractionRing R)) φ hker
  let ψ : (FractionRing R)ˣ ⧸ totallyPositiveUnits (FractionRing R) → φ.range :=
    fun q => ⟨L q, by
      induction q using QuotientGroup.induction_on with
      | _ x => exact ⟨x, (QuotientGroup.lift_mk' _ _ x).symm⟩⟩
  haveI : Finite φ.range := Finite.of_surjective ψ (by
    rintro ⟨_, x, rfl⟩
    exact ⟨QuotientGroup.mk' _ x, Subtype.ext (QuotientGroup.lift_mk' _ _ x)⟩)
  simpa [φ]

/-- The kernel of `Cl⁺(K) → Cl(K)` is finite when the fraction field has finitely
many real embeddings. -/
theorem finite_ker_toClassGroup (R : Type*) [CommRing R] [IsDomain R]
    [Finite (FractionRing R →+* ℝ)] : Finite (toClassGroup R).ker := by
  rw [toClassGroup_ker_eq_principalToNarrow_range]
  exact finite_range_principalToNarrow R

/-- The narrow class group is finite if the wide class group is finite and the
fraction field has finitely many real embeddings. -/
instance instFiniteNarrowClassGroup (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [Finite (ClassGroup R)] [Finite (FractionRing R →+* ℝ)] :
    Finite (NarrowClassGroup R) := by
  rw [(toClassGroup R).finite_iff_finite_ker_range]
  exact ⟨finite_ker_toClassGroup R, inferInstance⟩

end NarrowClassGroup
