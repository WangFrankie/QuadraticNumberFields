/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span

/-!
# Ideal Span Lemmas

Material destined for mathlib.
-/

namespace Ideal

/-- Auxiliary clearing-denominators lemma for ideal maps.

If multiplication by `c` carries every element of `S` into the image of `R`,
then multiplying any element of `I.map f` by `f c` makes it come from an
element of `I`. -/
private theorem exists_mem_of_mul_mem_map_aux {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {c : R}
    (hc : ∀ s : S, ∃ r : R, f r = f c * s)
    {I : Ideal R} {y : S} (hy : y ∈ I.map f) (s : S) :
    ∃ z : R, z ∈ I ∧ f z = (f c * s) * y := by
  change y ∈ span (f '' I) at hy
  revert s
  induction hy using Submodule.span_induction with
  | mem y hy =>
      intro s
      rcases hy with ⟨i, hi, rfl⟩
      rcases hc s with ⟨r, hr⟩
      refine ⟨r * i, I.mul_mem_left r hi, ?_⟩
      rw [map_mul, hr]
  | zero =>
      intro s
      exact ⟨0, I.zero_mem, by simp⟩
  | add y z _ _ ihy ihz =>
      intro s
      rcases ihy s with ⟨y', hy', hfy'⟩
      rcases ihz s with ⟨z', hz', hfz'⟩
      refine ⟨y' + z', I.add_mem hy' hz', ?_⟩
      rw [map_add, hfy', hfz']
      ring
  | smul t y _ ih =>
      intro s
      rcases ih (s * t) with ⟨z, hz, hfz⟩
      refine ⟨z, hz, ?_⟩
      rw [hfz]
      ring

/-- Extension-contraction for an ideal coprime to a conductor element.

If `f : R →+* S` is injective, multiplication by `f c` carries `S` into the
image of `R`, and `I + (c) = R`, then extending `I` to `S` and contracting back
to `R` recovers `I`. -/
theorem comap_map_eq_of_span_sup_eq_top_of_mul_range_subset
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {c : R}
    (hf : Function.Injective f)
    (hc : ∀ s : S, ∃ r : R, f r = f c * s)
    (I : Ideal R) (hI : I ⊔ span ({c} : Set R) = ⊤) :
    (I.map f).comap f = I := by
  apply le_antisymm
  · intro x hx
    rcases exists_mem_of_mul_mem_map_aux f hc hx 1 with ⟨z, hz, hfz⟩
    have hcx : c * x ∈ I := by
      have hcz : c * x = z := by
        apply hf
        calc
          f (c * x) = f c * f x := by rw [map_mul]
          _ = (f c * 1) * f x := by ring
          _ = f z := hfz.symm
      rw [hcz]
      exact hz
    have htop : (1 : R) ∈ I ⊔ span ({c} : Set R) := by
      rw [hI]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp htop with ⟨i, hi, j, hj, hij⟩
    have hxi : x * i ∈ I := I.mul_mem_left x hi
    have hxj : x * j ∈ I := by
      rw [mem_span_singleton] at hj
      rcases hj with ⟨r, rfl⟩
      convert I.mul_mem_left r hcx using 1
      ring
    have hx_eq : x = x * i + x * j := by
      calc
        x = x * 1 := by rw [mul_one]
        _ = x * (i + j) := by rw [hij]
        _ = x * i + x * j := by rw [mul_add]
    rw [hx_eq]
    exact I.add_mem hxi hxj
  · exact Ideal.le_comap_map (f := f)

/-- An element of a quotient by `I` is a unit iff its representative generates
the unit ideal modulo `I`. -/
theorem Quotient.isUnit_mk_iff_span_sup_eq_top {R : Type*} [CommRing R]
    (I : Ideal R) (x : R) :
    IsUnit (Quotient.mk I x) ↔ span ({x} : Set R) ⊔ I = ⊤ := by
  constructor
  · intro hx
    rw [Ideal.eq_top_iff_one]
    rcases isUnit_iff_exists.mp hx with ⟨y, hxy, _hyx⟩
    rcases Quotient.mk_surjective y with ⟨r, rfl⟩
    have hmem : x * r - 1 ∈ I := by
      have hmk : Quotient.mk I (x * r) = Quotient.mk I 1 := by
        simpa using hxy
      exact (Quotient.mk_eq_mk_iff_sub_mem (I := I) (x * r) 1).mp hmk
    have hxmem : x * r ∈ span ({x} : Set R) := by
      exact Ideal.mul_mem_right r _ (Ideal.subset_span (by simp))
    have hsup_xr : x * r ∈ span ({x} : Set R) ⊔ I :=
      Ideal.mem_sup_left hxmem
    have hsup_sub : x * r - 1 ∈ span ({x} : Set R) ⊔ I :=
      Ideal.mem_sup_right hmem
    have hsub : x * r - (x * r - 1) ∈ span ({x} : Set R) ⊔ I :=
      Ideal.sub_mem _ hsup_xr hsup_sub
    simpa using hsub
  · intro htop
    rw [Ideal.eq_top_iff_one] at htop
    rcases (Submodule.mem_sup.mp htop) with ⟨a, ha, b, hb, hab⟩
    rw [Ideal.mem_span_singleton] at ha
    rcases ha with ⟨r, hr⟩
    have hab' : x * r + b = 1 := by simpa [hr] using hab
    rw [isUnit_iff_exists]
    refine ⟨Quotient.mk I r, ?_, ?_⟩
    · have hmem : x * r - 1 ∈ I := by
        have hcalc : x * r - 1 = -b := by
          calc
            x * r - 1 = x * r - (x * r + b) := by rw [hab']
            _ = -b := by ring
        rw [hcalc]
        exact I.neg_mem hb
      exact (Quotient.mk_eq_mk_iff_sub_mem (I := I) (x * r) 1).mpr hmem
    · have hmem : r * x - 1 ∈ I := by
        have hcalc : r * x - 1 = -b := by
          calc
            r * x - 1 = x * r - 1 := by rw [mul_comm]
            _ = x * r - (x * r + b) := by rw [hab']
            _ = -b := by ring
        rw [hcalc]
        exact I.neg_mem hb
      exact (Quotient.mk_eq_mk_iff_sub_mem (I := I) (r * x) 1).mpr hmem

/-- The quotient unit represented by an element whose principal span is
coprime to the quotient ideal. -/
noncomputable def Quotient.unitOfSpanSupEqTop {R : Type*} [CommRing R]
    (I : Ideal R) (x : R) (h : span ({x} : Set R) ⊔ I = ⊤) :
    (R ⧸ I)ˣ :=
  ((Quotient.isUnit_mk_iff_span_sup_eq_top I x).2 h).unit

@[simp]
theorem Quotient.coe_unitOfSpanSupEqTop {R : Type*} [CommRing R]
    (I : Ideal R) (x : R) (h : span ({x} : Set R) ⊔ I = ⊤) :
    (Quotient.unitOfSpanSupEqTop I x h : R ⧸ I) = Quotient.mk I x :=
  IsUnit.unit_spec _

/-- An ideal maps to the unit ideal in the quotient by `I` iff it is coprime to
`I`. -/
theorem Quotient.map_eq_top_iff_sup_eq_top {R : Type*} [CommRing R]
    (I J : Ideal R) :
    J.map (Quotient.mk I) = ⊤ ↔ I ⊔ J = ⊤ := by
  constructor
  · intro h
    have hcomap : (J.map (Quotient.mk I)).comap (Quotient.mk I) = ⊤ := by
      rw [h, Ideal.comap_top]
    simpa [Ideal.comap_map_quotientMk] using hcomap
  · intro h
    have hcomap : (J.map (Quotient.mk I)).comap (Quotient.mk I) = ⊤ := by
      rw [Ideal.comap_map_quotientMk, h]
    exact Ideal.comap_eq_top_iff.mp hcomap

/-- A representative is a quotient unit iff its principal ideal maps to the unit
ideal in the quotient. -/
theorem Quotient.isUnit_mk_iff_map_span_singleton_eq_top
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    IsUnit (Quotient.mk I x) ↔
      (span ({x} : Set R)).map (Quotient.mk I) = ⊤ := by
  rw [Quotient.isUnit_mk_iff_span_sup_eq_top]
  rw [Quotient.map_eq_top_iff_sup_eq_top]
  rw [sup_comm]

/-- If two principal multiples of ideals become equal and the two ideals map to
`⊤` in the quotient, then the two principal ideals have the same quotient
image. -/
theorem Quotient.map_span_singleton_eq_of_span_mul_eq_of_maps_eq_top
    {R : Type*} [CommRing R] (I J K : Ideal R) {x y : R}
    (hJ : J.map (Quotient.mk I) = ⊤)
    (hK : K.map (Quotient.mk I) = ⊤)
    (hxy : span ({x} : Set R) * J = span ({y} : Set R) * K) :
    (span ({x} : Set R)).map (Quotient.mk I) =
      (span ({y} : Set R)).map (Quotient.mk I) := by
  have hmap := congrArg (fun L => L.map (Quotient.mk I)) hxy
  simpa [Ideal.map_mul, hJ, hK] using hmap

/-- Under the same quotient-coprime hypotheses, a principal multiplier is a unit
modulo `I` iff the matching multiplier is. -/
theorem Quotient.isUnit_mk_iff_isUnit_mk_of_span_mul_eq_of_maps_eq_top
    {R : Type*} [CommRing R] (I J K : Ideal R) {x y : R}
    (hJ : J.map (Quotient.mk I) = ⊤)
    (hK : K.map (Quotient.mk I) = ⊤)
    (hxy : span ({x} : Set R) * J = span ({y} : Set R) * K) :
    IsUnit (Quotient.mk I x) ↔ IsUnit (Quotient.mk I y) := by
  have hspan :=
    Quotient.map_span_singleton_eq_of_span_mul_eq_of_maps_eq_top I J K hJ hK hxy
  rw [Quotient.isUnit_mk_iff_map_span_singleton_eq_top,
    Quotient.isUnit_mk_iff_map_span_singleton_eq_top, hspan]

/-- A span is contained in a principal span iff each generator is divisible by
the principal generator. -/
-- Repository use: support theorem for `span_le_span_singleton_of_forall_dvd`.
theorem span_le_span_singleton_iff_forall_dvd
    {α : Type*} [CommSemiring α] {a : α} {S : Set α} :
    span S ≤ span {a} ↔ ∀ x ∈ S, a ∣ x := by
  rw [span_le]
  exact forall_congr' fun x => forall_congr' fun _ => mem_span_singleton

/-- If `a` divides every element of `S`, then `Ideal.span S ≤ Ideal.span {a}`. -/
-- Repository use: `Examples/SqrtNeg5/Ideals.lean` uses this for explicit
-- ideal-factorization containments.
theorem span_le_span_singleton_of_forall_dvd
    {α : Type*} [CommSemiring α] {a : α} {S : Set α}
    (h : ∀ x ∈ S, a ∣ x) :
    span S ≤ span {a} :=
  span_le_span_singleton_iff_forall_dvd.2 h

/-- If `m ∣ n`, then the ideal generated by `n` is contained in the ideal
generated by `m`. -/
theorem span_natCast_le_span_natCast_of_dvd
    {R : Type*} [CommSemiring R] {m n : ℕ} (h : m ∣ n) :
    span ({(n : R)} : Set R) ≤ span ({(m : R)} : Set R) := by
  rw [span_singleton_le_iff_mem, mem_span_singleton]
  rcases h with ⟨k, rfl⟩
  exact ⟨(k : R), by simp [Nat.cast_mul]⟩

/-- Coprimality with the ideal generated by `n` passes to the ideal generated by
any divisor `m` of `n`. -/
theorem isCoprime_span_natCast_of_isCoprime_span_natCast_of_dvd
    {R : Type*} [CommSemiring R] (I : Ideal R) {m n : ℕ}
    (hcop : IsCoprime I (span ({(n : R)} : Set R))) (hmn : m ∣ n) :
    IsCoprime I (span ({(m : R)} : Set R)) := by
  rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
  apply top_unique
  rw [← hcop]
  exact sup_le_sup_left (span_natCast_le_span_natCast_of_dvd hmn) I

/-- If `x * a` and `x * b` both lie in `K`, then `(x) * (a, b) ≤ K`. -/
theorem span_singleton_mul_span_pair_le {R : Type*} [CommRing R]
    {x a b : R} {K : Ideal R} (ha : x * a ∈ K) (hb : x * b ∈ K) :
    span ({x} : Set R) * span ({a, b} : Set R) ≤ K := by
  rw [span_singleton_mul_le_iff]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
  | zero => simp
  | add y z _ _ hy hz => simpa [mul_add] using K.add_mem hy hz
  | smul r y _ hy =>
      simpa [mul_assoc, mul_comm, mul_left_comm] using K.mul_mem_left r hy

/-- If all four products of two pairs of generators lie in an ideal, then the
product of the two generated pair ideals is contained in that ideal. -/
theorem span_pair_mul_span_pair_le {R : Type*} [CommRing R]
    {a b c d : R} {K : Ideal R}
    (hac : a * c ∈ K) (had : a * d ∈ K)
    (hbc : b * c ∈ K) (hbd : b * d ∈ K) :
    span ({a, b} : Set R) * span ({c, d} : Set R) ≤ K := by
  rw [span_pair_mul_span_pair]
  refine span_le.mpr ?_
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals simpa

/-- Pull back a principal ideal span along a ring equivalence. -/
theorem comap_span_singleton_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : S) :
    Ideal.comap (e : R →+* S) (span ({x} : Set S)) = span ({e.symm x} : Set R) := by
  ext z
  change e z ∈ span ({x} : Set S) ↔ z ∈ span ({e.symm x} : Set R)
  rw [mem_span_singleton, mem_span_singleton]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.symm s, ?_⟩
    apply e.injective
    simp [hs]
  · rintro ⟨r, hr⟩
    refine ⟨e r, ?_⟩
    simpa using congrArg e hr

/-- Pull back a two-generator ideal span along a ring equivalence. -/
theorem comap_span_pair_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a b : S) :
    Ideal.comap e.toRingHom (span ({a, b} : Set S)) =
      span ({e.symm a, e.symm b} : Set R) := by
  ext z
  change e z ∈ span ({a, b} : Set S) ↔ z ∈ span ({e.symm a, e.symm b} : Set R)
  rw [mem_span_pair, mem_span_pair]
  constructor
  · rintro ⟨u, v, huv⟩
    refine ⟨e.symm u, e.symm v, ?_⟩
    apply e.injective
    simp [huv]
  · rintro ⟨u, v, huv⟩
    refine ⟨e u, e v, ?_⟩
    simpa using congrArg e huv

/-- Pulling ideals back along a ring equivalence preserves ideal products. -/
theorem comap_mul_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I J : Ideal S) :
    Ideal.comap (e : R →+* S) (I * J) =
      Ideal.comap (e : R →+* S) I * Ideal.comap (e : R →+* S) J := by
  apply_fun Ideal.map (e : R →+* S) using fun A B h =>
    calc
      A = Ideal.comap (e : R →+* S) (Ideal.map (e : R →+* S) A) := by
        rw [Ideal.comap_map_of_bijective (f := (e : R →+* S)) e.bijective]
      _ = Ideal.comap (e : R →+* S) (Ideal.map (e : R →+* S) B) := by rw [h]
      _ = B := by
        rw [Ideal.comap_map_of_bijective (f := (e : R →+* S)) e.bijective]
  rw [Ideal.map_comap_of_surjective (e : R →+* S) e.surjective]
  rw [Ideal.map_mul]
  rw [Ideal.map_comap_of_surjective (e : R →+* S) e.surjective]
  rw [Ideal.map_comap_of_surjective (e : R →+* S) e.surjective]

/-- Pulling back a product of a principal ideal and another ideal along a ring
equivalence preserves the principal generator. -/
theorem comap_span_singleton_mul_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : S) (I : Ideal S) :
    Ideal.comap (e : R →+* S) (span ({x} : Set S) * I) =
      span ({e.symm x} : Set R) * Ideal.comap (e : R →+* S) I := by
  rw [comap_mul_of_ringEquiv, comap_span_singleton_of_ringEquiv]

end Ideal
