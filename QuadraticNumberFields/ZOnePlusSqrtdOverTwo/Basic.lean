/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import QNFMathlib.Algebra.QuadraticAlgebra.Defs
import QuadraticNumberFields.RingOfIntegers.HalfInt

/-!
# The Ring `ℤ[(1 + √(1 + 4k)) / 2]`

This file defines and studies the ring `ZOnePlusSqrtdOverTwo k`, which is the
candidate ring of integers for quadratic fields with `d ≡ 1 (mod 4)`.
When `d = 1 + 4k`, we have `𝓞(Q(√d)) ≅ ℤ[(1+√d)/2]`.

## Main Definitions

* `ZOnePlusSqrtdOverTwo k`: The ring `ℤ[(1 + √(1+4k))/2]` modeled as
  `QuadraticAlgebra ℤ k 1` (satisfying `ω² = ω + k`).
* `Qsqrtd.omega k`: The generator `ω = (1 + √(1+4k))/2` in `Q(√(1+4k))`.
* `Qsqrtd.Zomega k`: The subalgebra `ℤ[ω]` as a `Subalgebra`.
* `ZOnePlusSqrtdOverTwo.toQsqrtdHom`: Ring hom embedding into `Q(√(1+4k))`.
* `ZOnePlusSqrtdOverTwo.ofZsqrtdHom`: The inclusion
  `ℤ[√(1+4k)] ↪ ℤ[(1+√(1+4k))/2]`.
* `ZOnePlusSqrtdOverTwo.carrierSet`: The image as a set.

## Main Theorems

* `ZOnePlusSqrtdOverTwo.toQsqrtdHom_injective`: The embedding is injective.
* `ZOnePlusSqrtdOverTwo.mem_range_ofZsqrtdHom_iff_even_im`: The suborder
  `ℤ[√(1+4k)]` is the even-`ω`-coefficient part of `ℤ[ω]`.
* `ZOnePlusSqrtdOverTwo.halfInt_mem_carrierSet_iff_same_parity`:
  A half-integer is in the carrier iff its coordinates have the same parity.
-/

namespace Qsqrtd

/-- The discriminant-like parameter `1 + 4k` viewed in `ℚ`. -/
abbrev d_of_k (k : ℤ) : ℚ := ((1 + 4 * k : ℤ) : ℚ)

/-- `ω_k = (1 + √(1 + 4k)) / 2` in `Q(√(1 + 4k))`. -/
def omega (k : ℤ) : Qsqrtd (d_of_k k) := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩

/-- The order candidate `ℤ[ω_k]` with `ω_k = (1 + √(1 + 4k)) / 2`. -/
abbrev Zomega (k : ℤ) : Subalgebra ℤ (Qsqrtd (d_of_k k)) :=
  Algebra.adjoin ℤ ({omega k} : Set (Qsqrtd (d_of_k k)))

lemma omega_mem_Zomega (k : ℤ) : omega k ∈ Zomega k :=
  Algebra.subset_adjoin (by simp)

end Qsqrtd

open QuadraticNumberFields

/-- Algebraic model of `ℤ[(1 + √(1 + 4d))/2]` via `ω^2 = ω + d`.
In `QuadraticAlgebra R a b`, one has `ω^2 = a + b * ω`, so this is
`QuadraticAlgebra ℤ d 1` (not `QuadraticAlgebra ℤ 1 d`). -/
abbrev ZOnePlusSqrtdOverTwo (d : ℤ) : Type := QuadraticAlgebra ℤ d 1

namespace ZOnePlusSqrtdOverTwo

/-- Ambient parameter in `ℚ`: `1 + 4d`. -/
abbrev qParam (d : ℤ) : ℚ := Qsqrtd.d_of_k d

/-- The norm on `ℤ[(1 + √(1 + 4d))/2]` as a `MonoidHom` to `ℤ`. -/
abbrev normHom (d : ℤ) : ZOnePlusSqrtdOverTwo d →* ℤ :=
  QuadraticAlgebra.norm

theorem normHom_apply (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    normHom d z = QuadraticAlgebra.norm z :=
  rfl

/-- The norm on the unit group of `ℤ[(1 + √(1 + 4d))/2]`, as a `MonoidHom` to `ℤˣ`. -/
abbrev normUnitsHom (d : ℤ) : (ZOnePlusSqrtdOverTwo d)ˣ →* ℤˣ :=
  Units.map (normHom d)

theorem normUnitsHom_coe (d : ℤ) (u : (ZOnePlusSqrtdOverTwo d)ˣ) :
    ((normUnitsHom d u : ℤˣ) : ℤ) = QuadraticAlgebra.norm (u : ZOnePlusSqrtdOverTwo d) := by
  simp [normUnitsHom, normHom]

/-- The norm of `x + y·ω` in coordinates: `‖x + y·ω‖ = x² + x·y - d·y²`. -/
@[simp]
theorem norm_mk (d x y : ℤ) :
    QuadraticAlgebra.norm (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d) = x ^ 2 + x * y - d * y ^ 2 := by
  have h : QuadraticAlgebra.norm (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d) =
      x * x + 1 * x * y - d * y * y := QuadraticAlgebra.norm_def _
  rw [h]; ring

/-- `x + y·ω` is a unit of `ℤ[(1 + √(1 + 4d))/2]` iff `x² + x·y - d·y² = ±1`. -/
theorem isUnit_mk_iff {d x y : ℤ} :
    IsUnit (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d) ↔
      x ^ 2 + x * y - d * y ^ 2 = 1 ∨ x ^ 2 + x * y - d * y ^ 2 = -1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff, norm_mk]

/-! ## Reduction modulo `2` -/

/-- Coordinate reduction modulo `2` for `ℤ[(1 + √(1 + 4d)) / 2]`. -/
noncomputable def modTwoHom (d : ℤ) :
    ZOnePlusSqrtdOverTwo d →+* QuadraticAlgebra (ZMod 2) (d : ZMod 2) 1 where
  toFun z := ⟨(z.re : ZMod 2), (z.im : ZMod 2)⟩
  map_one' := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' := by
    intro x y
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  map_zero' := by
    ext <;> simp [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
  map_add' := by
    intro x y
    ext <;> simp [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]

@[simp]
theorem modTwoHom_apply (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    modTwoHom d z = ⟨(z.re : ZMod 2), (z.im : ZMod 2)⟩ :=
  rfl

/-- The coordinate reduction modulo `2` is onto. -/
theorem modTwoHom_surjective (d : ℤ) : Function.Surjective (modTwoHom d) := by
  intro z
  rcases ZMod.intCast_surjective z.re with ⟨a, ha⟩
  rcases ZMod.intCast_surjective z.im with ⟨b, hb⟩
  refine ⟨⟨a, b⟩, ?_⟩
  ext
  · simpa [modTwoHom] using ha
  · simpa [modTwoHom] using hb

/-- An element reduces to zero modulo `2` iff both coordinates are even. -/
lemma modTwoHom_eq_zero_iff (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    modTwoHom d z = 0 ↔ (2 : ℤ) ∣ z.re ∧ (2 : ℤ) ∣ z.im := by
  constructor
  · intro hz
    have hre : (z.re : ZMod 2) = 0 := by
      simpa [modTwoHom] using congrArg QuadraticAlgebra.re hz
    have him : (z.im : ZMod 2) = 0 := by
      simpa [modTwoHom] using congrArg QuadraticAlgebra.im hz
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd z.re 2).mp hre,
      (ZMod.intCast_zmod_eq_zero_iff_dvd z.im 2).mp him⟩
  · rintro ⟨hre, him⟩
    ext <;> simp [modTwoHom,
      (ZMod.intCast_zmod_eq_zero_iff_dvd z.re 2).mpr hre,
      (ZMod.intCast_zmod_eq_zero_iff_dvd z.im 2).mpr him]

/-- Divisibility by `2` in the half-integral order is coordinatewise evenness. -/
lemma two_dvd_iff (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (2 : ZOnePlusSqrtdOverTwo d) ∣ z ↔ (2 : ℤ) ∣ z.re ∧ (2 : ℤ) ∣ z.im := by
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · refine ⟨w.re, ?_⟩
      change (⟨2, 0⟩ * w).re = 2 * w.re
      simp [QuadraticAlgebra.re_mul]
    · refine ⟨w.im, ?_⟩
      change (⟨2, 0⟩ * w).im = 2 * w.im
      simp [QuadraticAlgebra.im_mul]
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨⟨a, b⟩, ?_⟩
    ext
    · change z.re = (⟨2, 0⟩ * (⟨a, b⟩ : ZOnePlusSqrtdOverTwo d)).re
      simp [ha]
    · change z.im = (⟨2, 0⟩ * (⟨a, b⟩ : ZOnePlusSqrtdOverTwo d)).im
      simp [hb]

/-- The kernel of coordinate reduction modulo `2` is the principal ideal `(2)`. -/
lemma ker_modTwoHom (d : ℤ) :
    RingHom.ker (modTwoHom d) = Ideal.span ({(2 : ZOnePlusSqrtdOverTwo d)} : Set _) := by
  ext z
  rw [RingHom.mem_ker, modTwoHom_eq_zero_iff, Ideal.mem_span_singleton, two_dvd_iff]

/-- The quotient by `(2)` is the quadratic algebra obtained by reducing the
parameter modulo `2`. -/
noncomputable def quotientSpanTwoEquivModTwo (d : ℤ) :
    (ZOnePlusSqrtdOverTwo d ⧸ Ideal.span ({(2 : ZOnePlusSqrtdOverTwo d)} : Set _)) ≃+*
      QuadraticAlgebra (ZMod 2) (d : ZMod 2) 1 :=
  (Ideal.quotEquivOfEq (ker_modTwoHom d).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := modTwoHom d) (modTwoHom_surjective d))

/-- The reduced quadratic algebra modulo `2` has at most three units. -/
lemma modTwoTarget_units_card_le_three (d : ℤ) :
    Fintype.card (QuadraticAlgebra (ZMod 2) (d : ZMod 2) 1)ˣ ≤ 3 := by
  let R := QuadraticAlgebra (ZMod 2) (d : ZMod 2) 1
  let e : Rˣ ↪ {x : R // x ≠ 0} :=
    { toFun := fun u => ⟨(u : R), u.ne_zero⟩
      inj' := by
        intro u v h
        exact Units.ext (congrArg Subtype.val h) }
  have hle := Fintype.card_le_of_embedding e
  have hnonzero : Fintype.card {x : R // x ≠ 0} = 3 := by
    rw [Fintype.card_subtype_compl (p := fun x : R => x = 0)]
    rw [QuadraticAlgebra.card]
    norm_num
  simpa [hnonzero] using hle

/-- If the half-integral parameter is odd, the reduced quadratic algebra modulo
`2` has exactly three units. -/
lemma modTwoTarget_units_card_eq_three_of_intCast_eq_one
    (d : ℤ) (hd : (d : ZMod 2) = 1) :
    Fintype.card (QuadraticAlgebra (ZMod 2) (d : ZMod 2) 1)ˣ = 3 := by
  rw [hd]
  decide

/-- The quotient by `(2)` is finite, via coordinate reduction modulo `2`. -/
noncomputable instance instFintypeQuotientSpanTwo (d : ℤ) :
    Fintype (ZOnePlusSqrtdOverTwo d ⧸
      Ideal.span ({(2 : ZOnePlusSqrtdOverTwo d)} : Set _)) :=
  Fintype.ofEquiv (QuadraticAlgebra (ZMod 2) (d : ZMod 2) 1)
    (quotientSpanTwoEquivModTwo d).symm.toEquiv

/-- The unit group of the quotient by `(2)` has at most three elements. -/
lemma quotient_span_two_units_card_le_three (d : ℤ) :
    Nat.card (ZOnePlusSqrtdOverTwo d ⧸
      Ideal.span ({(2 : ZOnePlusSqrtdOverTwo d)} : Set _))ˣ ≤ 3 := by
  rw [Nat.card_congr (Units.mapEquiv (quotientSpanTwoEquivModTwo d).toMulEquiv).toEquiv]
  rw [Nat.card_eq_fintype_card]
  exact modTwoTarget_units_card_le_three d

/-- If the half-integral parameter is odd, the unit group of the quotient by
`(2)` has exactly three elements. -/
lemma quotient_span_two_units_card_eq_three_of_intCast_eq_one
    (d : ℤ) (hd : (d : ZMod 2) = 1) :
    Nat.card (ZOnePlusSqrtdOverTwo d ⧸
      Ideal.span ({(2 : ZOnePlusSqrtdOverTwo d)} : Set _))ˣ = 3 := by
  rw [Nat.card_congr (Units.mapEquiv (quotientSpanTwoEquivModTwo d).toMulEquiv).toEquiv]
  rw [Nat.card_eq_fintype_card]
  exact modTwoTarget_units_card_eq_three_of_intCast_eq_one d hd

/-- Coordinate-level embedding candidate into `Q(√(1 + 4d))`. -/
def toQsqrtdFun (d : ℤ) : ZOnePlusSqrtdOverTwo d → Qsqrtd (qParam d) :=
  -- Send `r + sω` to `r + s * (1 + √(1 + 4d)) / 2`,
  -- so the real coordinate is `r + s/2` and the `√d`-coordinate is `s/2`.
  fun x => ⟨(x.re : ℚ) + (x.im : ℚ) / 2, (x.im : ℚ) / 2⟩

/-- Coordinate-level embedding as a ring hom into `Q(√(1 + 4d))`. -/
def toQsqrtdHom (d : ℤ) : ZOnePlusSqrtdOverTwo d →+* Qsqrtd (qParam d) where
  toFun := toQsqrtdFun d
  map_one' := by
    ext <;> simp [toQsqrtdFun, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' := by
    -- The multiplication formulas agree because `ω² = ω + d`,
    -- which is exactly the relation defining `QuadraticAlgebra ℤ d 1`.
    intro x y
    ext <;>
      simp [toQsqrtdFun, qParam, Qsqrtd.d_of_k,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;>
      ring
  map_zero' := by
    ext <;> simp [toQsqrtdFun, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
  map_add' := by
    intro x y
    ext <;> simp [toQsqrtdFun, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;> ring

@[simp] theorem toQsqrtdHom_apply (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    toQsqrtdHom d z = toQsqrtdFun d z := rfl

@[simp]
theorem toQsqrtdFun_re (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (toQsqrtdFun d z).re = (z.re : ℚ) + (z.im : ℚ) / 2 :=
  rfl

@[simp]
theorem toQsqrtdFun_im (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (toQsqrtdFun d z).im = (z.im : ℚ) / 2 :=
  rfl

@[simp]
theorem toQsqrtdHom_re (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (toQsqrtdHom d z).re = (z.re : ℚ) + (z.im : ℚ) / 2 :=
  rfl

@[simp]
theorem toQsqrtdHom_im (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (toQsqrtdHom d z).im = (z.im : ℚ) / 2 :=
  rfl

@[simp]
theorem toQsqrtdHom_mk_re (d x y : ℤ) :
    (toQsqrtdHom d (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d)).re = (x : ℚ) + (y : ℚ) / 2 :=
  rfl

@[simp]
theorem toQsqrtdHom_mk_im (d x y : ℤ) :
    (toQsqrtdHom d (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d)).im = (y : ℚ) / 2 :=
  rfl

/-- The canonical map `toQsqrtdHom` is injective. -/
theorem toQsqrtdHom_injective (d : ℤ) : Function.Injective (toQsqrtdHom d) := by
  intro x y hxy
  -- Equality of images first identifies the `ω`-coefficients from the imaginary parts,
  -- then the constant terms from the real parts.
  have himHalf : (x.im : ℚ) / 2 = (y.im : ℚ) / 2 := by
    simpa [toQsqrtdHom, toQsqrtdFun] using congrArg QuadraticAlgebra.im hxy
  have himQ : (x.im : ℚ) = (y.im : ℚ) := by
    nlinarith [himHalf]
  have hreHalf : (x.re : ℚ) + (x.im : ℚ) / 2 = (y.re : ℚ) + (y.im : ℚ) / 2 := by
    simpa [toQsqrtdHom, toQsqrtdFun] using congrArg QuadraticAlgebra.re hxy
  have hreQ : (x.re : ℚ) = (y.re : ℚ) := by
    nlinarith [hreHalf, himQ]
  ext
  · exact_mod_cast hreQ
  · exact_mod_cast himQ

/-- The natural inclusion `ℤ[√(1+4k)] ↪ ℤ[(1+√(1+4k))/2]`.

It sends `a + b√(1+4k)` to `(a - b) + 2bω`, using `√(1+4k) = 2ω - 1`.
This is the abstract conductor-`2` suborder inside the half-integral order. -/
def ofZsqrtdHom (k : ℤ) : Zsqrtd (1 + 4 * k) →+* ZOnePlusSqrtdOverTwo k where
  toFun := fun z => ⟨z.re - z.im, 2 * z.im⟩
  map_one' := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' := by
    intro x y
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
  map_zero' := by
    ext <;> simp [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
  map_add' := by
    intro x y
    ext <;> simp [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;> ring

/-- The inclusion `ofZsqrtdHom` is compatible with the two ambient embeddings
into `Q(√(1+4k))`. -/
theorem toQsqrtdHom_ofZsqrtdHom (k : ℤ) (z : Zsqrtd (1 + 4 * k)) :
    toQsqrtdHom k (ofZsqrtdHom k z) =
      Zsqrtd.toQsqrtdHom (1 + 4 * k) z := by
  ext <;> simp [ofZsqrtdHom, toQsqrtdHom, toQsqrtdFun, Zsqrtd.toQsqrtdHom]

/-- The inclusion `ℤ[√(1+4k)] ↪ ℤ[(1+√(1+4k))/2]` is injective. -/
theorem ofZsqrtdHom_injective (k : ℤ) : Function.Injective (ofZsqrtdHom k) := by
  intro x y hxy
  ext
  · have hre : x.re - x.im = y.re - y.im := by
      simpa [ofZsqrtdHom] using congrArg QuadraticAlgebra.re hxy
    have him : 2 * x.im = 2 * y.im := by
      simpa [ofZsqrtdHom] using congrArg QuadraticAlgebra.im hxy
    omega
  · have him : 2 * x.im = 2 * y.im := by
      simpa [ofZsqrtdHom] using congrArg QuadraticAlgebra.im hxy
    omega

/-- The image of `ℤ[√(1+4k)]` inside `ℤ[(1+√(1+4k))/2]` consists exactly of
the elements with even `ω`-coefficient. -/
theorem mem_range_ofZsqrtdHom_iff_even_im (k : ℤ) (w : ZOnePlusSqrtdOverTwo k) :
    (∃ z : Zsqrtd (1 + 4 * k), ofZsqrtdHom k z = w) ↔ 2 ∣ w.im := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.im, rfl⟩
  · rintro ⟨b, hb⟩
    refine ⟨⟨w.re + b, b⟩, ?_⟩
    ext <;> simp [ofZsqrtdHom, hb]

/-- Candidate carrier set of `ℤ[(1 + √(1 + 4d))/2]` inside `Q(√(1 + 4d))`. -/
def carrierSet (d : ℤ) : Set (Qsqrtd (qParam d)) := Set.range (toQsqrtdFun d)

/-- A half-integer element belongs to the `ℤ[(1 + √(1+4k))/2]` carrier iff the two
numerators have the same parity. -/
theorem halfInt_mem_carrierSet_iff_same_parity (k a' b' : ℤ) :
    (∃ z : ZOnePlusSqrtdOverTwo k,
      toQsqrtdFun k z = RingOfIntegers.halfInt (1 + 4 * k) a' b') ↔
      a' % 2 = b' % 2 := by
  constructor
  · rintro ⟨z, hz⟩
    -- If `(a' + b'√d)/2 = r + sω`, then necessarily `s = b'`
    -- and `a' = 2r + b'`, so `a'` and `b'` have the same parity.
    have him : z.im / 2 = (b' : ℚ) / 2 := by
      simpa [toQsqrtdFun, RingOfIntegers.halfInt] using
        congrArg QuadraticAlgebra.im hz
    have hbq : z.im = (b' : ℚ) := by
      nlinarith [him]
    have hreq : z.re + z.im / 2 = (a' : ℚ) / 2 := by
      simpa [toQsqrtdFun, RingOfIntegers.halfInt] using
        congrArg QuadraticAlgebra.re hz
    have haq : 2 * z.re + z.im = (a' : ℚ) := by
      nlinarith [hreq]
    have ha : 2 * z.re + z.im = a' := by exact_mod_cast haq
    have hb : z.im = b' := by exact_mod_cast hbq
    have ha' : 2 * z.re + b' = a' := by simpa [hb] using ha
    omega
  · intro hpar
    -- Conversely, same parity means `a' - b' = 2t`, so
    -- `(a' + b'√d)/2 = t + b' * ω`.
    have hmod : (a' - b') % 2 = 0 := by
      omega
    have hdiv : (2 : ℤ) ∣ (a' - b') := Int.dvd_iff_emod_eq_zero.mpr hmod
    rcases hdiv with ⟨t, ht⟩
    have hrepr : a' = 2 * t + b' := by
      omega
    refine ⟨⟨t, b'⟩, ?_⟩
    ext
    · simp [toQsqrtdFun, RingOfIntegers.halfInt, hrepr]
      ring
    · simp [toQsqrtdFun, RingOfIntegers.halfInt]

/-- Equivalent set-membership form of `halfInt_mem_carrierSet_iff_same_parity`. -/
theorem halfInt_mem_carrierSet_iff_same_parity_set (k a' b' : ℤ) :
    RingOfIntegers.halfInt (1 + 4 * k) a' b' ∈ carrierSet k ↔
      a' % 2 = b' % 2 :=
  by simpa [carrierSet] using (halfInt_mem_carrierSet_iff_same_parity k a' b')

end ZOnePlusSqrtdOverTwo
