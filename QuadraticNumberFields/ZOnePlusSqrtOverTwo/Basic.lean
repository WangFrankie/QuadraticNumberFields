/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.HalfInt

/-!
# The Ring `ℤ[(1 + √(1 + 4k)) / 2]`

This file defines and studies the ring `ZOnePlusSqrtOverTwo k`, which is the
candidate ring of integers for quadratic fields with `d ≡ 1 (mod 4)`.
When `d = 1 + 4k`, we have `𝓞(Q(√d)) ≅ ℤ[(1+√d)/2]`.

## Main Definitions

* `ZOnePlusSqrtOverTwo k`: The ring `ℤ[(1 + √(1+4k))/2]` modeled as
  `QuadraticAlgebra ℤ k 1` (satisfying `ω² = ω + k`).
* `Qsqrtd.omega k`: The generator `ω = (1 + √(1+4k))/2` in `Q(√(1+4k))`.
* `Qsqrtd.Zomega k`: The subalgebra `ℤ[ω]` as a `Subalgebra`.
* `ZOnePlusSqrtOverTwo.toQsqrtdHom`: Ring hom embedding into `Q(√(1+4k))`.
* `ZOnePlusSqrtOverTwo.carrierSet`: The image as a set.

## Main Theorems

* `ZOnePlusSqrtOverTwo.toQsqrtdHom_injective`: The embedding is injective.
* `ZOnePlusSqrtOverTwo.halfInt_mem_carrierSet_iff_same_parity`:
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

/-- Algebraic model of `ℤ[(1 + √(1 + 4d))/2]` via `ω^2 = ω + d`.
In `QuadraticAlgebra R a b`, one has `ω^2 = a + b * ω`, so this is
`QuadraticAlgebra ℤ d 1` (not `QuadraticAlgebra ℤ 1 d`). -/
abbrev ZOnePlusSqrtOverTwo (d : ℤ) : Type := QuadraticAlgebra ℤ d 1

namespace ZOnePlusSqrtOverTwo

/-- Ambient parameter in `ℚ`: `1 + 4d`. -/
abbrev qParam (d : ℤ) : ℚ := Qsqrtd.d_of_k d

/-- Coordinate-level embedding candidate into `Q(√(1 + 4d))`. -/
def toQsqrtdFun (d : ℤ) : ZOnePlusSqrtOverTwo d → Qsqrtd (qParam d) :=
  -- Send `r + sω` to `r + s * (1 + √(1 + 4d)) / 2`,
  -- so the real coordinate is `r + s/2` and the `√d`-coordinate is `s/2`.
  fun x => ⟨(x.re : ℚ) + (x.im : ℚ) / 2, (x.im : ℚ) / 2⟩

/-- Coordinate-level embedding as a ring hom into `Q(√(1 + 4d))`. -/
def toQsqrtdHom (d : ℤ) : ZOnePlusSqrtOverTwo d →+* Qsqrtd (qParam d) where
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

@[simp] theorem toQsqrtdHom_apply (d : ℤ) (z : ZOnePlusSqrtOverTwo d) :
    toQsqrtdHom d z = toQsqrtdFun d z := rfl

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

/-- Candidate carrier set of `ℤ[(1 + √(1 + 4d))/2]` inside `Q(√(1 + 4d))`. -/
def carrierSet (d : ℤ) : Set (Qsqrtd (qParam d)) := Set.range (toQsqrtdFun d)

/-- A half-integer element belongs to the `ℤ[(1 + √(1+4k))/2]` carrier iff the two
numerators have the same parity. -/
theorem halfInt_mem_carrierSet_iff_same_parity (k a' b' : ℤ) :
    (∃ z : ZOnePlusSqrtOverTwo k,
      toQsqrtdFun k z = QuadraticNumberFields.RingOfIntegers.halfInt (1 + 4 * k) a' b') ↔
      a' % 2 = b' % 2 := by
  constructor
  · rintro ⟨z, hz⟩
    -- If `(a' + b'√d)/2 = r + sω`, then necessarily `s = b'`
    -- and `a' = 2r + b'`, so `a'` and `b'` have the same parity.
    have him : z.im / 2 = (b' : ℚ) / 2 := by
      simpa [toQsqrtdFun, QuadraticNumberFields.RingOfIntegers.halfInt] using
        congrArg QuadraticAlgebra.im hz
    have hbq : z.im = (b' : ℚ) := by
      nlinarith [him]
    have hreq : z.re + z.im / 2 = (a' : ℚ) / 2 := by
      simpa [toQsqrtdFun, QuadraticNumberFields.RingOfIntegers.halfInt] using
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
    · simp [toQsqrtdFun, QuadraticNumberFields.RingOfIntegers.halfInt, hrepr]
      ring
    · simp [toQsqrtdFun, QuadraticNumberFields.RingOfIntegers.halfInt]

/-- Equivalent set-membership form of `halfInt_mem_carrierSet_iff_same_parity`. -/
theorem halfInt_mem_carrierSet_iff_same_parity_set (k a' b' : ℤ) :
    QuadraticNumberFields.RingOfIntegers.halfInt (1 + 4 * k) a' b' ∈ carrierSet k ↔
      a' % 2 = b' % 2 :=
  by simpa [carrierSet] using (halfInt_mem_carrierSet_iff_same_parity k a' b')

end ZOnePlusSqrtOverTwo
