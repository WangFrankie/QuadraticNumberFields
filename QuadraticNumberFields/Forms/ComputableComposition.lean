/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.GaussComposition
import Mathlib.Logic.Denumerable

/-!
# Computable Gauss Composition Data

This file makes the data feeding Gauss composition computable, so that a full
computable Dirichlet composition (and ultimately a `decide`/`#eval`-able form
class group) can be built on top of the existing, already-proven composition
theory.

Two pieces are provided:

* `unitedBezout`: a computable replacement for the `Classical.choice`-based
  `UnitedBezout.ofIsUnited`, built directly from `Int.gcdA`/`Int.gcdB`.
* `coprimeEvalVector`: a computable witness for Cox Lemma 2.25
  (`exists_coprime_eval_of_isPrimitive`), extracted by `Nat.find` over the
  `Denumerable` enumeration of `ℤ × ℤ`.  This is the only previously
  noncomputable input to the concordant-representative replacement
  (`exists_concordant_of_sameDiscriminant`); making it computable unblocks a
  computable composition.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-- A computable choice of united Bézout data, built explicitly from
`Int.gcdA`/`Int.gcdB`.  Unlike `UnitedBezout.ofIsUnited`, this does not depend on
`Classical.choice`: the coefficients are computed from `Q.a`, `R.a`, and
`sigma Q R`, and only the `linear_combination` proof field uses the united
hypothesis. -/
def unitedBezout {Q R : BinaryQuadraticForm} (h : Q.IsUnited R) :
    UnitedBezout Q R :=
  let g : ℕ := Int.gcd R.a (sigma Q R)
  { u := Int.gcdA Q.a g
    v := Int.gcdB Q.a g * Int.gcdA R.a (sigma Q R)
    w := Int.gcdB Q.a g * Int.gcdB R.a (sigma Q R)
    linear_combination := by
      have hgcd : Int.gcd Q.a g = 1 := by
        simpa [IsUnited, coeffGCD3, g, Int.gcd] using h.2
      have hbezout_left :
          (1 : ℤ) = Q.a * Int.gcdA Q.a g + (g : ℤ) * Int.gcdB Q.a g := by
        rw [← Int.gcd_eq_gcd_ab Q.a g, hgcd]
        norm_num
      have hbezout_right :
          (g : ℤ) = R.a * Int.gcdA R.a (sigma Q R) +
            sigma Q R * Int.gcdB R.a (sigma Q R) :=
        Int.gcd_eq_gcd_ab R.a (sigma Q R)
      calc
        Int.gcdA Q.a g * Q.a +
            (Int.gcdB Q.a g * Int.gcdA R.a (sigma Q R)) * R.a +
            (Int.gcdB Q.a g * Int.gcdB R.a (sigma Q R)) * sigma Q R
            = Q.a * Int.gcdA Q.a g + (g : ℤ) * Int.gcdB Q.a g := by
              rw [hbezout_right]; ring
        _ = 1 := hbezout_left.symm }

/-- The `n`-th lattice point (via `Denumerable`) is a primitive vector on which
`Q` takes a value coprime to `M`. -/
private def coprimeEvalPred (Q : BinaryQuadraticForm) (M : ℤ) (n : ℕ) : Prop :=
  Int.gcd (Denumerable.ofNat (ℤ × ℤ) n).1 (Denumerable.ofNat (ℤ × ℤ) n).2 = 1 ∧
    Int.gcd (Q.eval (Denumerable.ofNat (ℤ × ℤ) n).1
      (Denumerable.ofNat (ℤ × ℤ) n).2) M = 1

instance (Q : BinaryQuadraticForm) (M : ℤ) : DecidablePred (coprimeEvalPred Q M) :=
  fun n => by unfold coprimeEvalPred; infer_instance

private theorem exists_coprimeEvalPred (Q : BinaryQuadraticForm) (M : ℤ)
    (hQ : Q.IsPrimitive) (hM : M ≠ 0) : ∃ n, coprimeEvalPred Q M n := by
  obtain ⟨x, y, hxy, hcop⟩ := exists_coprime_eval_of_isPrimitive hQ hM
  refine ⟨Encodable.encode (x, y), ?_⟩
  unfold coprimeEvalPred
  rw [Denumerable.ofNat_of_decode (Encodable.encodek (x, y))]
  exact ⟨hxy, hcop⟩

/-- A computable primitive vector `(x, y)` (i.e. `gcd x y = 1`) on which the
primitive form `Q` takes a value coprime to a nonzero integer `M`.

This is a computable witness for `exists_coprime_eval_of_isPrimitive`
(Cox Lemma 2.25), obtained by `Nat.find` over the `Denumerable` enumeration of
`ℤ × ℤ`.  The executable code does not call `Classical.choice`; the existence
proof feeding `Nat.find` is erased at runtime. -/
def coprimeEvalVector (Q : BinaryQuadraticForm) (M : ℤ)
    (hQ : Q.IsPrimitive) (hM : M ≠ 0) : ℤ × ℤ :=
  Denumerable.ofNat (ℤ × ℤ) (Nat.find (exists_coprimeEvalPred Q M hQ hM))

/-- `coprimeEvalVector` is a primitive vector. -/
theorem coprimeEvalVector_gcd (Q : BinaryQuadraticForm) (M : ℤ)
    (hQ : Q.IsPrimitive) (hM : M ≠ 0) :
    Int.gcd (coprimeEvalVector Q M hQ hM).1 (coprimeEvalVector Q M hQ hM).2 = 1 :=
  (Nat.find_spec (exists_coprimeEvalPred Q M hQ hM)).1

/-- `Q` takes a value coprime to `M` at `coprimeEvalVector`. -/
theorem coprimeEvalVector_eval_gcd (Q : BinaryQuadraticForm) (M : ℤ)
    (hQ : Q.IsPrimitive) (hM : M ≠ 0) :
    Int.gcd (Q.eval (coprimeEvalVector Q M hQ hM).1
      (coprimeEvalVector Q M hQ hM).2) M = 1 :=
  (Nat.find_spec (exists_coprimeEvalPred Q M hQ hM)).2

/-! ## Computable united representatives -/

/-- If the first two entries in a triple of coefficients are coprime, then the
three-entry absolute gcd is `1`. -/
theorem coeffGCD3_eq_one_of_gcd_left {x y z : ℤ} (hxy : Int.gcd x y = 1) :
    coeffGCD3 x y z = 1 := by
  have hgcd : Nat.gcd x.natAbs y.natAbs = 1 := by
    simpa [Int.gcd] using hxy
  apply Nat.dvd_one.mp
  rw [← hgcd]
  unfold coeffGCD3
  exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))

/-- A computable representative of `R` whose leading coefficient is coprime to
`Q.a`.

The representative is obtained by finding a primitive vector `(x, y)` on which
`R` represents a value coprime to `Q.a`, then using the explicit
`SL₂(ℤ)` matrix with first column `(x, y)`. -/
def unitedRep (Q R : BinaryQuadraticForm) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    BinaryQuadraticForm :=
  let v := coprimeEvalVector R Q.a hR hQa
  transform R (sl2z_of_coprime v.1 v.2 (coprimeEvalVector_gcd R Q.a hR hQa))

/-- The leading coefficient of `unitedRep` is the represented coprime value. -/
theorem unitedRep_a (Q R : BinaryQuadraticForm) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    (unitedRep Q R hR hQa).a =
      R.eval (coprimeEvalVector R Q.a hR hQa).1 (coprimeEvalVector R Q.a hR hQa).2 := by
  simp [unitedRep, transform_sl2z_of_coprime_a]

/-- The leading coefficient of `unitedRep` is coprime to `Q.a`. -/
theorem gcd_left_a_unitedRep (Q R : BinaryQuadraticForm)
    (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    Int.gcd Q.a (unitedRep Q R hR hQa).a = 1 := by
  rw [unitedRep_a]
  simpa [Int.gcd, Nat.gcd_comm] using coprimeEvalVector_eval_gcd R Q.a hR hQa

/-- `unitedRep` is properly equivalent to the original right factor. -/
theorem unitedRep_properEquivalent (Q R : BinaryQuadraticForm)
    (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    ProperEquivalent R (unitedRep Q R hR hQa) := by
  exact properEquivalent_sl2z_of_coprime R
    (coprimeEvalVector R Q.a hR hQa).1
    (coprimeEvalVector R Q.a hR hQa).2
    (coprimeEvalVector_gcd R Q.a hR hQa)

/-- If `Q` and `R` have the same discriminant, then `unitedRep Q R` is united
with `Q`. -/
theorem unitedRep_isUnited {Q R : BinaryQuadraticForm}
    (hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    Q.IsUnited (unitedRep Q R hR hQa) := by
  refine ⟨?_, ?_⟩
  · exact hQR.trans (disc_eq_of_properEquivalent (unitedRep_properEquivalent Q R hR hQa))
  · exact coeffGCD3_eq_one_of_gcd_left (gcd_left_a_unitedRep Q R hR hQa)

end BinaryQuadraticForm
end QuadraticNumberFields
