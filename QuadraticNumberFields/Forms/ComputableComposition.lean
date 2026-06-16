/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.GaussComposition

/-!
# Computable Gauss Composition Data

This file makes the united-form Bézout data computable, replacing the
`Classical.choice`-based `UnitedBezout.ofIsUnited` with an explicit constructor
built directly from `Int.gcdA`/`Int.gcdB`.  This is the first step toward a
fully computable Dirichlet composition on binary quadratic forms.

The construction mirrors the existential proof
`exists_unitedBezout_of_isUnited`, but returns the structure directly so that
`composeUnited` becomes computable.
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

end BinaryQuadraticForm
end QuadraticNumberFields
