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

/-! ## Computable Dirichlet composition

The composition is carried out in two steps:

1. **Replace** the right factor `R` by a properly equivalent representative `R'`
   whose leading coefficient is coprime to `Q.a` (`unitedRep`).
2. **Compose** using the classical Gauss formula, with the middle coefficient `B`
   chosen via the Chinese Remainder Theorem to satisfy simultaneously
   `B ≡ Q.b (mod 2·Q.a)` and `B ≡ R'.b (mod 2·R'.a)`.  Because `Q.a` and `R'.a`
   are coprime (step 1), the CRT solution exists and the final division for `c`
   is exact.

This bypasses the three-term Bézout-`σ` construction of `composeUnited` and
gives a form whose discriminant matches `Q.disc` unconditionally. -/

/-- The adjusted middle coefficient for Gauss composition, chosen to satisfy
`B ≡ Q.b (mod 2·Q.a)` and `B ≡ R.b (mod 2·R.a)` simultaneously.  The two
leading coefficients are assumed coprime (e.g. after `unitedRep`). -/
def composeMiddleB (Q R : BinaryQuadraticForm) : ℤ :=
  let d := (R.b - Q.b) / 2
  let x := d * Int.gcdA Q.a R.a
  Q.b + 2 * Q.a * x

/-- `composeMiddleB` satisfies `B ≡ Q.b (mod 2·Q.a)`.
Proof: `B = Q.b + 2·Q.a·x`, so `2·Q.a ∣ B - Q.b`. -/
theorem composeMiddleB_modEq_left (Q R : BinaryQuadraticForm) :
    composeMiddleB Q R ≡ Q.b [ZMOD 2 * Q.a] := by
  rw [composeMiddleB, Int.modEq_iff_dvd]
  -- Goal: 2*Q.a ∣ Q.b - (Q.b + 2*Q.a*x)  =>  2*Q.a ∣ -(2*Q.a*x)
  have : Q.b - (Q.b + 2 * Q.a * (((R.b - Q.b) / 2) * Int.gcdA Q.a R.a)) =
      -((2 * Q.a) * (((R.b - Q.b) / 2) * Int.gcdA Q.a R.a)) := by ring
  rw [this, dvd_neg]
  exact dvd_mul_right _ _

/-- Computable Dirichlet composition.  The right factor is first replaced by a
properly equivalent representative whose leading coefficient is coprime to
`Q.a`; then the middle coefficient is chosen via the CRT to make the final
`c`-division exact. -/
def composeForm (Q R : BinaryQuadraticForm)
    (hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    BinaryQuadraticForm :=
  let R' := unitedRep Q R hR hQa
  let B := composeMiddleB Q R'
  { a := Q.a * R'.a
    b := B
    c := (B ^ 2 - Q.disc) / (4 * (Q.a * R'.a)) }

@[simp] theorem composeForm_a (Q R : BinaryQuadraticForm)
    (hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    (composeForm Q R hQR hR hQa).a =
      Q.a * (unitedRep Q R hR hQa).a :=
  rfl

@[simp] theorem composeForm_b (Q R : BinaryQuadraticForm)
    (hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    (composeForm Q R hQR hR hQa).b =
      composeMiddleB Q (unitedRep Q R hR hQa) :=
  rfl

@[simp] theorem composeForm_c (Q R : BinaryQuadraticForm)
    (hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
    (composeForm Q R hQR hR hQa).c =
      ((composeMiddleB Q (unitedRep Q R hR hQa)) ^ 2 - Q.disc) /
        (4 * (Q.a * (unitedRep Q R hR hQa).a)) :=
  rfl

/-- **Discriminant preservation for computable composition** (statement only;
the CRT divisibility proof is a non-trivial number-theory lemma to be
completed in a follow-up).

The result form has the same discriminant as `Q` (and thus `R`).  The
proof uses the Chinese Remainder Theorem: the adjusted `B` satisfies
`B ≡ Q.b (mod 2·Q.a)` and `B ≡ R'.b (mod 2·R'.a)`; since `Q.a` and `R'.a`
are coprime, `B² - Q.disc` is divisible by `4·Q.a·R'.a`, making the final
division exact. -/
theorem disc_composeForm (Q R : BinaryQuadraticForm)
    (hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0)
    (_hQpos : Q.IsPositiveDefinite) (_hRpos : R.IsPositiveDefinite) :
    (composeForm Q R hQR hR hQa).disc = Q.disc := by
  -- The `#eval` regression tests below numerically verify this for concrete
  -- forms of discriminant -84.  The general CRT divisibility proof:
  --   1. B ≡ Q.b (mod 2·Q.a) ⇒ 4·Q.a ∣ B² - Q.disc  (by algebra)
  --   2. B ≡ R'.b (mod 2·R'.a) ⇒ 4·R'.a ∣ B² - Q.disc
  --   3. gcd(Q.a, R'.a) = 1 ⇒ 4·Q.a·R'.a ∣ B² - Q.disc
  --   4. Therefore the `c`-division is exact, so disc = Q.disc.
  -- TODO: formalize steps 1-3.
  sorry

/-! ## Regression: computable composition on `d = -21` spike forms

The spike (Design Doc §2) confirms that `fieldDiscriminant (-21 : ℚ) = -84` and
the primitive reduced forms are `[(1,0,21), (2,2,11), (3,0,7), (5,4,5)]`.
These `#eval` tests verify that `composeForm` runs to a concrete integer triple
without errors.

The CRT-adjusted middle coefficient guarantees exact division, so the
output discriminant equals `Q.disc` unconditionally.  The `example` blocks
double-check the full form triple and its discriminant. -/

/-- Regression: `composeForm` on `(1,0,21)` × `(2,2,11)`.
Principal form × non-principal gives the non-principal form back
(class-group identity law).  CRT-adjusted output: `(11, -2, 2)`, disc = `-84`. -/
def testComposeFormIdentity : BinaryQuadraticForm :=
  let Q := BinaryQuadraticForm.mk 1 0 21
  let R := BinaryQuadraticForm.mk 2 2 11
  have hQR : Q.disc = R.disc := by
    unfold disc; decide
  have hR : R.IsPrimitive := by
    unfold IsPrimitive; decide
  have hQa : Q.a ≠ 0 := by decide
  composeForm Q R hQR hR hQa

#eval testComposeFormIdentity

/-- The output triple matches the CRT algorithm's expected values. -/
example : testComposeFormIdentity.a = 11 := by native_decide
example : testComposeFormIdentity.b = -2 := by native_decide
example : testComposeFormIdentity.c = 2 := by native_decide
/-- Discriminant preserved. -/
example : testComposeFormIdentity.disc = -84 := by
  unfold testComposeFormIdentity disc; native_decide

/-- `composeForm` with the principal form `(1,0,21)` and `(5,4,5)`.
CRT-adjusted output: `(5, -4, 5)`, disc = `-84`. -/
def testComposeFormPrincipal2 : BinaryQuadraticForm :=
  let Q := BinaryQuadraticForm.mk 1 0 21
  let R := BinaryQuadraticForm.mk 5 4 5
  have hQR : Q.disc = R.disc := by
    unfold disc; decide
  have hR : R.IsPrimitive := by
    unfold IsPrimitive; decide
  have hQa : Q.a ≠ 0 := by decide
  composeForm Q R hQR hR hQa

#eval testComposeFormPrincipal2

example : testComposeFormPrincipal2.a = 5 := by native_decide
example : testComposeFormPrincipal2.b = -4 := by native_decide
example : testComposeFormPrincipal2.c = 5 := by native_decide
example : testComposeFormPrincipal2.disc = -84 := by
  unfold testComposeFormPrincipal2 disc; native_decide

/-- `composeForm` of `(3,0,7)` with itself (order-2 element).
CRT-adjusted output: `(21, 0, 1)`, disc = `-84`. -/
def testComposeFormOrder2 : BinaryQuadraticForm :=
  let Q := BinaryQuadraticForm.mk 3 0 7
  let R := BinaryQuadraticForm.mk 3 0 7
  have hQR : Q.disc = R.disc := by
    unfold disc; decide
  have hR : R.IsPrimitive := by
    unfold IsPrimitive; decide
  have hQa : Q.a ≠ 0 := by decide
  composeForm Q R hQR hR hQa

#eval testComposeFormOrder2

example : testComposeFormOrder2.a = 21 := by native_decide
example : testComposeFormOrder2.b = 0 := by native_decide
example : testComposeFormOrder2.c = 1 := by native_decide
example : testComposeFormOrder2.disc = -84 := by
  unfold testComposeFormOrder2 disc; native_decide

/-- Verify that all four reduced forms of discriminant `-84` have equal
discriminant (a precondition for composition). -/
example : (BinaryQuadraticForm.mk 1 0 21).disc = -84 := by
  unfold disc; native_decide
example : (BinaryQuadraticForm.mk 2 2 11).disc = -84 := by
  unfold disc; native_decide
example : (BinaryQuadraticForm.mk 3 0 7).disc = -84 := by
  unfold disc; native_decide
example : (BinaryQuadraticForm.mk 5 4 5).disc = -84 := by
  unfold disc; native_decide

/-- All four forms are primitive. -/
example : (BinaryQuadraticForm.mk 1 0 21).IsPrimitive := by
  unfold IsPrimitive; decide
example : (BinaryQuadraticForm.mk 2 2 11).IsPrimitive := by
  unfold IsPrimitive; decide
example : (BinaryQuadraticForm.mk 3 0 7).IsPrimitive := by
  unfold IsPrimitive; decide
example : (BinaryQuadraticForm.mk 5 4 5).IsPrimitive := by
  unfold IsPrimitive; decide

end BinaryQuadraticForm
end QuadraticNumberFields
