/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Gauss.Composition
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

/-- The computable united representative has positive leading coefficient when
the original right factor is positive definite. -/
theorem unitedRep_a_pos (Q R : BinaryQuadraticForm)
    (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) (hRpos : R.IsPositiveDefinite) :
    0 < (unitedRep Q R hR hQa).a := by
  rw [unitedRep_a]
  have hxy_gcd : Int.gcd (coprimeEvalVector R Q.a hR hQa).1
      (coprimeEvalVector R Q.a hR hQa).2 = 1 :=
    coprimeEvalVector_gcd R Q.a hR hQa
  have hxy_nonzero : (coprimeEvalVector R Q.a hR hQa).1 ≠ 0 ∨
      (coprimeEvalVector R Q.a hR hQa).2 ≠ 0 := by
    by_contra! hboth
    rcases hboth with ⟨hx, hy⟩
    rw [hx, hy] at hxy_gcd
    simp at hxy_gcd
  exact eval_pos_of_isPositiveDefinite R hRpos hxy_nonzero

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
  have : Q.b - (Q.b + 2 * Q.a * (((R.b - Q.b) / 2) * Int.gcdA Q.a R.a)) =
      -((2 * Q.a) * (((R.b - Q.b) / 2) * Int.gcdA Q.a R.a)) := by ring
  rw [this, dvd_neg]
  exact dvd_mul_right _ _

/-- `composeMiddleB` satisfies `B ≡ R.b (mod 2·R.a)` when `Q.a` and `R.a`
are coprime and the middle coefficients have the same parity (which follows
from equal discriminant).  The proof uses the Bézout identity
`gcdA·Q.a + gcdB·R.a = 1`. -/
theorem composeMiddleB_modEq_right (Q R : BinaryQuadraticForm)
    (hcop : Int.gcd Q.a R.a = 1) (hpar : 2 ∣ R.b - Q.b) :
    composeMiddleB Q R ≡ R.b [ZMOD 2 * R.a] := by
  rw [composeMiddleB, Int.modEq_iff_dvd]
  -- Goal: 2*R.a ∣ R.b - (Q.b + 2*Q.a*x)
  -- where x = d*gcdA, d = (R.b-Q.b)/2
  obtain ⟨d, hd⟩ := hpar
  have hd_exact : (R.b - Q.b) / 2 = d := by
    rw [hd, Int.mul_ediv_cancel_left d (by norm_num : (2 : ℤ) ≠ 0)]
  have hbezout : Q.a * Int.gcdA Q.a R.a + R.a * Int.gcdB Q.a R.a = 1 := by
    rw [← Int.gcd_eq_gcd_ab Q.a R.a, hcop]; simp
  rw [hd_exact]
  -- Goal: 2*R.a ∣ R.b - (Q.b + 2*Q.a*(d*gcdA))
  -- = -(Q.b + 2*Q.a*d*gcdA - R.b)
  -- = -(2d*(Q.a*gcdA - 1))  [since R.b = Q.b + 2d]
  -- = -2d*(-R.a*gcdB)  [by Bézout]
  -- = 2*R.a*(d*gcdB)
  have h_expr : R.b - (Q.b + 2 * Q.a * (d * Int.gcdA Q.a R.a)) =
      (2 * R.a) * (d * Int.gcdB Q.a R.a) := by
    have hb_eq : R.b = Q.b + 2 * d := by linarith
    rw [hb_eq]
    calc
      (Q.b + 2 * d) - (Q.b + 2 * Q.a * (d * Int.gcdA Q.a R.a))
          = 2 * d * (1 - Q.a * Int.gcdA Q.a R.a) := by ring
      _ = 2 * d * (R.a * Int.gcdB Q.a R.a) := by
        rw [show 1 - Q.a * Int.gcdA Q.a R.a = R.a * Int.gcdB Q.a R.a by linarith]
      _ = (2 * R.a) * (d * Int.gcdB Q.a R.a) := by ring
  rw [h_expr]
  exact dvd_mul_right _ _

/-- Computable Dirichlet composition.  The right factor is first replaced by a
properly equivalent representative whose leading coefficient is coprime to
`Q.a`; then the middle coefficient is chosen via the CRT to make the final
`c`-division exact. -/
def composeForm (Q R : BinaryQuadraticForm)
    (_hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) :
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

/-- **Discriminant preservation for computable composition.**
The result form has the same discriminant as `Q` (and thus `R`).  The
proof uses the CRT-adjusted `B`: since `B ≡ Q.b (mod 2·Q.a)` and
`B ≡ R'.b (mod 2·R'.a)` with `gcd(Q.a, R'.a) = 1`, the value
`B² - Q.disc` is divisible by `4·Q.a·R'.a`, making the `c`-division exact. -/
theorem disc_composeForm (Q R : BinaryQuadraticForm)
    (hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0)
    (_hQpos : Q.IsPositiveDefinite) (hRpos : R.IsPositiveDefinite) :
    (composeForm Q R hQR hR hQa).disc = Q.disc := by
  let R' := unitedRep Q R hR hQa
  let B := composeMiddleB Q R'
  have hcop : Int.gcd Q.a R'.a = 1 := gcd_left_a_unitedRep Q R hR hQa
  -- R'.disc = R.disc (proper equivalence preserves discriminant), and Q.disc = R.disc
  have hdisc_eq : Q.disc = R'.disc :=
    hQR.trans (disc_eq_of_properEquivalent (unitedRep_properEquivalent Q R hR hQa))
  -- Parity: same discriminant ⇒ middle coefficients have same parity
  -- even_sub_b_of_same_discriminant gives Even (R'.b - Q.b), i.e. ∃k, diff = k+k = 2*k
  have hpar : 2 ∣ R'.b - Q.b := by
    rcases even_sub_b_of_same_discriminant hdisc_eq with ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩
  -- CRT congruences
  have h_mod_left : B ≡ Q.b [ZMOD 2 * Q.a] := composeMiddleB_modEq_left Q R'
  have h_mod_right : B ≡ R'.b [ZMOD 2 * R'.a] :=
    composeMiddleB_modEq_right Q R' hcop hpar
  -- Step 1: 4·Q.a ∣ B² - Q.disc
  -- Int.modEq_iff_dvd: B ≡ Q.b [ZMOD 2·Q.a] ↔ 2·Q.a ∣ Q.b - B
  -- So Q.b - B = 2·Q.a·k, hence B = Q.b - 2·Q.a·k = Q.b + 2·Q.a·(-k)
  have h_dvd_left : (4 * Q.a) ∣ B ^ 2 - Q.disc := by
    have hk_div := (Int.modEq_iff_dvd.mp h_mod_left)
    rcases hk_div with ⟨k, hk⟩
    -- hk: 2*Q.a * k = Q.b - B, so B = Q.b - 2*Q.a*k
    have hB : B = Q.b - 2 * Q.a * k := by linarith
    rw [hB]
    -- (Q.b - 2*Q.a*k)² - Q.disc = (Q.b - 2*Q.a*k)² - (Q.b² - 4*Q.a*Q.c)
    -- = 4*Q.a*(Q.a*k² - Q.b*k + Q.c)
    use Q.a * k ^ 2 - Q.b * k + Q.c
    calc
      (Q.b - 2 * Q.a * k) ^ 2 - Q.disc
          = (Q.b - 2 * Q.a * k) ^ 2 - (Q.b ^ 2 - 4 * Q.a * Q.c) := rfl
      _ = 4 * Q.a * (Q.a * k ^ 2 - Q.b * k + Q.c) := by ring
  -- Step 2: 4·R'.a ∣ B² - Q.disc
  have h_dvd_right : (4 * R'.a) ∣ B ^ 2 - Q.disc := by
    have hk_div := (Int.modEq_iff_dvd.mp h_mod_right)
    rcases hk_div with ⟨k, hk⟩
    have hB : B = R'.b - 2 * R'.a * k := by linarith
    rw [hB, hdisc_eq]
    use R'.a * k ^ 2 - R'.b * k + R'.c
    calc
      (R'.b - 2 * R'.a * k) ^ 2 - R'.disc
          = (R'.b - 2 * R'.a * k) ^ 2 - (R'.b ^ 2 - 4 * R'.a * R'.c) := rfl
      _ = 4 * R'.a * (R'.a * k ^ 2 - R'.b * k + R'.c) := by ring
  -- Step 3: coprime cancellation → 4·Q.a·R'.a ∣ B² - Q.disc
  have h_dvd_prod : (4 * Q.a * R'.a) ∣ B ^ 2 - Q.disc := by
    rcases h_dvd_left with ⟨A, hA⟩
    rcases h_dvd_right with ⟨C, hC⟩
    -- 4*Q.a*A = B²-Q.disc = 4*R'.a*C ⇒ Q.a*A = R'.a*C ⇒ R'.a ∣ Q.a*A
    have h_eq : Q.a * A = R'.a * C := by nlinarith
    have h_ra_div_qaA : R'.a ∣ Q.a * A := by rw [h_eq]; exact dvd_mul_right _ _
    -- With gcd = 1, cancel: R'.a ∣ A
    have h_ra_div_A : R'.a ∣ A :=
      Int.dvd_of_dvd_mul_right_of_gcd_one h_ra_div_qaA (by rwa [Int.gcd_comm])
    rcases h_ra_div_A with ⟨D, hD⟩
    use D
    calc
      B ^ 2 - Q.disc = 4 * Q.a * A := hA
      _ = 4 * Q.a * (R'.a * D) := by rw [hD]
      _ = (4 * Q.a * R'.a) * D := by ring
  -- Step 4: exact division ⇒ disc = Q.disc
  rcases h_dvd_prod with ⟨C, hC⟩
  have hR'a_pos : 0 < R'.a := by
    simpa [R'] using unitedRep_a_pos Q R hR hQa hRpos
  have hR'a_ne_zero : R'.a ≠ 0 := ne_of_gt hR'a_pos
  have h_den_nonzero' : (4 * Q.a * R'.a) ≠ 0 := by
    intro hzero
    have h_or : (4 : ℤ) = 0 ∨ Q.a * R'.a = 0 :=
      eq_zero_or_eq_zero_of_mul_eq_zero (by simpa [mul_assoc] using hzero)
    rcases h_or with (h4 | hprod)
    · norm_num at h4
    · rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with (hqa | hra)
      · exact hQa hqa
      · exact hR'a_ne_zero hra
  -- Final step: compute the discriminant via the coefficient lemmas.
  -- disc = b² - 4*a*c = B² - 4*(Q.a*R'.a)*((B²-Q.disc)/(4*(Q.a*R'.a))) = ... = Q.disc
  have h_exact_div : (B ^ 2 - Q.disc) / (4 * (Q.a * R'.a)) = C := by
    have h_denom_eq : 4 * (Q.a * R'.a) = (4 * Q.a * R'.a) := by ring
    rw [h_denom_eq, hC]
    exact Int.mul_ediv_cancel_left C h_den_nonzero'
  calc
    (composeForm Q R hQR hR hQa).disc
        = (composeForm Q R hQR hR hQa).b ^ 2 -
          4 * (composeForm Q R hQR hR hQa).a *
              (composeForm Q R hQR hR hQa).c := rfl
    _ = B ^ 2 - 4 * (Q.a * R'.a) * ((B ^ 2 - Q.disc) / (4 * (Q.a * R'.a))) := by
      simp [composeForm_a, composeForm_b, composeForm_c, R', B]
    _ = B ^ 2 - 4 * (Q.a * R'.a) * C := by rw [h_exact_div]
    _ = B ^ 2 - ((4 * Q.a * R'.a) * C) := by ring
    _ = B ^ 2 - (B ^ 2 - Q.disc) := by rw [← hC]
    _ = Q.disc := by ring

/-- The exact division identity for the `c` coefficient of `composeForm`:
`(4 * Q.a * R'.a) * c = B² - Q.disc`. -/
theorem composeForm_exact_div (Q R : BinaryQuadraticForm)
    (hQR : Q.disc = R.disc) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0)
    (_hQpos : Q.IsPositiveDefinite) (hRpos : R.IsPositiveDefinite) :
    (4 * Q.a * (unitedRep Q R hR hQa).a) * (composeForm Q R hQR hR hQa).c =
      (composeMiddleB Q (unitedRep Q R hR hQa)) ^ 2 - Q.disc := by
  let R' := unitedRep Q R hR hQa
  let B := composeMiddleB Q R'
  have hcop : Int.gcd Q.a R'.a = 1 := gcd_left_a_unitedRep Q R hR hQa
  have hdisc_eq : Q.disc = R'.disc :=
    hQR.trans (disc_eq_of_properEquivalent (unitedRep_properEquivalent Q R hR hQa))
  have hpar : 2 ∣ R'.b - Q.b := by
    rcases even_sub_b_of_same_discriminant hdisc_eq with ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩
  have h_mod_left : B ≡ Q.b [ZMOD 2 * Q.a] := composeMiddleB_modEq_left Q R'
  have h_mod_right : B ≡ R'.b [ZMOD 2 * R'.a] :=
    composeMiddleB_modEq_right Q R' hcop hpar
  -- Step 1: 4·Q.a ∣ B² - Q.disc
  have h_dvd_left : (4 * Q.a) ∣ B ^ 2 - Q.disc := by
    have hk_div := (Int.modEq_iff_dvd.mp h_mod_left)
    rcases hk_div with ⟨k, hk⟩
    have hB : B = Q.b - 2 * Q.a * k := by linarith
    rw [hB]
    use Q.a * k ^ 2 - Q.b * k + Q.c
    calc
      (Q.b - 2 * Q.a * k) ^ 2 - Q.disc
          = (Q.b - 2 * Q.a * k) ^ 2 - (Q.b ^ 2 - 4 * Q.a * Q.c) := rfl
      _ = 4 * Q.a * (Q.a * k ^ 2 - Q.b * k + Q.c) := by ring
  -- Step 2: 4·R'.a ∣ B² - Q.disc
  have h_dvd_right : (4 * R'.a) ∣ B ^ 2 - Q.disc := by
    have hk_div := (Int.modEq_iff_dvd.mp h_mod_right)
    rcases hk_div with ⟨k, hk⟩
    have hB : B = R'.b - 2 * R'.a * k := by linarith
    rw [hB, hdisc_eq]
    use R'.a * k ^ 2 - R'.b * k + R'.c
    calc
      (R'.b - 2 * R'.a * k) ^ 2 - R'.disc
          = (R'.b - 2 * R'.a * k) ^ 2 - (R'.b ^ 2 - 4 * R'.a * R'.c) := rfl
      _ = 4 * R'.a * (R'.a * k ^ 2 - R'.b * k + R'.c) := by ring
  -- Step 3: coprime cancellation → 4·Q.a·R'.a ∣ B² - Q.disc
  have h_dvd_prod : (4 * Q.a * R'.a) ∣ B ^ 2 - Q.disc := by
    rcases h_dvd_left with ⟨A, hA⟩
    rcases h_dvd_right with ⟨C, hC⟩
    have h_eq : Q.a * A = R'.a * C := by nlinarith
    have h_ra_div_qaA : R'.a ∣ Q.a * A := by rw [h_eq]; exact dvd_mul_right _ _
    have h_ra_div_A : R'.a ∣ A :=
      Int.dvd_of_dvd_mul_right_of_gcd_one h_ra_div_qaA (by rwa [Int.gcd_comm])
    rcases h_ra_div_A with ⟨D, hD⟩
    use D
    calc
      B ^ 2 - Q.disc = 4 * Q.a * A := hA
      _ = 4 * Q.a * (R'.a * D) := by rw [hD]
      _ = (4 * Q.a * R'.a) * D := by ring
  -- Rewrite h_dvd_prod to the exact form we need
  rcases h_dvd_prod with ⟨C, hC⟩
  have h_den_nonzero' : (4 * Q.a * R'.a) ≠ 0 := by
    intro hzero
    have h_or : (4 : ℤ) = 0 ∨ Q.a * R'.a = 0 :=
      eq_zero_or_eq_zero_of_mul_eq_zero (by simpa [mul_assoc] using hzero)
    rcases h_or with (h4 | hprod)
    · norm_num at h4
    · rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with (hqa | hra)
      · exact hQa hqa
      · have hR'a_pos : 0 < R'.a := by
          simpa [R'] using unitedRep_a_pos Q R hR hQa hRpos
        exact ne_of_gt hR'a_pos hra
  have h_denom_eq' : 4 * (Q.a * R'.a) = (4 * Q.a * R'.a) := by ring
  calc
    (4 * Q.a * R'.a) * (composeForm Q R hQR hR hQa).c
        = (4 * Q.a * R'.a) * ((B ^ 2 - Q.disc) / (4 * (Q.a * R'.a))) := rfl
    _ = (4 * Q.a * R'.a) * C := by
      rw [h_denom_eq', hC, Int.mul_ediv_cancel_left C h_den_nonzero']
    _ = B ^ 2 - Q.disc := by rw [hC]

/-- **Primitivity preservation for computable composition.**
Both input forms must be primitive; the composed form is primitive too. -/
theorem isPrimitive_composeForm (Q R : BinaryQuadraticForm)
    (hQR : Q.disc = R.disc) (hQprim : Q.IsPrimitive) (hRprim : R.IsPrimitive)
    (hQa : Q.a ≠ 0) (hQpos : Q.IsPositiveDefinite) (hRpos : R.IsPositiveDefinite) :
    (composeForm Q R hQR hRprim hQa).IsPrimitive := by
  let R' := unitedRep Q R hRprim hQa
  let B := composeMiddleB Q R'
  have hcop : Int.gcd Q.a R'.a = 1 := gcd_left_a_unitedRep Q R hRprim hQa
  have hdisc_eq : Q.disc = R'.disc :=
    hQR.trans (disc_eq_of_properEquivalent (unitedRep_properEquivalent Q R hRprim hQa))
  have hpar : 2 ∣ R'.b - Q.b := by
    rcases even_sub_b_of_same_discriminant hdisc_eq with ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩
  have h_mod_left : B ≡ Q.b [ZMOD 2 * Q.a] := composeMiddleB_modEq_left Q R'
  have h_mod_right : B ≡ R'.b [ZMOD 2 * R'.a] :=
    composeMiddleB_modEq_right Q R' hcop hpar
  -- R' is primitive (primitivity preserved under SL₂)
  have hR'prim : R'.IsPrimitive :=
    isPrimitive_transform R hRprim (sl2z_of_coprime
      (coprimeEvalVector R Q.a hRprim hQa).1
      (coprimeEvalVector R Q.a hRprim hQa).2
      (coprimeEvalVector_gcd R Q.a hRprim hQa))
  -- Exact division identity: (4·Q.a·R'.a) · c = B² - Q.disc
  have h_exact_div : (4 * Q.a * R'.a) * (composeForm Q R hQR hRprim hQa).c = B ^ 2 - Q.disc :=
    composeForm_exact_div Q R hQR hRprim hQa hQpos hRpos
  -- Now the primitivity argument proper
  unfold IsPrimitive
  let S := composeForm Q R hQR hRprim hQa
  let n : ℕ := Int.gcd S.a (Int.gcd S.b S.c)
  change n = 1
  by_contra hn
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn
  have hpz_dvd_n : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
  have hn_a : (n : ℤ) ∣ S.a := Int.gcd_dvd_left _ _
  have hn_bc : (n : ℤ) ∣ Int.gcd S.b S.c := Int.gcd_dvd_right _ _
  have hn_b : (n : ℤ) ∣ S.b := dvd_trans hn_bc (Int.gcd_dvd_left _ _)
  have hn_c : (n : ℤ) ∣ S.c := dvd_trans hn_bc (Int.gcd_dvd_right _ _)
  have hpS_a : (p : ℤ) ∣ S.a := dvd_trans hpz_dvd_n hn_a
  have hpS_b : (p : ℤ) ∣ S.b := dvd_trans hpz_dvd_n hn_b
  have hpS_c : (p : ℤ) ∣ S.c := dvd_trans hpz_dvd_n hn_c
  -- Unfold S coefficients
  have haS : S.a = Q.a * R'.a := by dsimp [S, composeForm, R', B]
  have hbS : S.b = B := by dsimp [S, composeForm, R', B]
  rw [haS] at hpS_a
  rw [hbS] at hpS_b
  -- p ∣ Q.a * R'.a, gcd(Q.a, R'.a) = 1 ⇒ p divides exactly one
  have hpQaRa_nat : p ∣ (Q.a * R'.a).natAbs := (Int.natCast_dvd).mp hpS_a
  rw [Int.natAbs_mul] at hpQaRa_nat
  rcases (Nat.Prime.dvd_mul hp).mp hpQaRa_nat with hpQa_nat | hpRa_nat
  · -- Case 1: p ∣ Q.a
    have hpQa : (p : ℤ) ∣ Q.a := (Int.natCast_dvd).mpr hpQa_nat
    -- p ∣ Q.a ⇒ from B ≡ Q.b (mod 2·Q.a) we get p ∣ Q.b
    have hpQb_sub_B : (p : ℤ) ∣ Q.b - B := by
      rcases (Int.modEq_iff_dvd.mp h_mod_left) with ⟨k, hk⟩
      rw [hk]
      have hp2Qa : (p : ℤ) ∣ 2 * Q.a := dvd_mul_of_dvd_right hpQa 2
      exact dvd_mul_of_dvd_left hp2Qa k
    have hpQb : (p : ℤ) ∣ Q.b := by
      have : Q.b = (Q.b - B) + B := by ring
      rw [this]; exact dvd_add hpQb_sub_B hpS_b
    -- From the exact division identity derive p ∣ Q.c
    rcases (Int.modEq_iff_dvd.mp h_mod_left) with ⟨k₁, hk₁⟩
    have hB_eq : B = Q.b - 2 * Q.a * k₁ := by linarith
    rw [hB_eq] at h_exact_div
    have h_factor : (Q.b - 2 * Q.a * k₁) ^ 2 - (Q.b ^ 2 - 4 * Q.a * Q.c) =
        4 * Q.a * (Q.c - k₁ * Q.b + Q.a * k₁ ^ 2) := by ring
    rw [show Q.disc = Q.b ^ 2 - 4 * Q.a * Q.c from rfl] at h_exact_div
    rw [h_factor] at h_exact_div
    have h_cancel : R'.a * S.c = Q.c - k₁ * Q.b + Q.a * k₁ ^ 2 := by
      have h4Qa_ne : 4 * Q.a ≠ 0 := mul_ne_zero (by norm_num) hQa
      apply mul_left_cancel₀ h4Qa_ne
      calc
        4 * Q.a * (R'.a * S.c) = (4 * Q.a * R'.a) * S.c := by ring
        _ = 4 * Q.a * (Q.c - k₁ * Q.b + Q.a * k₁ ^ 2) := h_exact_div
        _ = 4 * Q.a * (Q.c - k₁ * Q.b + Q.a * k₁ ^ 2) := rfl
    have hpQc : (p : ℤ) ∣ Q.c := by
      have hQc_expr : Q.c = R'.a * S.c + k₁ * Q.b - Q.a * k₁ ^ 2 := by linarith
      rw [hQc_expr]
      apply dvd_sub
      · apply dvd_add
        · exact dvd_mul_of_dvd_right hpS_c _
        · exact dvd_mul_of_dvd_right hpQb k₁
      · exact dvd_mul_of_dvd_left hpQa (k₁ ^ 2)
    exact not_prime_dvd_coefficients_of_isPrimitive hQprim hp hpQa hpQb hpQc
  · -- Case 2: p ∣ R'.a
    have hpR'a : (p : ℤ) ∣ R'.a := (Int.natCast_dvd).mpr hpRa_nat
    -- p ∣ R'.a ⇒ from B ≡ R'.b (mod 2·R'.a) we get p ∣ R'.b
    have hpR'b_sub_B : (p : ℤ) ∣ R'.b - B := by
      rcases (Int.modEq_iff_dvd.mp h_mod_right) with ⟨k, hk⟩
      rw [hk]
      have hp2R'a : (p : ℤ) ∣ 2 * R'.a := dvd_mul_of_dvd_right hpR'a 2
      exact dvd_mul_of_dvd_left hp2R'a k
    have hpR'b : (p : ℤ) ∣ R'.b := by
      have : R'.b = (R'.b - B) + B := by ring
      rw [this]; exact dvd_add hpR'b_sub_B hpS_b
    -- From the exact division identity derive p ∣ R'.c
    rcases (Int.modEq_iff_dvd.mp h_mod_right) with ⟨k₂, hk₂⟩
    have hB_eq : B = R'.b - 2 * R'.a * k₂ := by linarith
    rw [hB_eq] at h_exact_div
    -- Use Q.disc = R'.disc to express in terms of R'
    have hdiscR' : R'.disc = R'.b ^ 2 - 4 * R'.a * R'.c := rfl
    rw [hdisc_eq, hdiscR'] at h_exact_div
    have h_factor : (R'.b - 2 * R'.a * k₂) ^ 2 - (R'.b ^ 2 - 4 * R'.a * R'.c) =
        4 * R'.a * (R'.c - k₂ * R'.b + R'.a * k₂ ^ 2) := by ring
    rw [h_factor] at h_exact_div
    have h_cancel : Q.a * S.c = R'.c - k₂ * R'.b + R'.a * k₂ ^ 2 := by
      have hR'a_ne : R'.a ≠ 0 :=
        ne_of_gt (by simpa [R'] using unitedRep_a_pos Q R hRprim hQa hRpos)
      have h4R'a_ne : 4 * R'.a ≠ 0 := mul_ne_zero (by norm_num) hR'a_ne
      apply mul_left_cancel₀ h4R'a_ne
      calc
        4 * R'.a * (Q.a * S.c) = (4 * Q.a * R'.a) * S.c := by ring
        _ = 4 * R'.a * (R'.c - k₂ * R'.b + R'.a * k₂ ^ 2) := h_exact_div
        _ = 4 * R'.a * (R'.c - k₂ * R'.b + R'.a * k₂ ^ 2) := rfl
    have hpR'c : (p : ℤ) ∣ R'.c := by
      have hR'c_expr : R'.c = Q.a * S.c + k₂ * R'.b - R'.a * k₂ ^ 2 := by linarith
      rw [hR'c_expr]
      apply dvd_sub
      · apply dvd_add
        · exact dvd_mul_of_dvd_right hpS_c _
        · exact dvd_mul_of_dvd_right hpR'b k₂
      · exact dvd_mul_of_dvd_left hpR'a (k₂ ^ 2)
    exact not_prime_dvd_coefficients_of_isPrimitive hR'prim hp hpR'a hpR'b hpR'c

/-! ## Regression: computable composition on `d = -21` spike forms

The spike (Design Doc §2) confirms that `fieldDiscriminant (-21 : ℚ) = -84` and
the primitive reduced forms are `[(1,0,21), (2,2,11), (3,0,7), (5,4,5)]`.
These `#eval` tests verify that `composeForm` runs to a concrete integer triple
without errors.

The CRT-adjusted middle coefficient guarantees exact division, so the
output discriminant equals `Q.disc` unconditionally.  The `example` blocks
double-check the full form triple and its discriminant. -/

set_option linter.hashCommand false

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

-- The output triple matches the CRT algorithm's expected values.
#guard testComposeFormIdentity.a == 11
#guard testComposeFormIdentity.b == -2
#guard testComposeFormIdentity.c == 2
-- Discriminant preserved.
#guard testComposeFormIdentity.disc == -84

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

#guard testComposeFormPrincipal2.a == 5
#guard testComposeFormPrincipal2.b == -4
#guard testComposeFormPrincipal2.c == 5
#guard testComposeFormPrincipal2.disc == -84

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

#guard testComposeFormOrder2.a == 21
#guard testComposeFormOrder2.b == 0
#guard testComposeFormOrder2.c == 1
#guard testComposeFormOrder2.disc == -84

/-- Verify that all four reduced forms of discriminant `-84` have equal
discriminant (a precondition for composition). -/
example : (BinaryQuadraticForm.mk 1 0 21).disc = -84 := by
  norm_num [disc]
example : (BinaryQuadraticForm.mk 2 2 11).disc = -84 := by
  norm_num [disc]
example : (BinaryQuadraticForm.mk 3 0 7).disc = -84 := by
  norm_num [disc]
example : (BinaryQuadraticForm.mk 5 4 5).disc = -84 := by
  norm_num [disc]

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
