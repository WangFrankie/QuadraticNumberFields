/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassNumber.Criteria
import QuadraticNumberFields.RingOfIntegers.CommonInstances
import QuadraticNumberFields.Splitting.Qsqrtd.Classification
import Lean.Elab.Tactic

/-!
# Class Number One for the Nine Heegner Numbers

This file proves that the nine imaginary quadratic fields `ℚ(√d)` with
`d ∈ {-1, -2, -3, -7, -11, -19, -43, -67, -163}` (the **Heegner numbers**)
all have class number one. This is the elementary direction of the
Baker–Heegner–Stark theorem (see `QuadraticNumberFields.Heegner.StarkHeegner`
for the full statement).

## Proof strategy

For each Heegner number the Minkowski bound `(2/π)·√|D|` is estimated by
`Qsqrtd.minkowskiBound_lt_of_neg` (using only `π > 3`), and every rational
prime below the bound is checked to be **inert** via the splitting
classification: `d ≡ 5 (mod 8)` for `p = 2`, and `legendreSym p d = -1` for
odd `p`. The criterion
`Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn` then yields
triviality of the class group.

The largest case `d = -163` has Minkowski bound `≈ 8.13 < 9`, so the primes
`2, 3, 5, 7` must all be inert — the classical computation.

## Main results

* `classNumber_eq_one_neg1` … `classNumber_eq_one_neg163`: the nine cases.
* `heegnerSet`: the nine Heegner numbers as a `Finset ℤ`.
* `classNumber_eq_one_of_mem_heegnerSet`: packaged forward direction.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

open Splitting
open Lean Elab Tactic

instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## A small tactic for the Heegner class-number-one computations -/

syntax (name := prove_class_number_one_qsqrtd_for)
  "prove_class_number_one_qsqrtd_for " term ", " term : tactic

macro_rules
  | `(tactic| prove_class_number_one_qsqrtd_for $d, $n) =>
      `(tactic|
        exact Qsqrtd.classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn ($d : ℤ)
          (by
            intro p hp hple
            have hb : Qsqrtd.minkowskiBound ($d : ℤ) < ($n : ℕ) := by
              first
                | exact Qsqrtd.minkowskiBound_lt_of_neg ($d : ℤ) (by norm_num)
                    (by
                      first
                        | rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]
                        | rw [RingOfIntegers.discr_of_mod_four_ne_one _ (by decide)]
                      norm_num)
                | exact Qsqrtd.minkowskiBound_lt_of_pos ($d : ℤ) (by norm_num)
                    (by
                      first
                        | rw [RingOfIntegers.discr_of_mod_four_eq_one _ (by decide)]
                        | rw [RingOfIntegers.discr_of_mod_four_ne_one _ (by decide)]
                      norm_num)
            have hplt : p < ($n : ℕ) := by exact_mod_cast hple.trans_lt hb
            interval_cases p
            all_goals
              first
                | exact absurd hp (by decide)
                | exact isInert_two_of_mod_eight_eq_five ($d : ℤ) (by decide)
                | exact (isInert_iff_legendreSym_eq_neg_one ($d : ℤ) 3 (by decide)
                    (by decide)).mpr (by decide)
                | exact (isInert_iff_legendreSym_eq_neg_one ($d : ℤ) 5 (by decide)
                    (by decide)).mpr (by decide)
                | exact (isInert_iff_legendreSym_eq_neg_one ($d : ℤ) 7 (by decide)
                    (by decide)).mpr (by decide)))

/--
Close a Heegner class-number-one goal by the common proof pattern:
use the inert-prime Minkowski criterion, prove the numeric bound, and check all
rational primes below that bound by the quadratic splitting criteria.
-/
private partial def findQsqrtdArg? : Expr → Option Expr
  | .app f a =>
      if f.isConstOf ``Qsqrtd then some a else findQsqrtdArg? f <|> findQsqrtdArg? a
  | .lam _ t b _ => findQsqrtdArg? t <|> findQsqrtdArg? b
  | .forallE _ t b _ => findQsqrtdArg? t <|> findQsqrtdArg? b
  | .letE _ t v b _ => findQsqrtdArg? t <|> findQsqrtdArg? v <|> findQsqrtdArg? b
  | .mdata _ b => findQsqrtdArg? b
  | .proj _ _ b => findQsqrtdArg? b
  | _ => none

private def classNumberFieldArg? (target : Expr) : Option Expr := do
  guard (Expr.isAppOfArity target ``Eq 3)
  let lhs := Expr.getArg! target 1
  findQsqrtdArg? lhs

private def intCastArg? (e : Expr) : Option Expr :=
  if Expr.isAppOfArity e ``Int.cast 3 then some (Expr.getArg! e 2) else none

private def ofNatExpr? (e : Expr) : Option Nat :=
  if Expr.isAppOfArity e ``OfNat.ofNat 3 then
    match Expr.getArg! e 1 with
    | .lit (.natVal n) => some n
    | _ => none
  else
    none

private partial def intExpr? (e : Expr) : Option Int :=
  if Expr.isAppOfArity e ``Neg.neg 3 then
    return -Int.ofNat (← ofNatExpr? (Expr.getArg! e 2))
  else
    return Int.ofNat (← ofNatExpr? e)

private def discrFormulaValue (d : Int) : Int :=
  if d % 4 = 1 then d else 4 * d

private def firstMinkowskiBoundCandidate? (d : Int) : Option Nat :=
  let D := discrFormulaValue d
  (List.range 9).map (· + 2) |>.find? fun n =>
    if d < 0 then
      4 * |D| < 9 * (Int.ofNat n) ^ 2
    else
      |D| < 4 * (Int.ofNat n) ^ 2

elab "prove_class_number_one_qsqrtd" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some qArg := classNumberFieldArg? target
    | throwError "prove_class_number_one_qsqrtd: target does not contain `Qsqrtd ((d : ℤ) : ℚ)`"
  let some d ← pure (intCastArg? qArg)
    | throwError
        "prove_class_number_one_qsqrtd: expected the `Qsqrtd` parameter to be cast from `ℤ`"
  let some dVal := intExpr? d
    | throwError "prove_class_number_one_qsqrtd: expected a concrete integer parameter"
  let some nVal := firstMinkowskiBoundCandidate? dVal
    | throwError
        "prove_class_number_one_qsqrtd: no Minkowski bound candidate found from 2 through 10"
  let dStx ← Term.exprToSyntax d
  let nStx : TSyntax `term := ⟨Syntax.mkNumLit (toString nVal)⟩
  evalTactic (← `(tactic| prove_class_number_one_qsqrtd_for $dStx, $nStx))

/-- `ℚ(√-1)` has class number one: the Minkowski bound is `4/π < 2`. -/
theorem classNumber_eq_one_neg1 :
    NumberField.classNumber (Qsqrtd ((-1 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-- `ℚ(√-2)` has class number one: the Minkowski bound is `(2/π)·√8 < 2`. -/
theorem classNumber_eq_one_neg2 :
    NumberField.classNumber (Qsqrtd ((-2 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-- `ℚ(√-3)` has class number one: the Minkowski bound is `(2/π)·√3 < 2`. -/
theorem classNumber_eq_one_neg3 :
    NumberField.classNumber (Qsqrtd ((-3 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-- `ℚ(√-7)` has class number one: the Minkowski bound is `(2/π)·√7 < 2`. -/
theorem classNumber_eq_one_neg7 :
    NumberField.classNumber (Qsqrtd ((-7 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-- `ℚ(√-11)` has class number one: the Minkowski bound is `(2/π)·√11 < 3`,
and `2` is inert since `-11 ≡ 5 (mod 8)`. -/
theorem classNumber_eq_one_neg11 :
    NumberField.classNumber (Qsqrtd ((-11 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-- `ℚ(√-19)` has class number one: the Minkowski bound is `(2/π)·√19 < 3`,
and `2` is inert since `-19 ≡ 5 (mod 8)`. -/
theorem classNumber_eq_one_neg19 :
    NumberField.classNumber (Qsqrtd ((-19 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-- `ℚ(√-43)` has class number one: the Minkowski bound is `(2/π)·√43 < 5`,
and `2, 3` are inert. -/
theorem classNumber_eq_one_neg43 :
    NumberField.classNumber (Qsqrtd ((-43 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-- `ℚ(√-67)` has class number one: the Minkowski bound is `(2/π)·√67 < 6`,
and `2, 3, 5` are inert. -/
theorem classNumber_eq_one_neg67 :
    NumberField.classNumber (Qsqrtd ((-67 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-- `ℚ(√-163)` has class number one: the Minkowski bound is `(2/π)·√163 < 9`,
and `2, 3, 5, 7` are all inert — the classical Heegner computation. -/
theorem classNumber_eq_one_neg163 :
    NumberField.classNumber (Qsqrtd ((-163 : ℤ) : ℚ)) = 1 := by
  prove_class_number_one_qsqrtd

/-! ## The Heegner numbers, packaged -/

/-- The nine **Heegner numbers**: the negative squarefree integers `d` for
which `ℚ(√d)` has class number one. -/
def heegnerSet : Finset ℤ := {-1, -2, -3, -7, -11, -19, -43, -67, -163}

/-- **Forward direction of the Baker–Heegner–Stark theorem**: every Heegner
number gives an imaginary quadratic field of class number one. -/
theorem classNumber_eq_one_of_mem_heegnerSet
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d ∈ heegnerSet) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  fin_cases hd
  all_goals prove_class_number_one_qsqrtd

end Heegner
end QuadraticNumberFields
