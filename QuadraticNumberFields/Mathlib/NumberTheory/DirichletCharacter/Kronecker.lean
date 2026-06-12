/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import QuadraticNumberFields.Mathlib.NumberTheory.LegendreSymbol.KroneckerSymbol
import QuadraticNumberFields.Mathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity

/-!
# Kronecker Symbol as a Dirichlet Character

Material destined for mathlib.

This file packages the Kronecker symbol `(D / ·)` as a `DirichletCharacter ℤ D.natAbs`,
for every integer `D` whose remainder modulo `4` is `0` or `1`. The signature is

```
noncomputable def kroneckerCharacter (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] :
    DirichletCharacter ℤ D.natAbs
```

`D = 0` is allowed by the `Fact` (since `0 % 4 = 0`) and reduces to the trivial
Dirichlet character on `ZMod 0 = ℤ` (only `±1` are units; both map to `1`).

## Main definitions

* `kroneckerCharacterFun`: the underlying value map `ZMod D.natAbs → ℤ`,
  `x ↦ kroneckerSymNat D x.val`.
* `kroneckerCharacter`: the `DirichletCharacter` packaging.

## Main results

* `kroneckerCharacter_apply_natCast`: at a natural argument, the character value is
  `kroneckerSymNat D n`.
* `kroneckerCharacter_apply_intCast`: at an integer argument, the character value is
  `kroneckerSym D n`.
-/

namespace QuadraticNumberFields

/-- The value map of the Kronecker Dirichlet character: `x ↦ kroneckerSymNat D x.val`. -/
def kroneckerCharacterFun (D : ℤ) (x : ZMod D.natAbs) : ℤ :=
  kroneckerSymNat D x.val

/-- `kroneckerSymNat D 1 = 1` for every `D : ℤ`. -/
private lemma kroneckerCharacterFun_one (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] :
    kroneckerCharacterFun D 1 = 1 := by
  unfold kroneckerCharacterFun
  rcases eq_or_ne D.natAbs 0 with hD0 | hD0
  · -- D.natAbs = 0 (D = 0): (1 : ZMod 0).val = 1, kroneckerSymNat 0 1 = 1
    rw [show (1 : ZMod D.natAbs).val = 1 from by rw [ZMod.val_one_eq_one_mod, hD0]]
    rw [kroneckerSymNat]
    simp [kroneckerTwo, jacobiSym.one_right]
  · rcases eq_or_ne D.natAbs 1 with hD1 | hD1
    · -- D.natAbs = 1: ZMod 1 has only one element; (1 : ZMod 1).val = 0.
      rw [show (1 : ZMod D.natAbs).val = 0 from by rw [ZMod.val_one_eq_one_mod, hD1]]
      rw [kroneckerSymNat]
      simp [hD1]
    · -- D.natAbs ≥ 2: (1 : ZMod D.natAbs).val = 1
      have hgt : 1 < D.natAbs := lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hD0) (Ne.symm hD1)
      have : Fact (1 < D.natAbs) := ⟨hgt⟩
      rw [ZMod.val_one]
      rw [kroneckerSymNat]
      simp [kroneckerTwo, jacobiSym.one_right]

/-- Multiplicativity of `kroneckerCharacterFun` on `ZMod D.natAbs`, conditional on
`D % 4 ∈ {0, 1}` (the hypothesis is used through `kroneckerSymNat_add_natAbs_eq`). -/
private lemma kroneckerCharacterFun_mul (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (x y : ZMod D.natAbs) :
    kroneckerCharacterFun D (x * y) =
      kroneckerCharacterFun D x * kroneckerCharacterFun D y := by
  unfold kroneckerCharacterFun
  sorry

/-- Nonunits of `ZMod D.natAbs` share a factor with `D.natAbs`, so the Kronecker
value is `0`. -/
private lemma kroneckerCharacterFun_nonunit (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    {x : ZMod D.natAbs} (hx : ¬ IsUnit x) : kroneckerCharacterFun D x = 0 := by
  unfold kroneckerCharacterFun
  rcases eq_or_ne D.natAbs 0 with hD0 | hD0
  · -- D = 0: ZMod 0 = ℤ; nonunit ⇔ x.natAbs ≠ 1 ⇔ x.val ≠ 1 (val = Int.natAbs on ZMod 0).
    -- Then `gcd x.val 0 = x.val ≠ 1`, so Shim C closes the goal.
    -- TODO(focused-followup): unify with the D.natAbs > 0 branch through a single
    -- IsUnit-vs-coprime bridge that covers both `NeZero` and `ZMod 0 = ℤ`.
    sorry
  · have : NeZero D.natAbs := ⟨hD0⟩
    have hcop : ¬ Nat.Coprime x.val D.natAbs := by
      rw [Nat.Coprime]
      intro hco
      apply hx
      rw [← ZMod.natCast_zmod_val x]
      exact (ZMod.isUnit_iff_coprime _ _).mpr hco
    exact kroneckerSymNat_eq_zero_of_not_coprime D hcop

/-- The Kronecker symbol `(D / ·)` as a `DirichletCharacter ℤ D.natAbs`, for every
`D : ℤ` with `D % 4 ∈ {0, 1}`. The construction packages `kroneckerSymNat D` via
the value map on `ZMod D.natAbs`. -/
noncomputable def kroneckerCharacter (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] :
    DirichletCharacter ℤ D.natAbs where
  toFun := kroneckerCharacterFun D
  map_one' := kroneckerCharacterFun_one D
  map_mul' := kroneckerCharacterFun_mul D
  map_nonunit' := fun _ hx => kroneckerCharacterFun_nonunit D hx

/-- Evaluation of the Kronecker character at a natural representative reproduces
`kroneckerSymNat D n`. -/
@[simp] theorem kroneckerCharacter_apply_natCast (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (n : ℕ) :
    kroneckerCharacter D ((n : ℕ) : ZMod D.natAbs) = kroneckerSymNat D n := by
  sorry

/-- Evaluation of the Kronecker character at an integer representative reproduces
`kroneckerSym D n`. -/
@[simp] theorem kroneckerCharacter_apply_intCast (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (n : ℤ) :
    kroneckerCharacter D ((n : ℤ) : ZMod D.natAbs) = kroneckerSym D n := by
  sorry

end QuadraticNumberFields
