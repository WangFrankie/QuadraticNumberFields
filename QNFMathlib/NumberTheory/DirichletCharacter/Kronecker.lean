/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbol
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity

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

* `kroneckerCharacter`: the `DirichletCharacter` packaging.

## Main results

* `kroneckerCharacter_apply`: direct evaluation at a `ZMod D.natAbs` argument.
* `kroneckerCharacter_apply_natCast`: at a natural argument, the character value is
  `kroneckerSymNat D n`.
* `kroneckerCharacter_neg_one`: at `-1`, the character is the sign of `D`.
* `kroneckerCharacter_apply_intCast`: at an integer argument, the character value is
  `kroneckerSym D n`.
-/

private def kroneckerCharacterFun (D : ℤ) (x : ZMod D.natAbs) : ℤ :=
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
  rw [ZMod.val_mul, kroneckerSymNat_mod_natAbs_eq]
  by_cases hx0 : x.val = 0
  · rw [hx0, zero_mul]
    by_cases hD1 : D.natAbs = 1
    · haveI : NeZero D.natAbs := ⟨by omega⟩
      have hyval : y.val = 0 := by
        have hylt := ZMod.val_lt y
        omega
      rw [hyval]
      simp [kroneckerSymNat, hD1]
    · simp [kroneckerSymNat, hD1]
  by_cases hy0 : y.val = 0
  · rw [hy0, mul_zero]
    by_cases hD1 : D.natAbs = 1
    · haveI : NeZero D.natAbs := ⟨by omega⟩
      have hxval : x.val = 0 := by
        have hxlt := ZMod.val_lt x
        omega
      rw [hxval]
      simp [kroneckerSymNat, hD1]
    · simp [kroneckerSymNat, hD1]
  exact kroneckerSymNat_mul D hx0 hy0

/-- Nonunits of `ZMod D.natAbs` share a factor with `D.natAbs`, so the Kronecker
value is `0`. -/
private lemma kroneckerCharacterFun_nonunit (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    {x : ZMod D.natAbs} (hx : ¬ IsUnit x) : kroneckerCharacterFun D x = 0 := by
  unfold kroneckerCharacterFun
  rcases eq_or_ne D.natAbs 0 with hD0 | hD0
  · -- D = 0: ZMod 0 = ℤ; nonunit means `x.val ≠ 1`.
    -- Then `gcd x.val 0 = x.val ≠ 1`, so the vanishing lemma closes the goal.
    have hxval : x.val ≠ 1 := by
      intro hxval
      apply hx
      have hunit0 : IsUnit ((ZMod.ringEquivCongr hD0) x) := by
        apply (ZMod.val_unit').mpr
        rw [ZMod.ringEquivCongr_val, hxval]
      have hunit := hunit0.map (ZMod.ringEquivCongr hD0).symm.toRingHom
      simpa using hunit
    have hcop : Nat.gcd x.val D.natAbs ≠ 1 := by
      have hgcd : Nat.gcd x.val D.natAbs = x.val := by
        conv_lhs =>
          congr
          · rfl
          · rw [hD0]
        rw [Nat.gcd_zero_right]
      rwa [hgcd]
    exact kroneckerSymNat_eq_zero_of_not_coprime D hcop
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

/-- Direct evaluation of the Kronecker character at a `ZMod D.natAbs` argument. -/
@[simp] theorem kroneckerCharacter_apply (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (x : ZMod D.natAbs) :
    kroneckerCharacter D x = kroneckerSymNat D x.val := rfl

/-- Evaluation of the Kronecker character at a natural representative reproduces
`kroneckerSymNat D n`.

Not a `simp` lemma: `kroneckerCharacter_apply` already rewrites the left-hand
side, so this would never be in simp-normal form; it is used via `rw`. -/
theorem kroneckerCharacter_apply_natCast (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (n : ℕ) :
    kroneckerCharacter D ((n : ℕ) : ZMod D.natAbs) = kroneckerSymNat D n := by
  rw [kroneckerCharacter_apply, ZMod.val_natCast]
  exact kroneckerSymNat_mod_natAbs_eq D n

/-- The Kronecker character value at `-1` is the sign factor in the Kronecker
symbol convention.

Not a `simp` lemma: `kroneckerCharacter_apply` already rewrites the left-hand
side, so this would never be in simp-normal form; it is used via `rw`. -/
theorem kroneckerCharacter_neg_one (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] :
    kroneckerCharacter D (-1 : ZMod D.natAbs) = if D < 0 then -1 else 1 := by
  rcases eq_or_ne D.natAbs 0 with hD0 | hD0
  · have hD : D = 0 := by omega
    subst D
    change kroneckerCharacterFun 0 (-1 : ZMod 0) = 1
    simp [kroneckerCharacterFun, kroneckerSymNat]
  · have hval : (-1 : ZMod D.natAbs).val = D.natAbs - 1 := by
      cases hN : D.natAbs with
      | zero => exact False.elim (hD0 hN)
      | succ N =>
          simp
    rw [kroneckerCharacter_apply, hval]
    exact kroneckerSymNat_natAbs_sub_one_eq_sign D hD0

/-- Evaluation of the Kronecker character at an integer representative reproduces
`kroneckerSym D n`.

Not a `simp` lemma: `kroneckerCharacter_apply` already rewrites the left-hand
side, so this would never be in simp-normal form; it is used via `rw`. -/
theorem kroneckerCharacter_apply_intCast (D : ℤ) [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (n : ℤ) :
    kroneckerCharacter D ((n : ℤ) : ZMod D.natAbs) = kroneckerSym D n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · have hcast : (((m : ℤ) : ZMod D.natAbs) = ((m : ℕ) : ZMod D.natAbs)) := by
      norm_num
    rw [hcast, kroneckerCharacter_apply_natCast, kroneckerSym_natCast]
  · rcases eq_or_ne m 0 with rfl | hm0
    · norm_num [kroneckerSym, kroneckerSymNat]
    · have hcast : (((-(m : ℤ) : ℤ) : ZMod D.natAbs) =
          (-1 : ZMod D.natAbs) * ((m : ℕ) : ZMod D.natAbs)) := by
        norm_num [Int.cast_neg]
      rw [hcast, map_mul, kroneckerCharacter_neg_one D, kroneckerCharacter_apply_natCast]
      have hne : (-(m : ℤ) : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hm0)
      have hlt : (-(m : ℤ) : ℤ) < 0 := neg_neg_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm0)
      rw [kroneckerSym, if_neg hne, if_pos hlt, Int.natAbs_neg, Int.natAbs_natCast]

/-! ## Examples -/

section Examples

local instance : Fact ((-3 : ℤ) % 4 = 0 ∨ (-3 : ℤ) % 4 = 1) := ⟨by norm_num⟩
local instance : Fact ((-4 : ℤ) % 4 = 0 ∨ (-4 : ℤ) % 4 = 1) := ⟨by norm_num⟩
local instance : Fact ((-8 : ℤ) % 4 = 0 ∨ (-8 : ℤ) % 4 = 1) := ⟨by norm_num⟩
local instance : Fact ((5 : ℤ) % 4 = 0 ∨ (5 : ℤ) % 4 = 1) := ⟨by norm_num⟩
local instance : Fact ((8 : ℤ) % 4 = 0 ∨ (8 : ℤ) % 4 = 1) := ⟨by norm_num⟩
local instance : Fact ((12 : ℤ) % 4 = 0 ∨ (12 : ℤ) % 4 = 1) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example : kroneckerCharacter (-3 : ℤ) ((2 : ℤ) : ZMod ((-3 : ℤ).natAbs)) = -1 := by
  rw [kroneckerCharacter_apply_intCast]
  change kroneckerSym (-3 : ℤ) (2 : ℕ) = -1
  rw [kroneckerSym_natCast]
  simp [kroneckerSymNat_two, kroneckerTwo]

example : kroneckerCharacter (-4 : ℤ) ((3 : ℕ) : ZMod ((-4 : ℤ).natAbs)) = -1 := by
  rw [kroneckerCharacter_apply_natCast]
  rw [kroneckerSymNat_eq_legendreSym_of_ne_two]
  · rw [legendreSym.mod]
    change legendreSym 3 2 = -1
    rw [legendreSym.at_two] <;> norm_num
  · norm_num

example : kroneckerCharacter (-8 : ℤ) ((5 : ℕ) : ZMod ((-8 : ℤ).natAbs)) = -1 := by
  rw [kroneckerCharacter_apply_natCast]
  rw [kroneckerSymNat_eq_legendreSym_of_ne_two]
  · rw [legendreSym.mod]
    change legendreSym 5 2 = -1
    rw [legendreSym.at_two] <;> norm_num
  · norm_num

example : kroneckerCharacter (5 : ℤ) ((2 : ℤ) : ZMod ((5 : ℤ).natAbs)) = -1 := by
  rw [kroneckerCharacter_apply_intCast]
  change kroneckerSym (5 : ℤ) (2 : ℕ) = -1
  rw [kroneckerSym_natCast]
  simp [kroneckerSymNat_two, kroneckerTwo]

example : kroneckerCharacter (8 : ℤ) ((3 : ℕ) : ZMod ((8 : ℤ).natAbs)) = -1 := by
  rw [kroneckerCharacter_apply_natCast]
  rw [kroneckerSymNat_eq_legendreSym_of_ne_two]
  · rw [legendreSym.mod]
    change legendreSym 3 2 = -1
    rw [legendreSym.at_two] <;> norm_num
  · norm_num

example : kroneckerCharacter (12 : ℤ) ((5 : ℕ) : ZMod ((12 : ℤ).natAbs)) = -1 := by
  rw [kroneckerCharacter_apply_natCast]
  rw [kroneckerSymNat_eq_legendreSym_of_ne_two]
  · rw [legendreSym.mod]
    change legendreSym 5 2 = -1
    rw [legendreSym.at_two] <;> norm_num
  · norm_num

end Examples
