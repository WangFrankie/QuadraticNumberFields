/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.DirichletCharacter.Kronecker

/-!
# Kronecker Character Smoke Examples

Small examples for the local Kronecker-character API.
-/

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
