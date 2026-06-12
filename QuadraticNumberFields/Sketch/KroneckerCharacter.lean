/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Mathlib.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# WIP Kronecker Dirichlet Character

This file isolates the incomplete `DirichletCharacter` packaging of the Kronecker
symbol. It is intentionally kept out of the stable root import until the `MulChar`
obligations are sorry-free.

## Status

The value map is `x ↦ kroneckerSymNat D x.val`. Three obligations remain open:

* `map_one'`: the representative of `1 : ZMod D.natAbs` evaluates to `1`.
* `map_mul'`: the value is independent of representatives modulo `D.natAbs` and
  multiplicative. Right-periodicity of the Kronecker symbol modulo `D` only holds
  for `D ≡ 0, 1 [ZMOD 4]` (a general `D`, such as `D = 3`, has period `4 * |D|`),
  and its proof packages quadratic reciprocity. A sorry-free construction should
  therefore either restrict to discriminant inputs `D ≡ 0, 1 [ZMOD 4]` or change
  the modulus.
* `map_nonunit'`: every nonunit of `ZMod D.natAbs` shares a factor with `D`, so its
  Kronecker value is `0`.
-/

namespace QuadraticNumberFields

/-- WIP: the Kronecker symbol `(D / ·)` as a Dirichlet character modulo `D.natAbs`.

The intended value map is `x ↦ kroneckerSymNat D x.val`; see the module docstring
for the outstanding obligations. The construction is mathematically valid only for
`D ≡ 0, 1 [ZMOD 4]`, which covers every quadratic field discriminant. -/
noncomputable def kroneckerCharacter (D : ℤ) : DirichletCharacter ℤ D.natAbs := by
  classical
  -- This incomplete obligation is isolated from stable imports by this file boundary.
  sorry

end QuadraticNumberFields
