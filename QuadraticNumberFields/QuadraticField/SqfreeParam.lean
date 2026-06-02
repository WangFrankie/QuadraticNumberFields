/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.CategoryTheory.Discrete.Basic
import QuadraticNumberFields.QuadraticField.Category

/-!
# Normalized Squarefree Parameters

This file packages the data of a normalized squarefree parameter `d ≠ 1` as a
structure `SqfreeParam`.  These are the parameters that index the standard
models `ℚ(√d)`: every quadratic field over `ℚ` is isomorphic to `ℚ(√d)` for a
unique such `d`.

Bundling the parameter data lets downstream constructions (functors into
`QuadraticFieldCat`, the isomorphism-class classification) take a single
structure argument instead of a bare integer plus two `Fact` hypotheses.

## Main definitions

* `SqfreeParam`: a squarefree integer `d ≠ 1`.
* `SqfreeParam.qsqrtd`: the standard model `ℚ(√d)` as a type.
* `SqfreeParam.toQuadraticFieldCat`: the standard model as a bundled object of
  `QuadraticFieldCat`.
* `SqfreeParamCat`: the discrete category on `SqfreeParam`.
* `SqfreeParam.stdModel`: the functor sending each parameter to its standard
  model object.

## Implementation notes

`SqfreeParam.stdModel` only expresses the family of standard-model *objects*
indexed by parameters; it is **not** a categorical equivalence with
`QuadraticFieldCat`.  The discrete category `SqfreeParamCat` has only identity
morphisms, whereas each object of `QuadraticFieldCat` has a non-trivial
`ℚ`-automorphism (the conjugation), so the two categories are not equivalent.
The correct classification statement is one of isomorphism classes, pursued
separately.
-/

/-- A normalized squarefree parameter: a squarefree integer `d ≠ 1`.

These index the standard quadratic-field models `ℚ(√d)`. -/
structure SqfreeParam where
  /-- The underlying integer. -/
  d : ℤ
  /-- The integer is squarefree. -/
  squarefree : Squarefree d
  /-- The integer is not `1` (so that `ℚ(√d)` is a genuine field, not `ℚ × ℚ`). -/
  ne_one : d ≠ 1

namespace SqfreeParam

instance (p : SqfreeParam) : Fact (Squarefree p.d) := ⟨p.squarefree⟩

instance (p : SqfreeParam) : Fact (p.d ≠ 1) := ⟨p.ne_one⟩

/-- The standard model `ℚ(√d)` associated to a squarefree parameter. -/
def qsqrtd (p : SqfreeParam) : Type :=
  Qsqrtd (p.d : ℚ)

/-- The standard model `ℚ(√d)` as a bundled object of `QuadraticFieldCat`. -/
def toQuadraticFieldCat (p : SqfreeParam) : QuadraticFieldCat :=
  QuadraticFieldCat.ofQsqrtd p.d

@[simp]
theorem toQuadraticFieldCat_carrier (p : SqfreeParam) :
    (p.toQuadraticFieldCat).carrier = Qsqrtd (p.d : ℚ) :=
  rfl

end SqfreeParam

open CategoryTheory

/-- The discrete category on normalized squarefree parameters. -/
abbrev SqfreeParamCat := Discrete SqfreeParam

/-- The standard-model functor: each parameter `d` is sent to the bundled
standard model `ℚ(√d)`.

This functor only records the family of standard-model objects; it is not a
categorical equivalence (see the module docstring). -/
def SqfreeParam.stdModel : SqfreeParamCat ⥤ QuadraticFieldCat :=
  Discrete.functor SqfreeParam.toQuadraticFieldCat

@[simp]
theorem SqfreeParam.stdModel_obj (p : SqfreeParam) :
    SqfreeParam.stdModel.obj ⟨p⟩ = p.toQuadraticFieldCat :=
  rfl

