/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.CategoryTheory.Discrete.Basic
import QuadraticNumberFields.QuadraticField.Category
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.Parameters

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

/-! ## Isomorphism-Class Classification

A squarefree parameter is determined by, and determines, the `ℚ`-algebra
isomorphism class of its standard model.  We record this as two statements:

* `stdModel_essentiallySurjective`: every quadratic field is `ℚ`-algebra
  isomorphic to a standard model `ℚ(√d)` of some squarefree parameter.
* `eq_of_algEquiv`: the parameter is recovered uniquely from the isomorphism
  class.

Together these say that `p ↦ ℚ(√(p.d))` induces a **bijection** between
`SqfreeParam` and the `ℚ`-algebra-isomorphism classes of quadratic fields.

This is the correct classification statement.  It is **not** a categorical
equivalence `Discrete SqfreeParam ≌ QuadraticFieldCat`: the discrete category
has only identities, while each quadratic field has a non-trivial conjugation
automorphism (`Task 5`/`Task 10`).

Both statements use `≃ₐ[ℚ]` with the canonical `QuadraticAlgebra` instances on
`Qsqrtd` (made explicit with `@AlgEquiv … instAlgebra …`).  They are phrased at
the level of `ℚ`-algebra equivalences rather than `QuadraticFieldCat`
isomorphisms: bridging to the category layer would require identifying the
`Algebra ℚ` instance bundled in a `QuadraticFieldCat` object with the canonical
one on `Qsqrtd`, but those agree only up to `Subsingleton.elim` and are not
definitionally equal (the same diamond met by
`Qsqrtd.algEquiv_self_eq_refl_or_star`).  Pinning the canonical instances keeps
instance resolution deterministic across import contexts. -/

/-- A squarefree parameter is determined by its integer `d` (the squarefree and
`≠ 1` fields are propositions). -/
theorem SqfreeParam.eq_of_d_eq {p q : SqfreeParam} (h : p.d = q.d) : p = q := by
  cases p; cases q; subst h; rfl

/-- **Essential surjectivity.** Every quadratic field is `ℚ`-algebra isomorphic
to the standard model `ℚ(√d)` of some squarefree parameter. -/
theorem SqfreeParam.stdModel_essentiallySurjective
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    ∃ p : SqfreeParam, Nonempty (@AlgEquiv ℚ K (Qsqrtd (p.d : ℚ)) Rat.commSemiring _
      QuadraticAlgebra.instCommSemiring.toSemiring _ QuadraticAlgebra.instAlgebra) := by
  obtain ⟨d, hsf, hne, ⟨e⟩⟩ := exists_algEquiv_qsqrtd K
  exact ⟨⟨d, hsf, hne⟩, ⟨e⟩⟩

/-- **Uniqueness of the parameter.** If the standard models of two squarefree
parameters are `ℚ`-algebra isomorphic, the parameters are equal. -/
theorem SqfreeParam.eq_of_algEquiv {p q : SqfreeParam}
    (e : @AlgEquiv ℚ (Qsqrtd (p.d : ℚ)) (Qsqrtd (q.d : ℚ)) Rat.commSemiring
      QuadraticAlgebra.instCommSemiring.toSemiring QuadraticAlgebra.instCommSemiring.toSemiring
      QuadraticAlgebra.instAlgebra QuadraticAlgebra.instAlgebra) : p = q :=
  SqfreeParam.eq_of_d_eq
    (Qsqrtd.param_unique p.d q.d e p.squarefree p.ne_one q.squarefree)

