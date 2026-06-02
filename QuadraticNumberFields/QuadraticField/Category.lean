/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Category.AlgCat.Basic
import QuadraticNumberFields.QuadraticField.Basic

/-!
# The Category of Quadratic Fields

This file defines the bundled category of quadratic fields over `ℚ`.

The concrete models `Qsqrtd d` are not part of the definition of the category.
They instead provide a family of standard objects through `QuadraticFieldCat.ofQsqrtd`.

## Main definitions

* `QuadraticFieldCat`: bundled abstract quadratic fields over `ℚ`.
* `QuadraticFieldCat.of`: bundle any `QuadraticField` over `ℚ`.
* `QuadraticFieldCat.ofQsqrtd`: the standard model `ℚ(√d)` as a bundled object.
* `QuadraticFieldCat.forgetToAlgCat`: the forgetful functor to `AlgCat ℚ`.
-/

open CategoryTheory

universe u

/-- The category of quadratic fields over `ℚ`.

An object is a field equipped with a `ℚ`-algebra structure and a proof that it is
a quadratic extension of `ℚ`. Morphisms are `ℚ`-algebra homomorphisms.
-/
structure QuadraticFieldCat where
  /-- The underlying type of a bundled quadratic field. -/
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra ℚ carrier]
  [quadraticField : QuadraticField carrier]

attribute [instance] QuadraticFieldCat.field
attribute [instance] QuadraticFieldCat.algebra
attribute [instance] QuadraticFieldCat.quadraticField

namespace QuadraticFieldCat

instance : CoeSort QuadraticFieldCat (Type u) :=
  ⟨fun K => K.carrier⟩

attribute [coe] QuadraticFieldCat.carrier

/-- Bundle any quadratic extension of `ℚ` as an object of `QuadraticFieldCat`. -/
abbrev of (K : Type u) [Field K] [Algebra ℚ K]
    [QuadraticField K] : QuadraticFieldCat.{u} :=
  ⟨K⟩

/-- The type of morphisms in `QuadraticFieldCat`. -/
abbrev Hom (K L : QuadraticFieldCat.{u}) : Type u :=
  K →ₐ[ℚ] L

instance : Category QuadraticFieldCat where
  Hom := Hom
  id K := AlgHom.id ℚ K
  comp f g := g.comp f

/-- The standard model `ℚ(√d)` as a bundled quadratic field. -/
abbrev ofQsqrtd (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    QuadraticFieldCat :=
  of (Qsqrtd (d : ℚ))

/-- Forget a quadratic field to its underlying `ℚ`-algebra. -/
def forgetToAlgCat : QuadraticFieldCat.{u} ⥤ AlgCat.{u} ℚ where
  obj K := AlgCat.of ℚ K
  map f := AlgCat.ofHom f

@[simp]
theorem forgetToAlgCat_obj (K : QuadraticFieldCat.{u}) :
    forgetToAlgCat.obj K = AlgCat.of ℚ K :=
  rfl

@[simp]
theorem forgetToAlgCat_map {K L : QuadraticFieldCat.{u}} (f : K ⟶ L) :
    forgetToAlgCat.map f = AlgCat.ofHom f :=
  rfl

end QuadraticFieldCat
