/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Basic Class Field Interfaces

Material destined for mathlib.

This file records lightweight predicates for the first class-field-theory
interfaces around Hilbert class fields. The definitions deliberately avoid
choosing a Hilbert class field object; they only package the properties of a
candidate extension.

## Main definitions

- `NumberField.IsUnramifiedAtFinitePlaces`: an extension of number fields is
  unramified at every finite prime of the top field.
- `NumberField.IsEverywhereUnramified`: an extension is unramified at both finite
  and infinite places.
- `NumberField.IsFiniteAbelianEverywhereUnramified`: the finite abelian
  everywhere-unramified extensions of a number field.
- `NumberField.IsHilbertClassField`: a degree-maximal finite abelian
  everywhere-unramified extension.

## Implementation notes

The `IsHilbertClassField` predicate uses a degree-maximality condition instead
of embedding all candidate extensions into a chosen algebraic closure. This
keeps the initial API independent of a global algebraic-closure model while
still giving a usable class-field-theory boundary.
-/

open scoped NumberField

namespace NumberField

/-- An extension of number fields is unramified at finite places if every
nonzero prime ideal of the ring of integers of the top field is unramified over
the ring of integers of the base field. -/
class IsUnramifiedAtFinitePlaces (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop where
  isUnramifiedAt : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
    Algebra.IsUnramifiedAt (𝓞 K) P

/-- An extension of number fields is everywhere unramified if it is unramified
at both finite and infinite places. -/
class IsEverywhereUnramified (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop where
  [finite : IsUnramifiedAtFinitePlaces K L]
  [infinite : IsUnramifiedAtInfinitePlaces K L]

/-- An everywhere-unramified extension is unramified at finite places. -/
instance (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [h : IsEverywhereUnramified K L] : IsUnramifiedAtFinitePlaces K L :=
  h.finite

/-- An everywhere-unramified extension is unramified at infinite places. -/
instance (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [h : IsEverywhereUnramified K L] : IsUnramifiedAtInfinitePlaces K L :=
  h.infinite

/-- A finite abelian everywhere-unramified extension of number fields. -/
class IsFiniteAbelianEverywhereUnramified (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop where
  [finiteDimensional : FiniteDimensional K L]
  [isGalois : IsGalois K L]
  isAbelian : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ
  [unramified : IsEverywhereUnramified K L]

/-- A finite abelian everywhere-unramified extension is everywhere unramified. -/
instance (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [h : IsFiniteAbelianEverywhereUnramified K L] : IsEverywhereUnramified K L :=
  h.unramified

/-- A Hilbert class field is a degree-maximal finite abelian
everywhere-unramified extension of a number field. -/
class IsHilbertClassField (K H : Type*) [Field K] [NumberField K]
    [Field H] [NumberField H] [Algebra K H] : Prop extends
    IsFiniteAbelianEverywhereUnramified K H where
  maximal : ∀ (L : Type*) [Field L] [NumberField L] [Algebra K L],
    IsFiniteAbelianEverywhereUnramified K L → Module.finrank K L ≤ Module.finrank K H

/-- A Hilbert class field is finite abelian and everywhere unramified. -/
instance (K H : Type*) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H]
    [h : IsHilbertClassField K H] : IsFiniteAbelianEverywhereUnramified K H :=
  h.toIsFiniteAbelianEverywhereUnramified

end NumberField
