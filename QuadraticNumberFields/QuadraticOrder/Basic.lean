/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Quadratic Orders

This file contains the basic project interface for orders in rational algebras.

The intent is deliberately narrow: this directory is the home for reusable
quadratic-order and order-Picard APIs that are missing from the current mathlib
dependency but are not specific to the Weber/CM conductor-`2` route.

## API placement

* General order/Picard interfaces belong under `QuadraticNumberFields.QuadraticOrder`.
* Pure mathlib lemmas about existing objects such as `CommRing.Pic`, `ClassGroup`,
  `FractionalIdeal`, `Ideal`, or `Submodule` belong under `QNFMathlib`.
* Prime-specific Weber/CM conductor-`2` statements belong under
  `QuadraticNumberFields.Heegner.WeberCM.ConductorTwo`.

## Main definitions

* `QuadraticOrder.IsOrderIn`: an order represented as a ring embedded in an
  ambient rational algebra.
* `QuadraticOrder.IsQuadraticOrderIn`: the specialization whose ambient algebra
  has dimension `2` over `ℚ`.
-/

namespace QuadraticNumberFields
namespace QuadraticOrder

/-- An order represented as a commutative ring embedded in an ambient rational
algebra.

This is a typeclass because the object is the ring `O`; the class records the
laws that make `O` an order in `K`.  It is not a bundled `Data` container. -/
class IsOrderIn (O K : Type*) [CommRing O] [Field K] [Algebra ℚ K] [Algebra O K] :
    Prop where
  /-- The chosen map from the order into the ambient algebra is injective. -/
  algebraMap_injective : Function.Injective (algebraMap O K)
  /-- An order is finite as a `ℤ`-module. -/
  finite : Module.Finite ℤ O
  /-- The order spans the ambient rational algebra after extending scalars to `ℚ`. -/
  spans_top : Submodule.span ℚ (Set.range fun x : O => algebraMap O K x) = ⊤

/-- A quadratic order is an order whose ambient rational algebra has dimension
`2` over `ℚ`. -/
class IsQuadraticOrderIn (O K : Type*) [CommRing O] [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [Algebra O K] : Prop extends IsOrderIn O K where
  /-- The ambient algebra is quadratic over `ℚ`. -/
  finrank_eq_two : Module.finrank ℚ K = 2

end QuadraticOrder
end QuadraticNumberFields
