/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.RingTheory.ClassGroup
import QuadraticNumberFields.QuadraticOrder.Picard

/-!
# Class Numbers of Orders

This file names the Picard class-number interface for quadratic orders.

For maximal orders in Dedekind domains, mathlib's `ClassGroup` is equivalent to
`CommRing.Pic`; for nonmaximal orders, the Picard group is the right target for
the future Cox/order class-number formula.

## Main definitions

* `QuadraticOrder.picardClassNumber`: the cardinality of `CommRing.Pic O`.
* `QuadraticOrder.HasOrderClassNumberFormula`: a reusable Prop for formulas
  comparing the class number of an order with an overorder and a local factor.
-/

namespace QuadraticNumberFields
namespace QuadraticOrder

/-- The Picard class number of an order-like commutative ring. -/
noncomputable abbrev picardClassNumber (O : Type*) [CommRing O]
    [Fintype (CommRing.Pic O)] : ℕ :=
  Fintype.card (CommRing.Pic O)

/-- A generic order class-number formula comparing an order `O` with an
overorder `S` and a rational local factor.

Specialized files, such as the conductor-`2` Weber/CM route, should instantiate
this Prop only after providing the relevant order/Picard bridge. -/
def HasOrderClassNumberFormula (O S : Type*) [CommRing O] [CommRing S]
    [Fintype (CommRing.Pic O)] [Fintype (CommRing.Pic S)] (localFactor : ℚ) :
    Prop :=
  (picardClassNumber O : ℚ) = (picardClassNumber S : ℚ) * localFactor

/-- On a domain, the Picard class number agrees with the cardinality of
mathlib's ideal class group. -/
theorem picardClassNumber_eq_classGroup_card_of_domain
    (R : Type*) [CommRing R] [IsDomain R]
    [Fintype (CommRing.Pic R)] [Fintype (ClassGroup R)] :
    picardClassNumber R = Fintype.card (ClassGroup R) := by
  exact Fintype.card_congr (ClassGroup.equivPic R).toEquiv.symm

end QuadraticOrder
end QuadraticNumberFields
