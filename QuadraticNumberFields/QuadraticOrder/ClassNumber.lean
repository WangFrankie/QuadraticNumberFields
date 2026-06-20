/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
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

## Main statements

* `QuadraticOrder.picardClassNumber_le_card_mul_of_extensionMap_surjective_of_kernelEmbedsInto`:
  a finite-kernel upper bound for Picard class numbers along an order map.
* `QuadraticOrder.picardClassNumber_eq_card_mul_of_extensionMap_surjective_of_kernelEquiv`:
  the corresponding equality when the kernel is identified with the finite
  local group.
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

/-- If the Picard extension map is surjective and its kernel embeds into a
finite group `U`, then the Picard class number of the smaller order is bounded
by `|U|` times the Picard class number of the larger order.

This is the abstract order/Picard form of the upper-bound input supplied by the
current conductor-`2` fiber-residue injectivity route. -/
theorem picardClassNumber_le_card_mul_of_extensionMap_surjective_of_kernelEmbedsInto
    {O S U : Type*} [CommRing O] [CommRing S] [Group U]
    [Fintype (CommRing.Pic O)] [Fintype (CommRing.Pic S)] [Fintype U]
    (i : O →+* S) (hsurj : Picard.ExtensionSurjective i)
    (hker : Picard.KernelEmbedsInto (U := U) i) :
    picardClassNumber O ≤ Fintype.card U * picardClassNumber S := by
  let f : CommRing.Pic O →* CommRing.Pic S := Picard.extensionMap i
  have hcard :
      Nat.card (CommRing.Pic O) = Nat.card ((CommRing.Pic O) ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hquot :
      Nat.card ((CommRing.Pic O) ⧸ f.ker) = Nat.card (CommRing.Pic S) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  have hker_le : Nat.card f.ker ≤ Fintype.card U := by
    simpa [f, Picard.relativeKernel] using
      Picard.natCard_relativeKernel_le_of_kernelEmbedsInto i hker
  calc
    picardClassNumber O = Nat.card (CommRing.Pic O) := by
      simp [picardClassNumber, Nat.card_eq_fintype_card]
    _ = Nat.card ((CommRing.Pic O) ⧸ f.ker) * Nat.card f.ker := hcard
    _ = Nat.card (CommRing.Pic S) * Nat.card f.ker := by rw [hquot]
    _ ≤ Nat.card (CommRing.Pic S) * Fintype.card U := Nat.mul_le_mul_left _ hker_le
    _ = Fintype.card U * picardClassNumber S := by
      simp [picardClassNumber, Nat.card_eq_fintype_card, Nat.mul_comm]

/-- If the Picard extension map is surjective and its kernel is equivalent to a
finite group `U`, then the Picard class number of the smaller order is exactly
`|U|` times the Picard class number of the larger order.

This is the abstract order/Picard shape of the equality needed for a Cox-style
order class-number formula. -/
theorem picardClassNumber_eq_card_mul_of_extensionMap_surjective_of_kernelEquiv
    {O S U : Type*} [CommRing O] [CommRing S] [Group U]
    [Fintype (CommRing.Pic O)] [Fintype (CommRing.Pic S)] [Fintype U]
    (i : O →+* S) (hsurj : Picard.ExtensionSurjective i)
    (hker : Picard.KernelEquiv (U := U) i) :
    picardClassNumber O = Fintype.card U * picardClassNumber S := by
  let f : CommRing.Pic O →* CommRing.Pic S := Picard.extensionMap i
  have hcard :
      Nat.card (CommRing.Pic O) = Nat.card ((CommRing.Pic O) ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hquot :
      Nat.card ((CommRing.Pic O) ⧸ f.ker) = Nat.card (CommRing.Pic S) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  have hker_card : Nat.card f.ker = Fintype.card U := by
    rcases hker with ⟨e⟩
    simpa [f, Picard.relativeKernel, Nat.card_eq_fintype_card] using
      Nat.card_congr e.toEquiv
  calc
    picardClassNumber O = Nat.card (CommRing.Pic O) := by
      simp [picardClassNumber, Nat.card_eq_fintype_card]
    _ = Nat.card ((CommRing.Pic O) ⧸ f.ker) * Nat.card f.ker := hcard
    _ = Nat.card (CommRing.Pic S) * Fintype.card U := by rw [hquot, hker_card]
    _ = Fintype.card U * picardClassNumber S := by
      simp [picardClassNumber, Nat.card_eq_fintype_card, Nat.mul_comm]

end QuadraticOrder
end QuadraticNumberFields
