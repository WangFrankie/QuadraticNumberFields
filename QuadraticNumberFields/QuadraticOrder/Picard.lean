/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.RingTheory.PicardGroup
import QuadraticNumberFields.QuadraticOrder.Basic

/-!
# Picard Interfaces for Orders

This file gives names to the Picard-group maps that appear in the order
class-number route.  It reuses mathlib's `CommRing.Pic`; it does not introduce a
parallel Picard group.

The conductor exact sequence for nonmaximal quadratic orders is not yet proved
in this repository.  The definitions here provide the stable target API for
that future proof.

## Main definitions

* `QuadraticOrder.Picard.extensionMap`: the Picard map induced by a ring
  homomorphism of orders.
* `QuadraticOrder.Picard.relativeKernel`: the kernel of that extension map.
* `QuadraticOrder.Picard.KernelEmbedsInto`: a named Prop for the kernel
  embedding supplied by conductor/residue-unit theory.
* `QuadraticOrder.Picard.KernelEquiv`: a named Prop for identifying the kernel
  with a concrete local group.
* `QuadraticOrder.Picard.ExtensionSurjective`: a named Prop for surjectivity of
  the extension map.
-/

namespace QuadraticNumberFields
namespace QuadraticOrder

namespace Picard

/-- The Picard-group map induced by extending scalars along a ring homomorphism
of orders. -/
noncomputable def extensionMap {O S : Type*} [CommRing O] [CommRing S]
    (i : O →+* S) : CommRing.Pic O →* CommRing.Pic S :=
  CommRing.Pic.mapRingHom i

/-- The relative Picard kernel of an order map.  For a nonmaximal order included
in its maximal order, this is the group controlled by the conductor exact
sequence. -/
noncomputable def relativeKernel {O S : Type*} [CommRing O] [CommRing S]
    (i : O →+* S) : Subgroup (CommRing.Pic O) :=
  (extensionMap i).ker

/-- The conductor/residue-unit input that the order route should eventually
prove: the relative Picard kernel embeds into a concrete local unit quotient
`U`. -/
def KernelEmbedsInto {O S U : Type*} [CommRing O] [CommRing S] [Group U]
    (i : O →+* S) : Prop :=
  Nonempty (relativeKernel i ↪ U)

/-- The stronger conductor/residue-unit input needed for an exact class-number
formula: the relative Picard kernel is identified with a concrete local group
`U`. -/
def KernelEquiv {O S U : Type*} [CommRing O] [CommRing S] [Group U]
    (i : O →+* S) : Prop :=
  Nonempty (relativeKernel i ≃* U)

/-- A kernel identification supplies a kernel embedding. -/
theorem kernelEmbedsInto_of_kernelEquiv
    {O S U : Type*} [CommRing O] [CommRing S] [Group U]
    (i : O →+* S) (h : KernelEquiv (U := U) i) : KernelEmbedsInto (U := U) i := by
  rcases h with ⟨e⟩
  exact ⟨e.toEmbedding⟩

/-- A named Prop for injectivity of the Picard extension map. -/
def ExtensionInjective {O S : Type*} [CommRing O] [CommRing S]
    (i : O →+* S) : Prop :=
  Function.Injective (extensionMap i)

/-- A named Prop for surjectivity of the Picard extension map. -/
def ExtensionSurjective {O S : Type*} [CommRing O] [CommRing S]
    (i : O →+* S) : Prop :=
  Function.Surjective (extensionMap i)

/-- An embedding of the relative Picard kernel into a finite group bounds the
kernel cardinality. -/
theorem natCard_relativeKernel_le_of_kernelEmbedsInto
    {O S U : Type*} [CommRing O] [CommRing S] [Group U] [Fintype U]
    (i : O →+* S) (h : KernelEmbedsInto (U := U) i) :
    Nat.card (relativeKernel i) ≤ Fintype.card U := by
  rcases h with ⟨e⟩
  simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective e e.injective

end Picard

end QuadraticOrder
end QuadraticNumberFields
