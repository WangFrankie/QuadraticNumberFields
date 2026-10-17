/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index

/-!
# Finite Group Homomorphism Cardinality Lemmas

Material destined for mathlib.
-/

namespace MonoidHom

section FiniteGroups

variable {G H : Type*} [Group G] [Group H]

/-- A surjective homomorphism between finite groups is injective iff its domain
and codomain have the same cardinality. -/
theorem injective_iff_nat_card_eq_of_surjective
    [Finite G] (f : G →* H) (hf : Function.Surjective f) :
    Function.Injective f ↔ Nat.card G = Nat.card H := by
  constructor
  · intro hinj
    exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf⟩)
  · intro hcard
    exact (hf.bijective_of_nat_card_le (le_of_eq hcard)).1

/-- A surjective homomorphism between finite groups has trivial kernel iff its
domain and codomain have the same cardinality. -/
theorem ker_eq_bot_iff_nat_card_eq_of_surjective
    [Finite G] (f : G →* H) (hf : Function.Surjective f) :
    f.ker = ⊥ ↔ Nat.card G = Nat.card H := by
  rw [← injective_iff_nat_card_eq_of_surjective f hf]
  exact MonoidHom.ker_eq_bot_iff f

/-- The cardinality of the domain of a surjective homomorphism of finite groups
is the product of the cardinalities of its kernel and codomain. -/
theorem nat_card_eq_card_ker_mul_card_of_surjective
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card G = Nat.card f.ker * Nat.card H := by
  calc
    Nat.card G = Nat.card (G ⧸ f.ker) * Nat.card f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    _ = Nat.card H * Nat.card f.ker := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    _ = Nat.card f.ker * Nat.card H := mul_comm _ _

/-- If a homomorphism from a finite group has nontrivial kernel, then its image
has cardinality at most half the domain cardinality. -/
theorem two_mul_card_range_le
    [Finite G] (f : G →* H) (hker : f.ker ≠ ⊥) :
    2 * Nat.card f.range ≤ Nat.card G := by
  have hker_card : 2 ≤ Nat.card f.ker := by
    have hlt : 1 < Nat.card f.ker := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hker
    exact Nat.succ_le_of_lt hlt
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card G := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index f.ker
  calc
    2 * Nat.card f.range ≤ Nat.card f.ker * Nat.card f.range :=
      Nat.mul_le_mul_right _ hker_card
    _ = Nat.card G := hcard

end FiniteGroups

end MonoidHom
