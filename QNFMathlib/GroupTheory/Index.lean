/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.Index

/-!
# Finite Group Homomorphism Cardinality Lemmas

Material destined for mathlib.
-/

namespace MonoidHom

/-- A surjective homomorphism between finite groups is injective iff its domain
and codomain have the same cardinality. -/
theorem injective_iff_nat_card_eq_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    Function.Injective f ↔ Nat.card G = Nat.card H := by
  simpa [Function.Bijective, hf] using Nat.bijective_iff_surjective_and_card (f : G → H)

/-- A surjective homomorphism between finite groups has trivial kernel iff its
domain and codomain have the same cardinality. -/
theorem ker_eq_bot_iff_nat_card_eq_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    f.ker = ⊥ ↔ Nat.card G = Nat.card H :=
  (MonoidHom.ker_eq_bot_iff f).trans (injective_iff_nat_card_eq_of_surjective f hf)

end MonoidHom
