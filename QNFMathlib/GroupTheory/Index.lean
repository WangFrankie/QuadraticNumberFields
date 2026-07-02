/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Exact
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

/-- A finite short exact sequence of groups has the expected cardinality
formula. -/
theorem nat_card_eq_mul_of_mulExact_of_surjective
    {K G H : Type*} [Group K] [Group G] [Group H] [Finite K] [Finite G] [Finite H]
    (f : K →* G) (g : G →* H)
    (hf : Function.Injective f) (hfg : Function.MulExact f g) (hg : Function.Surjective g) :
    Nat.card G = Nat.card K * Nat.card H := by
  have hker : g.ker = f.range := hfg.monoidHom_ker_eq
  have hcard_range_f : Nat.card f.range = Nat.card K := by
    exact (Nat.card_eq_of_bijective f.rangeRestrict
      ⟨fun _ _ hxy => hf (Subtype.ext_iff.mp hxy),
        MonoidHom.rangeRestrict_surjective f⟩).symm
  have hcard_ker : Nat.card g.ker = Nat.card K := by
    rw [hker, hcard_range_f]
  have hcard_range_g : Nat.card g.range = Nat.card H := by
    have htop : g.range = ⊤ := MonoidHom.range_eq_top.mpr hg
    rw [htop]
    simp
  calc
    Nat.card G = Nat.card g.ker * g.ker.index := by
      exact (Subgroup.card_mul_index g.ker).symm
    _ = Nat.card K * Nat.card H := by
      rw [hcard_ker, Subgroup.index_ker, hcard_range_g]

end MonoidHom
