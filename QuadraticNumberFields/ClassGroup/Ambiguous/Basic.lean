/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Torsion

/-!
# Ambiguous Narrow Classes

This file contains the narrow-class-group part of the elementary bridge
`fixed by inversion = two-torsion`. For a quadratic extension, conjugation acts
as inversion on ideal classes; the conjugation-specific ideal arithmetic belongs
in the ramified/ambiguous layer, while this file keeps the group-theoretic
strict-class-group interface independent.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

/-- Narrow ideal classes fixed by inversion. In the quadratic ambiguous-class
argument, this is the result-side object after proving that conjugation acts as
inversion on strict ideal classes. -/
def InversionFixedClass (R : Type*) [CommRing R] [IsDomain R] :=
  {C : _root_.NarrowClassGroup R // C = C⁻¹}

/-- The two-torsion subgroup of the narrow class group is equivalent to the
subtype of inversion-fixed narrow classes. -/
def twoTorsionEquivInversionFixedClass (R : Type*) [CommRing R] [IsDomain R] :
    _root_.NarrowClassGroup.twoTorsion R ≃ InversionFixedClass R where
  toFun C := by
    refine ⟨(C : _root_.NarrowClassGroup R), ?_⟩
    have hpow : (C : _root_.NarrowClassGroup R) ^ 2 = 1 := by
      simpa using (_root_.NarrowClassGroup.mem_twoTorsion_iff R C).mp C.2
    have hmul : (C : _root_.NarrowClassGroup R) * C = 1 := by
      simpa [pow_two] using hpow
    exact (eq_inv_iff_mul_eq_one).2 hmul
  invFun C := by
    refine ⟨C.1, ?_⟩
    rw [_root_.NarrowClassGroup.mem_twoTorsion_iff]
    have hmul : C.1 * C.1 = 1 := by
      nth_rewrite 1 [C.2]
      rw [inv_mul_cancel]
    simpa [pow_two] using hmul
  left_inv C := by
    ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

/-- The two-torsion subgroup and the inversion-fixed narrow classes have the
same cardinality. This is the narrow group-theoretic form of
`ambiguous narrow classes = Cl⁺[2]` once conjugation has been identified with
inversion. -/
theorem card_twoTorsion_eq_card_inversionFixedClass
    (R : Type*) [CommRing R] [IsDomain R] :
    Nat.card (_root_.NarrowClassGroup.twoTorsion R) = Nat.card (InversionFixedClass R) :=
  Nat.card_congr (twoTorsionEquivInversionFixedClass R)

end Ambiguous
end ClassGroup
end QuadraticNumberFields
