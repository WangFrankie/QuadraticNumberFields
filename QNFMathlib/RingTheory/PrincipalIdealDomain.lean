/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Principal Ideal Rings

Material destined for mathlib.
-/

namespace RingEquiv

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Transport `IsPrincipalIdealRing` across a ring equivalence. -/
theorem isPrincipalIdealRing (e : R ≃+* S) [IsPrincipalIdealRing R] :
    IsPrincipalIdealRing S :=
  IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective

/-- `IsPrincipalIdealRing` is invariant under ring equivalence. -/
theorem isPrincipalIdealRing_iff (e : R ≃+* S) :
    IsPrincipalIdealRing R ↔ IsPrincipalIdealRing S := by
  exact ⟨fun _ => isPrincipalIdealRing e, fun _ => isPrincipalIdealRing e.symm⟩

end Semiring

end RingEquiv
