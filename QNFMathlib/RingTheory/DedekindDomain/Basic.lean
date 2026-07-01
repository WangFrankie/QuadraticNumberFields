/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic
import QNFMathlib.RingTheory.Krull

/-!
# Dedekind-Domain Transport Across Ring Equivalences

Material destined for mathlib.
-/

namespace RingEquiv

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Transport `IsDedekindDomain` across a ring equivalence.

A Dedekind domain is characterized by: (1) Noetherian, (2) domain,
(3) integrally closed, (4) dimension ≤ 1. Each of these is individually
invariant under ring isomorphism, so the conjunction is as well. -/
-- Repository use: `QuadraticField/Transport.lean` uses this to transport
-- Dedekind-domain structures across ring equivalences.
theorem isDedekindDomain (e : R ≃+* S) [IsDedekindDomain R] :
    IsDedekindDomain S := by
  letI : IsNoetherianRing R :=
    show IsNoetherian R R from IsDedekindRing.toIsNoetherian
  letI : IsDomain S := e.toMulEquiv.isDomain_iff.mp inferInstance
  letI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  letI : IsIntegrallyClosed S := IsIntegrallyClosed.of_equiv e
  letI : Ring.DimensionLEOne S := dimensionLEOne e
  letI : IsDedekindRing S :=
    { toIsNoetherian := show IsNoetherian S S from inferInstance
      toDimensionLEOne := inferInstance
      toIsIntegralClosure :=
        show IsIntegralClosure S S (FractionRing S) from inferInstance }
  infer_instance

/-- `IsDedekindDomain` is invariant under ring equivalence. -/
-- Repository use: currently support API for the forward transport theorem above;
-- no direct non-patch reference is expected yet.
theorem isDedekindDomain_iff (e : R ≃+* S) :
    IsDedekindDomain R ↔ IsDedekindDomain S := by
  exact ⟨fun _ => isDedekindDomain e, fun _ => isDedekindDomain e.symm⟩

end CommRing

end RingEquiv
