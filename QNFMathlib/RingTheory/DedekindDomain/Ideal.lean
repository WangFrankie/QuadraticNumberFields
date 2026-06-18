/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Principality Criterion for Ideals of Dedekind Domains

Material destined for mathlib.

In a Dedekind domain, every nonzero ideal factors into prime ideals, so an
ideal all of whose prime divisors are principal is itself principal. This is
the workhorse behind Minkowski-bound class-number computations: combined with
a bound asserting that every ideal class contains an ideal of small norm, it
reduces triviality of the class group to principality of finitely many prime
ideals.
-/

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- In a Dedekind domain, an ideal whose prime divisors are all principal is
itself principal. -/
theorem isPrincipal_of_forall_isPrime_dvd_isPrincipal {I : Ideal R}
    (h : ∀ P : Ideal R, P.IsPrime → P ∣ I → P.IsPrincipal) :
    I.IsPrincipal := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact ⟨0, by simp⟩
  | h₂ J hJ =>
    rw [Ideal.isUnit_iff.mp hJ]
    exact ⟨1, by simp⟩
  | h₃ J P hJ hP ih =>
    obtain ⟨a, ha⟩ := h P (Ideal.isPrime_of_prime hP) (dvd_mul_right P J)
    obtain ⟨b, hb⟩ := ih fun Q hQ hQd => h Q hQ (hQd.mul_left P)
    exact ⟨a * b, by rw [ha, hb, Ideal.span_singleton_mul_span_singleton]⟩

end Ideal
