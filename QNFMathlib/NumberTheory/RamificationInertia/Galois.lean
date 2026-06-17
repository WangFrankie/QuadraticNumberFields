/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.NormalClosure
import QNFMathlib.FieldTheory.Galois.Basic

/-!
# Galois Extensions and Ramification

Material destined for mathlib.
-/

/-- A quadratic Dedekind extension with `ringChar R ≠ 2` is a Galois extension at the
level of fraction fields. This is the bridge from `IsQuadraticExtension R S` to
`IsGaloisGroup Gal(L/K) R S`, where `K = FractionRing R` and `L = FractionRing S`. -/
-- Repository use: `Splitting/Factorization.lean` installs this as a local
-- instance so `ramificationIdxIn_eq_of_mem` can rewrite the Dedekind
-- factorization exponents uniformly. This use is partly implicit through
-- typeclass search for `IsGaloisGroup`.
theorem Algebra.IsQuadraticExtension.isGaloisGroup
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] (hchar : ringChar R ≠ 2) :
    letI K := FractionRing R
    letI L := FractionRing S
    letI := Ring.instAlgebraFractionRing
    letI := IsIntegralClosure.MulSemiringAction R K L S
    IsGaloisGroup Gal(L/K) R S := by
  letI K := FractionRing R
  letI L := FractionRing S
  letI := Ring.instAlgebraFractionRing
  letI := IsIntegralClosure.MulSemiringAction R K L S
  have : Algebra.IsQuadraticExtension K L :=
    Algebra.IsQuadraticExtension.fractionRing (R := R) (S := S)
  have hcharK : ringChar K ≠ 2 := by
    haveI : CharP K (ringChar R) :=
      IsFractionRing.charP_of_isFractionRing (R := R) (K := K) (ringChar R)
    simpa [ringChar.eq K (ringChar R)] using hchar
  have : Algebra.IsSeparable K L :=
    Algebra.IsQuadraticExtension.isSeparable_of_field_of_char_ne_two hcharK
  exact IsGaloisGroup.of_isFractionRing Gal(L/K) R S K L
