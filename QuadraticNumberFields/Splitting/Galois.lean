/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.NumberField.Galois
import QuadraticNumberFields.QuadraticField.RingOfIntegers
import QuadraticNumberFields.Splitting.Factorization

/-!
# Galois Actions and Splitting

This file records Galois-action facts for the fraction-field extension attached
to the ring of integers of a quadratic number field, especially the orbit and
stabilizer behavior of primes above split rational primes.
-/

namespace QuadraticNumberFields

open scoped NumberField Pointwise
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

section FractionRingGalois

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K]

local notation "OK" => NumberField.RingOfIntegers K

noncomputable local instance instMulSemiringActionFractionRingGalRingOfIntegersSplittingGalois
    [NumberField K] :
    MulSemiringAction Gal(FractionRing OK / FractionRing ℤ) OK :=
  IsIntegralClosure.MulSemiringAction ℤ (FractionRing ℤ) (FractionRing OK) OK

/-! ## Fraction-ring Galois group -/

/-- The fraction-field extension attached to the ring of integers of a quadratic
number field has degree two. -/
theorem finrank_fractionRing_ringOfIntegers_eq_two [NumberField K] :
    Module.finrank (FractionRing ℤ) (FractionRing OK) = 2 := by
  haveI : Algebra.IsAlgebraic ℤ OK := Algebra.IsAlgebraic.of_finite ℤ OK
  calc
    Module.finrank (FractionRing ℤ) (FractionRing OK) = Module.finrank ℤ OK := by
      simpa using
        (Algebra.IsAlgebraic.finrank_of_isFractionRing (R := ℤ) (R' := FractionRing ℤ)
          (S := OK) (S' := FractionRing OK))
    _ = Module.finrank ℚ K := by
      convert NumberField.RingOfIntegers.rank (K := K)
      exact Subsingleton.elim _ _
    _ = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

/-- The Galois group of the fraction-field extension attached to `𝓞 K / ℤ` has
two elements for a quadratic number field. -/
theorem card_gal_fractionRing_ringOfIntegers_eq_two [NumberField K] :
    Nat.card Gal(FractionRing OK / FractionRing ℤ) = 2 := by
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  haveI : IsGalois (FractionRing ℤ) (FractionRing OK) :=
    NumberField.isGalois_fractionRing_ringOfIntegers K
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_fractionRing_ringOfIntegers_eq_two K

/-! ## Split prime orbits -/

/-- Over a split rational prime, the fraction-field Galois orbit of any prime
above it has two elements. -/
theorem card_orbit_fractionRingGal_eq_two_of_mem_primesOver_of_isSplitIn [NumberField K]
    {p : Ideal ℤ} (hp0 : p ≠ ⊥) [p.IsMaximal] {P : Ideal OK}
    (hP : P ∈ Ideal.primesOver p OK) (hsplit : Ideal.IsSplitIn p OK) :
    Nat.card (MulAction.orbit Gal(FractionRing OK / FractionRing ℤ) P) = 2 := by
  letI := Algebra.IsQuadraticExtension.isGaloisGroup
    (R := ℤ) (S := OK) (by norm_num : ringChar ℤ ≠ 2)
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver p := hP.2
  rw [Algebra.IsInvariant.orbit_eq_primesOver ℤ OK
    Gal(FractionRing OK / FractionRing ℤ) p P]
  change (Ideal.primesOver p OK).ncard = 2
  exact Ideal.primesOver_ncard_eq_two_of_isSplitIn
    (S := OK) (p := p) (by simp [ringChar.eq_zero]) hp0 hsplit

/-- Over a split rational prime, the stabilizer in the fraction-field Galois
group of any prime above it is trivial. -/
theorem card_stabilizer_fractionRingGal_eq_one_of_mem_primesOver_of_isSplitIn [NumberField K]
    {p : Ideal ℤ} (hp0 : p ≠ ⊥) [p.IsMaximal] {P : Ideal OK}
    (hP : P ∈ Ideal.primesOver p OK) (hsplit : Ideal.IsSplitIn p OK) :
    Nat.card (MulAction.stabilizer Gal(FractionRing OK / FractionRing ℤ) P) = 1 := by
  letI := Algebra.IsQuadraticExtension.isGaloisGroup
    (R := ℤ) (S := OK) (by norm_num : ringChar ℤ ≠ 2)
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver p := hP.2
  have horbit_card :
      Nat.card (MulAction.orbit Gal(FractionRing OK / FractionRing ℤ) P) = 2 :=
    card_orbit_fractionRingGal_eq_two_of_mem_primesOver_of_isSplitIn
      (K := K) hp0 hP hsplit
  have hprod :
      Nat.card (MulAction.orbit Gal(FractionRing OK / FractionRing ℤ) P) *
          Nat.card (MulAction.stabilizer Gal(FractionRing OK / FractionRing ℤ) P) =
        Nat.card Gal(FractionRing OK / FractionRing ℤ) := by
    simpa [Nat.card_prod] using
      Nat.card_congr
        (MulAction.orbitProdStabilizerEquivGroup Gal(FractionRing OK / FractionRing ℤ) P)
  rw [horbit_card, card_gal_fractionRing_ringOfIntegers_eq_two K] at hprod
  omega

end FractionRingGalois

end QuadraticNumberFields
