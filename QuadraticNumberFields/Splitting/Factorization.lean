/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Defs
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Ideal-Factorization Characterisation of Splitting

This file translates the numerical `(e, f, g)` trichotomy proved in
`QuadraticNumberFields.Splitting.Defs` into the classical ideal-factorization
language for a degree-2 Dedekind extension `R → S`:

* split:    `map p = P₁ · P₂` with `P₁ ≠ P₂` two primes above `p`;
* inert:    `map p` is itself prime;
* ramified: `map p = P²` for a single prime `P` above `p`.

The key technical step is `map_eq_prod_pow_ramificationIdxIn`, which specialises
the Dedekind factorisation `map p = ∏ P ^ e(P)` using Galois uniformity (every
exponent equals `ramificationIdxIn p S`), via
`Algebra.IsQuadraticExtension.isGaloisGroup`.

## Main results

* `Ideal.map_eq_of_ramificationIdxIn_eq_one_of_inertiaDegIn_eq_one`
* `Ideal.map_eq_of_isSplitIn`
* `Ideal.map_isPrime_of_ncard_primesOver_eq_one_of_ramificationIdxIn_eq_one`
* `Ideal.map_isPrime_of_isInertIn`
* `Ideal.map_eq_sq_of_one_lt_ramificationIdxIn`
* `Ideal.map_eq_sq_of_isRamifiedIn`
-/

open Ideal

namespace Ideal

variable {R : Type*} [CommRing R]
variable (p : Ideal R) (S : Type*) [CommRing S] [Algebra R S]

section SemanticCharacterisation

local notation3 "e(" p ")" => ramificationIdxIn p S
local notation3 "P(" p ")" => primesOver p S
local notation3 "mapP(" p ")" => Ideal.map (algebraMap R S) p

/-- Bridge from per-prime `ramificationIdx` to the Galois-uniform
`ramificationIdxIn` for a quadratic extension, using
`Algebra.IsQuadraticExtension.isGaloisGroup`. -/
private theorem ramificationIdx_eq_ramificationIdxIn
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) [p.IsMaximal]
    {P' : Ideal S} (hP' : P' ∈ P(p)) :
    ramificationIdx p P' = e(p) := by
  letI := Ring.instAlgebraFractionRing
  letI := IsIntegralClosure.MulSemiringAction R (FractionRing R) (FractionRing S) S
  letI := Algebra.IsQuadraticExtension.isGaloisGroup (R := R) (S := S) hchar
  exact (ramificationIdxIn_eq_of_mem p S
    Gal(FractionRing S / FractionRing R) hP').symm

/-- The factorisation `map p = ∏ P ^ e(P)` specialised via Galois uniformity:
every exponent equals `ramificationIdxIn p S`. -/
private theorem map_eq_prod_pow_ramificationIdxIn
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    mapP(p) = ∏ P' ∈ P(p).toFinset, P' ^ e(p) := by
  have hfact := Ideal.map_algebraMap_eq_finset_prod_pow (R := S) (S := R)
    (Ne.bot_lt hp).ne'
  rw [hfact]
  apply Finset.prod_congr rfl
  intro P' hP'
  congr 1
  rw [Set.mem_toFinset] at hP'
  exact ramificationIdx_eq_ramificationIdxIn p S hchar hP'

/-- In a degree-2 Dedekind extension, the numerical split condition
`e = 1 ∧ f = 1` means the ideal factors as a product of two distinct primes:
`map p = P₁ · P₂`. -/
theorem map_eq_of_ramificationIdxIn_eq_one_of_inertiaDegIn_eq_one
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    (hs : e(p) = 1 ∧ inertiaDegIn p S = 1) :
    ∃ P₁ ∈ P(p), ∃ P₂ ∈ P(p), P₁ ≠ P₂ ∧ mapP(p) = P₁ * P₂ := by
  classical
  obtain ⟨_, he, _⟩ :=
    (ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg p S hchar hp).mp hs
  rw [Set.ncard_eq_two] at *
  obtain ⟨P₁, P₂, hne, hset⟩ := ‹∃ _, _›
  have hP1 : P₁ ∈ P(p) := by rw [hset]; exact Set.mem_insert _ _
  have hP2 : P₂ ∈ P(p) := by
    rw [hset]; exact Set.mem_insert_of_mem _ rfl
  refine ⟨P₁, hP1, P₂, hP2, hne, ?_⟩
  have hfact := map_eq_prod_pow_ramificationIdxIn p S hchar hp
  have hfin : P(p).toFinset = {P₁, P₂} := by
    ext Q
    simp [hset, Finset.mem_insert, Finset.mem_singleton]
  rw [hfin, he] at hfact
  simp only [pow_one] at hfact
  rwa [Finset.prod_pair hne] at hfact

/-- In a degree-2 Dedekind extension, `IsSplitIn p S` gives the classical split
factorization `map p = P₁ * P₂` with two distinct primes above `p`. -/
theorem map_eq_of_isSplitIn
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    (hs : IsSplitIn p S) :
    ∃ P₁ ∈ P(p), ∃ P₂ ∈ P(p), P₁ ≠ P₂ ∧ mapP(p) = P₁ * P₂ :=
  map_eq_of_ramificationIdxIn_eq_one_of_inertiaDegIn_eq_one p S hchar hp hs

/-- In a degree-2 Dedekind extension, the numerical inert condition
`g = 1 ∧ e = 1` means the lifted ideal is itself prime. -/
theorem map_isPrime_of_ncard_primesOver_eq_one_of_ramificationIdxIn_eq_one
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    (hi : P(p).ncard = 1 ∧ e(p) = 1) :
    mapP(p).IsPrime := by
  obtain ⟨hg, he⟩ := hi
  rw [Set.ncard_eq_one] at hg
  obtain ⟨P, hPset⟩ := hg
  have hfact := map_eq_prod_pow_ramificationIdxIn p S hchar hp
  have hfin : P(p).toFinset = {P} := by
    ext Q
    simp [hPset]
  rw [hfin, he] at hfact
  simp only [pow_one, Finset.prod_singleton] at hfact
  rw [hfact]
  exact (hPset ▸ Set.mem_singleton P : P ∈ P(p)).1

/-- In a degree-2 Dedekind extension, `IsInertIn p S` says the lifted ideal is
itself prime. -/
theorem map_isPrime_of_isInertIn
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    (hi : IsInertIn p S) :
    mapP(p).IsPrime :=
  map_isPrime_of_ncard_primesOver_eq_one_of_ramificationIdxIn_eq_one p S hchar hp hi

/-- In a degree-2 Dedekind extension, the numerical ramified condition
`1 < e` means the lifted ideal is the square of a prime: `map p = P²`. -/
theorem map_eq_sq_of_one_lt_ramificationIdxIn
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    (hr : 1 < e(p)) :
    ∃ P' ∈ P(p), mapP(p) = P' ^ 2 := by
  obtain ⟨hg, he, _⟩ := (one_lt_ramificationIdxIn_iff_efg p S hchar hp).mp hr
  rw [Set.ncard_eq_one] at hg
  obtain ⟨P, hPset⟩ := hg
  refine ⟨P, hPset ▸ Set.mem_singleton P, ?_⟩
  have hfact := map_eq_prod_pow_ramificationIdxIn p S hchar hp
  have hfin : P(p).toFinset = {P} := by
    ext Q
    simp [hPset]
  rw [hfin, he] at hfact
  simpa using hfact

/-- In a degree-2 Dedekind extension, `IsRamifiedIn p S` gives the classical
ramified factorization `map p = P ^ 2` for the unique prime above `p`. -/
theorem map_eq_sq_of_isRamifiedIn
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    (hr : IsRamifiedIn p S) :
    ∃ P' ∈ P(p), mapP(p) = P' ^ 2 :=
  map_eq_sq_of_one_lt_ramificationIdxIn p S hchar hp hr

end SemanticCharacterisation

end Ideal
