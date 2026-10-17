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

section SemanticCharacterisation

variable {R : Type*} [CommRing R]
variable (p : Ideal R) (S : Type*) [CommRing S] [Algebra R S]
variable [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
variable [Algebra.IsQuadraticExtension R S]

local notation3 "e(" p ")" => ramificationIdxIn p S
local notation3 "P(" p ")" => primesOver p S
local notation3 "mapP(" p ")" => Ideal.map (algebraMap R S) p

/-- Bridge from per-prime `ramificationIdx` to the Galois-uniform
`ramificationIdxIn` for a quadratic extension, using
`Algebra.IsQuadraticExtension.isGaloisGroup`. -/
private theorem ramificationIdx_eq_ramificationIdxIn
    (hchar : ringChar R ≠ 2)
    {P' : Ideal S} (hP' : P' ∈ P(p)) :
    P'.ramificationIdx R = e(p) := by
  letI := Ring.instAlgebraFractionRing
  letI := IsIntegralClosure.MulSemiringAction R (FractionRing R) (FractionRing S) S
  letI := Algebra.IsQuadraticExtension.isGaloisGroup (R := R) (S := S) hchar
  exact (ramificationIdxIn_eq_of_mem p S
    Gal(FractionRing S / FractionRing R) hP').symm

/-- Bridge from per-prime `inertiaDeg` to the Galois-uniform `inertiaDegIn`
for a quadratic extension, using `Algebra.IsQuadraticExtension.isGaloisGroup`. -/
private theorem inertiaDeg_eq_inertiaDegIn
    (hchar : ringChar R ≠ 2)
    {P' : Ideal S} (hP' : P' ∈ P(p)) :
    P'.inertiaDeg R = inertiaDegIn p S := by
  letI := Ring.instAlgebraFractionRing
  letI := IsIntegralClosure.MulSemiringAction R (FractionRing R) (FractionRing S) S
  letI := Algebra.IsQuadraticExtension.isGaloisGroup (R := R) (S := S) hchar
  exact (inertiaDegIn_eq_of_mem p S
    Gal(FractionRing S / FractionRing R) hP').symm

/-- In a split quadratic Dedekind extension, every prime above `p` has inertia
degree `1`. -/
theorem inertiaDeg_eq_one_of_isSplitIn
    (hchar : ringChar R ≠ 2)
    {P' : Ideal S} [P'.IsPrime] [P'.LiesOver p]
    (hs : IsSplitIn p S) :
    P'.inertiaDeg R = 1 := by
  have hP' : P' ∈ P(p) := ⟨inferInstance, inferInstance⟩
  rw [inertiaDeg_eq_inertiaDegIn p S hchar hP']
  exact hs.2

variable [p.IsMaximal]

/-- The factorisation `map p = ∏ P ^ e(P)` specialised via Galois uniformity:
every exponent equals `ramificationIdxIn p S`. -/
private theorem map_eq_prod_pow_ramificationIdxIn
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) :
    mapP(p) = ∏ P' ∈ P(p).toFinset, P' ^ e(p) := by
  have hfact := Ideal.map_algebraMap_eq_finsetProd_pow (R := S) (S := R)
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
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
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
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    (hs : IsSplitIn p S) :
    ∃ P₁ ∈ P(p), ∃ P₂ ∈ P(p), P₁ ≠ P₂ ∧ mapP(p) = P₁ * P₂ :=
  map_eq_of_ramificationIdxIn_eq_one_of_inertiaDegIn_eq_one p S hchar hp hs

/-- In a degree-2 Dedekind extension, the numerical inert condition
`g = 1 ∧ e = 1` means the lifted ideal is itself prime. -/
theorem map_isPrime_of_ncard_primesOver_eq_one_of_ramificationIdxIn_eq_one
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
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
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    (hi : IsInertIn p S) :
    mapP(p).IsPrime :=
  map_isPrime_of_ncard_primesOver_eq_one_of_ramificationIdxIn_eq_one p S hchar hp hi

/-- If `P` lies above an inert prime `p`, then extending `p` to `S` recovers
`P`. -/
theorem map_eq_of_isInertIn_of_mem_primesOver
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    {P' : Ideal S} (hP' : P' ∈ P(p))
    (hi : IsInertIn p S) :
    mapP(p) = P' := by
  letI : P'.LiesOver p := hP'.2
  have hQprime : mapP(p).IsPrime :=
    map_isPrime_of_isInertIn p S hchar hp hi
  have hQle : mapP(p) ≤ P' := by
    rw [Ideal.map_le_iff_le_comap, Ideal.LiesOver.over (p := p) (P := P')]
  have hQbot : mapP(p) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp
  exact (hQprime.isMaximal hQbot).eq_of_le hP'.1.ne_top hQle

/-- If `P` lies above an inert principal prime `p`, then `P` is principal. -/
theorem isPrincipal_of_isInertIn_of_mem_primesOver_of_isPrincipal
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    (hp_principal : p.IsPrincipal)
    {P' : Ideal S} (hP' : P' ∈ P(p))
    (hi : IsInertIn p S) :
    P'.IsPrincipal := by
  have hmap : mapP(p) = P' :=
    map_eq_of_isInertIn_of_mem_primesOver p S hchar hp hP' hi
  rcases hp_principal with ⟨x, hx⟩
  rw [← hmap, hx, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

/-- In an inert quadratic Dedekind extension, the unique prime above `p` has
inertia degree `2`. -/
theorem inertiaDeg_eq_two_of_isInertIn
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    {P' : Ideal S} [P'.IsPrime] [P'.LiesOver p]
    (hi : IsInertIn p S) :
    P'.inertiaDeg R = 2 := by
  have hP' : P' ∈ P(p) := ⟨inferInstance, inferInstance⟩
  rw [inertiaDeg_eq_inertiaDegIn p S hchar hP']
  exact ((ncard_primesOver_eq_one_and_ramificationIdxIn_eq_one_iff_efg p S hchar hp).mp hi).2.2

/-- In a ramified quadratic Dedekind extension, the unique prime above `p` has
inertia degree `1`. -/
theorem inertiaDeg_eq_one_of_isRamifiedIn
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    {P' : Ideal S} [P'.IsPrime] [P'.LiesOver p]
    (hr : IsRamifiedIn p S) :
    P'.inertiaDeg R = 1 := by
  have hP' : P' ∈ P(p) := ⟨inferInstance, inferInstance⟩
  rw [inertiaDeg_eq_inertiaDegIn p S hchar hP']
  exact ((one_lt_ramificationIdxIn_iff_efg p S hchar hp).mp hr).2.2

/-- In a degree-2 Dedekind extension, the numerical ramified condition
`1 < e` means the lifted ideal is the square of a prime: `map p = P²`. -/
theorem map_eq_sq_of_one_lt_ramificationIdxIn
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
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
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    (hr : IsRamifiedIn p S) :
    ∃ P' ∈ P(p), mapP(p) = P' ^ 2 :=
  map_eq_sq_of_one_lt_ramificationIdxIn p S hchar hp hr

/-- In a quadratic Dedekind extension, a ramified prime has a singleton fiber
above it. -/
theorem exists_primesOver_eq_singleton_of_isRamifiedIn
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    (hr : IsRamifiedIn p S) :
    ∃ P : Ideal S, P(p) = {P} := by
  have hg : P(p).ncard = 1 :=
    ((one_lt_ramificationIdxIn_iff_efg p S hchar hp).mp hr).1
  rw [Set.ncard_eq_one] at hg
  exact hg

/-- In a quadratic Dedekind extension, a ramified prime has a unique prime above it. -/
theorem primesOver_eq_singleton_of_isRamifiedIn
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    {P' : Ideal S} (hP' : P' ∈ P(p))
    (hr : IsRamifiedIn p S) :
    P(p) = {P'} := by
  obtain ⟨Q, hQ⟩ :=
    exists_primesOver_eq_singleton_of_isRamifiedIn p S hchar hp hr
  have hP'Q : P' = Q := by
    rw [hQ] at hP'
    exact hP'
  simpa [hP'Q] using hQ

/-- In a quadratic Dedekind extension, a ramified factorization can be targeted
at any chosen prime above the ramified base prime. -/
theorem map_eq_sq_of_isRamifiedIn_of_mem_primesOver
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    {P' : Ideal S} (hP' : P' ∈ P(p))
    (hr : IsRamifiedIn p S) :
    mapP(p) = P' ^ 2 := by
  obtain ⟨Q, hQ, hmap⟩ := map_eq_sq_of_isRamifiedIn p S hchar hp hr
  have hsingleton : P(p) = {P'} :=
    primesOver_eq_singleton_of_isRamifiedIn p S hchar hp hP' hr
  have hQP' : Q = P' := by
    have hQmem : Q ∈ ({P'} : Set (Ideal S)) := by
      simpa [hsingleton] using hQ
    simpa using hQmem
  simpa [hQP'] using hmap

/-- A split prime in a quadratic Dedekind extension has exactly two prime ideals
above it. -/
theorem primesOver_ncard_eq_two_of_isSplitIn
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    (hsplit : IsSplitIn p S) :
    P(p).ncard = 2 :=
  ((ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg p S hchar hp).mp
    hsplit).1

/-- A finite set with cardinality two and two distinct known elements is exactly
the pair of those elements. -/
private theorem set_eq_pair_of_ncard_eq_two_of_mem_of_mem_of_ne
    {α : Type*} {s : Set α} {a b : α}
    (hs : s.ncard = 2) (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) :
    s = {a, b} := by
  have hpair : ({a, b} : Set α).ncard = 2 := Set.ncard_pair hne
  have hsfinite : s.Finite := by
    rw [Set.ncard_eq_two] at hs
    obtain ⟨x, y, _hxy, rfl⟩ := hs
    simp
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ hsfinite).symm
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · simp [hs, hpair]

/-- If `P` and `Q` are the two distinct primes above a split prime, then
extending the base prime gives `P * Q`. -/
theorem map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥)
    {P' Q' : Ideal S} (hP' : P' ∈ P(p)) (hQ' : Q' ∈ P(p))
    (hne : P' ≠ Q') (hsplit : IsSplitIn p S) :
    mapP(p) = P' * Q' := by
  have hfiber : P(p) = {P', Q'} :=
    set_eq_pair_of_ncard_eq_two_of_mem_of_mem_of_ne
      (primesOver_ncard_eq_two_of_isSplitIn p S hchar hp hsplit) hP' hQ' hne
  obtain ⟨P₁, hP₁, P₂, hP₂, hPne, hmap⟩ :=
    map_eq_of_isSplitIn p S hchar hp hsplit
  have hP₁' : P₁ = P' ∨ P₁ = Q' := by
    have hmem : P₁ ∈ ({P', Q'} : Set (Ideal S)) := by
      simpa [hfiber] using hP₁
    simpa using hmem
  have hP₂' : P₂ = P' ∨ P₂ = Q' := by
    have hmem : P₂ ∈ ({P', Q'} : Set (Ideal S)) := by
      simpa [hfiber] using hP₂
    simpa using hmem
  rcases hP₁' with rfl | rfl <;> rcases hP₂' with rfl | rfl
  · exact False.elim (hPne rfl)
  · exact hmap
  · simpa [mul_comm] using hmap
  · exact False.elim (hPne rfl)

end SemanticCharacterisation

end Ideal
