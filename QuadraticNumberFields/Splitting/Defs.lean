/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Over
import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.NormalClosure
/-!
# Splitting Definitions and Trichotomy

This file defines the split/inert/ramified classification for prime ideals
in Dedekind extensions, and proves the trichotomy theorem for degree-2 extensions
(quadratic number fields).

## Main Definitions

* `Ideal.IsCompletelySplitIn`: General completely split behavior for a prime ideal.
* `Ideal.IsInertInGeneral`: General inert behavior for a prime ideal.
* `Ideal.IsRamifiedInGeneral`: General ramified behavior for a prime ideal.
* `Ideal.IsSplitIn`: Galois-global split behavior used in the quadratic trichotomy.
* `Ideal.IsInertIn`: Galois-global inert behavior used in the quadratic trichotomy.
* `Ideal.IsRamifiedIn`: Galois-global ramified behavior used in the quadratic trichotomy.

## Main Theorems

* `Ideal.isSplit_or_isInert_or_isRamified`: For a degree-2 extension, every prime
  falls into exactly one of the three categories.
-/

open Ideal

namespace Ideal

variable {R : Type*} [CommRing R]
variable (p : Ideal R) (S : Type*) [CommRing S] [Algebra R S]

local notation3 "g(" p ")" => (primesOver p S).ncard

section GeneralDefs

local notation3 "e(" p "," P ")" => ramificationIdx p P
local notation3 "f(" p "," P ")" => Ideal.inertiaDeg p P
local notation3 "τ(" p "," P ")" => (e(p, P), f(p, P), g(p))

/-- General completely split behavior: there is at least one prime above `p`, and every
prime above `p` has ramification index and inertia degree equal to `1`. -/
def IsCompletelySplitIn : Prop :=
  0 < g(p) ∧ ∀ P ∈ primesOver p S, e(p, P) = 1 ∧ f(p, P) = 1

/-- General inert behavior: there is a unique prime above `p`, and it is unramified. -/
def IsInertInGeneral : Prop :=
  g(p) = 1 ∧ ∀ P ∈ primesOver p S, e(p, P) = 1

/-- General ramified behavior: some prime above `p` has ramification index greater than `1`. -/
def IsRamifiedInGeneral : Prop :=
  ∃ P ∈ primesOver p S, 1 < e(p, P)

end GeneralDefs


section GalDefs

local notation3 "e(" p ")" => ramificationIdxIn p S
local notation3 "f(" p ")" => Ideal.inertiaDegIn p S
local notation3 "τ(" p ")" => (e(p), f(p), g(p))

/-- Galois-global split behavior used in the quadratic trichotomy. -/
def IsSplitIn : Prop :=
  e(p) = 1 ∧ f(p) = 1

/-- Galois-global inert behavior used in the quadratic trichotomy. -/
def IsInertIn : Prop :=
  g(p) = 1 ∧ e(p) = 1

/-- Galois-global ramified behavior used in the quadratic trichotomy. -/
def IsRamifiedIn : Prop :=
  1 < e(p)

lemma ramificationIdxIn_eq_of_mem (G : Type*) [Group G] [Finite G] [MulSemiringAction G S]
    [IsGaloisGroup G R S] {P : Ideal S} (hP : P ∈ primesOver p S) :
    e(p) = ramificationIdx p P := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  simpa using (Ideal.ramificationIdxIn_eq_ramificationIdx p P G)

lemma inertiaDegIn_eq_of_mem (G : Type*) [Group G] [Finite G] [MulSemiringAction G S]
    [IsGaloisGroup G R S] {P : Ideal S} (hP : P ∈ primesOver p S) :
    f(p) = Ideal.inertiaDeg p P := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  simpa using (Ideal.inertiaDegIn_eq_inertiaDeg p P G)

lemma finite_primesOver_of_nonempty (G : Type*) [Group G] [Finite G] [MulSemiringAction G S]
    [IsGaloisGroup G R S] (hne : ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver p) :
    Finite (primesOver p S) := by
  let P0 : primesOver p S := ⟨hne.choose, hne.choose_spec⟩
  let fG : G → primesOver p S := fun σ => σ • P0
  refine Finite.of_surjective fG ?_
  intro Q
  let : (P0 : Ideal S).IsPrime := P0.2.1
  let : (P0 : Ideal S).LiesOver p := P0.2.2
  let : (Q : Ideal S).IsPrime := Q.2.1
  let : (Q : Ideal S).LiesOver p := Q.2.2
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (p := p) (P := (P0 : Ideal S)) (Q := (Q : Ideal S)) (G := G)
  refine ⟨σ, Subtype.ext hσ⟩

lemma isRamifiedIn_iff_isRamifiedInGeneral (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] :
    IsRamifiedIn p S ↔ IsRamifiedInGeneral p S := by
  constructor
  · intro hpRam
    by_cases hne : ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver p
    · refine ⟨hne.choose, hne.choose_spec, ?_⟩
      have hP : hne.choose ∈ primesOver p S := hne.choose_spec
      rw [← ramificationIdxIn_eq_of_mem (p := p) (S := S) G hP]
      exact hpRam
    · simp [IsRamifiedIn, ramificationIdxIn, hne] at hpRam
  · rintro ⟨P, hP, hPgt⟩
    change 1 < e(p)
    rw [ramificationIdxIn_eq_of_mem (p := p) (S := S) G hP]
    exact hPgt

lemma isInertIn_iff_isInertInGeneral (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] :
    IsInertIn p S ↔ IsInertInGeneral p S := by
  constructor
  · rintro ⟨hg, he⟩
    refine ⟨hg, ?_⟩
    intro P hP
    rw [← ramificationIdxIn_eq_of_mem (p := p) (S := S) G hP]
    exact he
  · rintro ⟨hg, hgen⟩
    have hcard : (primesOver p S).ncard = 1 := by
      simpa using hg
    obtain ⟨P, hPset⟩ := Set.ncard_eq_one.mp hcard
    have hP : P ∈ primesOver p S := by simp [hPset]
    refine ⟨hg, ?_⟩
    rw [ramificationIdxIn_eq_of_mem (p := p) (S := S) G hP]
    exact hgen P hP

lemma isSplitIn_iff_isCompletelySplitIn (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] :
    IsSplitIn p S ↔ IsCompletelySplitIn p S := by
  constructor
  · rintro ⟨he, hf⟩
    have hne : ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver p := by
      by_contra h
      simp [ramificationIdxIn, h] at he
    let : Finite (primesOver p S) := finite_primesOver_of_nonempty (p := p) (S := S) G hne
    have hs : (primesOver p S).Finite := Set.toFinite _
    have hpos : 0 < (primesOver p S).ncard := by
      rw [Set.ncard_pos (hs := hs)]
      exact ⟨hne.choose, hne.choose_spec⟩
    refine ⟨hpos, ?_⟩
    intro P hP
    constructor
    · rw [← ramificationIdxIn_eq_of_mem (p := p) (S := S) G hP]
      exact he
    · rw [← inertiaDegIn_eq_of_mem (p := p) (S := S) G hP]
      exact hf
  · rintro ⟨hpos, hgen⟩
    have hs : (primesOver p S).Finite := Set.finite_of_ncard_pos hpos
    rw [Set.ncard_pos (hs := hs)] at hpos
    obtain ⟨P, hP⟩ := hpos
    refine ⟨?_, ?_⟩
    · rw [ramificationIdxIn_eq_of_mem (p := p) (S := S) G hP]
      exact (hgen P hP).1
    · rw [inertiaDegIn_eq_of_mem (p := p) (S := S) G hP]
      exact (hgen P hP).2


end GalDefs


section MissingMathlib
-- variable
/-! ## Fraction-field bridge lemma

This is a general bridge result that appears to be missing from mathlib.
-/

/-- If `S` is a quadratic extension of `R`, then the fraction field of `S` is a quadratic
extension of the fraction field of `R`. -/
theorem _root_.Algebra.IsQuadraticExtension.fractionRing
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra R K] [Algebra S L] [Algebra R L] [Algebra K L]
    [IsDomain R] [IsDomain S] [IsFractionRing R K] [IsFractionRing S L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsQuadraticExtension R S] :
    Algebra.IsQuadraticExtension K L := by
  letI : Algebra.IsAlgebraic R S := Algebra.IsAlgebraic.of_finite R S
  refine ⟨?_⟩
  calc
    Module.finrank K L = Module.finrank R S := by
      simpa using
        (Algebra.IsAlgebraic.finrank_of_isFractionRing (R := R) (R' := K) (S := S) (S' := L))
    _ = 2 := Algebra.IsQuadraticExtension.finrank_eq_two R S

/-- If `K` is a quadratic extension of a field `F` of characteristic not equal to `2`,
then `K/F` is separable. -/
theorem _root_.Algebra.IsQuadraticExtension.isSeparable_of_field_of_char_ne_two
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsQuadraticExtension F K]
    (hchar : ringChar F ≠ 2) : Algebra.IsSeparable F K := by
  rw [isSeparable_iff_finInsepDegree_eq_one] -- [Field F, Field K, Algebra F K]
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow (F := F) (E := K) (q := ringExpChar F)
  have hdiv : Field.finInsepDegree F K ∣ 2 := by
    refine ⟨Field.finSepDegree F K, ?_⟩
    rw [Nat.mul_comm, Field.finSepDegree_mul_finInsepDegree,
      Algebra.IsQuadraticExtension.finrank_eq_two F K]
  rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
  · exact h1
  · have hexp : ringExpChar F ≠ 2 := by
      rw [ringExpChar]
      intro h
      omega
    rw [hn] at h2
    cases n with
    | zero => simp at h2
    | succ n =>
        have hq_dvd : ringExpChar F ∣ 2 := by
          rw [pow_succ] at h2
          exact ⟨(ringExpChar F) ^ n, by simpa [Nat.mul_comm] using h2.symm⟩
        rcases (Nat.dvd_prime Nat.prime_two).1 hq_dvd with hq1 | hq2
        · simp [hq1] at h2
        · exact (hexp hq2).elim


end MissingMathlib


section Trichotomy

variable [IsDedekindDomain S]

local notation3 "e(" p ")" => ramificationIdxIn p S
local notation3 "f(" p ")" => Ideal.inertiaDegIn p S
local notation3 "τ(" p ")" => (e(p), f(p), g(p))

/-! ## Trichotomy for degree-2 extensions

For `[L : K] = 2`, `∑ eᵢfᵢ = 2` forces exactly three possibilities:
* `(e, f, g) = (1, 1, 2)` — split
* `(e, f, g) = (1, 2, 1)` — inert
* `(e, f, g) = (2, 1, 1)` — ramified
-/
-- Set L is List of ℕ , Σ A = p → ∀ a ∈ A, a = 1 or a = p
lemma eq_one_or_p_if_list_prod_eq_p {p : ℕ} (hp : Nat.Prime p) {L : List ℕ}
      (h : L.prod = p) : ∀ a ∈ L, a = 1 ∨ a = p := by
    intro a ha
    have hdiv : a ∣ p := by
      rw [← h]
      exact List.dvd_prod ha
    exact (Nat.dvd_prime hp).1 hdiv

theorem foo (a b c : ℕ) (h : a * b * c = 2) :
      (a = 2 ∧ b = 1 ∧ c = 1) ∨
      (a = 1 ∧ b = 1 ∧ c = 2) ∨
      (a = 1 ∧ b = 2 ∧ c = 1) := by
    have hL : [a, b, c].prod = 2 := by
      simpa [Nat.mul_assoc] using h
    have H := eq_one_or_p_if_list_prod_eq_p Nat.prime_two hL
    rcases H a (by simp) with (rfl | rfl)
    <;> rcases H b (by simp) with (rfl | rfl)
    <;> rcases H c (by simp) with (rfl | rfl)
    <;> simp_all

theorem efg_trichotomy [Nontrivial R] [IsDedekindDomain R] [Algebra.IsQuadraticExtension R S]
    -- [CharZero R] -- char≠ 2 is enough
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    (g(p) = 2 ∧ e(p) = 1 ∧ f(p) = 1) ∨
    (g(p) = 1 ∧ e(p) = 1 ∧ f(p) = 2) ∨
    (g(p) = 1 ∧ e(p) = 2 ∧ f(p) = 1) := by
  let K:=FractionRing R
  let L:=FractionRing S
  let := Ring.instAlgebraFractionRing
  let := IsIntegralClosure.MulSemiringAction R K L S
  have : Algebra.IsQuadraticExtension K L :=
    Algebra.IsQuadraticExtension.fractionRing (R := R) (S := S)
  -- have : Algebra.IsSeparable K L := sorry  add char≠2 to assumptions or 【[CharZero R] 】
  have : ringChar K ≠ 2 := by
    haveI : CharP K (ringChar R) :=
      IsFractionRing.charP_of_isFractionRing (R := R) (K := K) (ringChar R)
    simpa [ringChar.eq K (ringChar R)] using hchar
  have : Algebra.IsSeparable K L :=
    Algebra.IsQuadraticExtension.isSeparable_of_field_of_char_ne_two this
  have := IsGaloisGroup.of_isFractionRing Gal(L/K) R S K L
  have h_mul:= Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S Gal(L/K)
  have : Nat.card Gal(L/K) = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two K L]
    exact IsGaloisGroup.card_eq_finrank Gal(L/K) K L
  rw [this] at h_mul
  apply foo
  rw [mul_assoc]
  assumption

theorem isSplitIn_iff_efg [Nontrivial R] [IsDedekindDomain R]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    p.IsSplitIn S ↔ g(p) = 2 ∧ e(p) = 1 ∧ f(p) = 1 := by
  constructor
  · rintro ⟨he, hf⟩
    rcases efg_trichotomy p S hchar hp with ⟨hg, -, -⟩ | ⟨-, -, hf'⟩ | ⟨-, he', -⟩
    · exact ⟨hg, he, hf⟩
    all_goals omega
  · rintro ⟨-, he, hf⟩
    exact ⟨he, hf⟩

theorem isInertIn_iff_efg [Nontrivial R] [IsDedekindDomain R]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    p.IsInertIn S ↔ g(p) = 1 ∧ e(p) = 1 ∧ f(p) = 2 := by
  constructor
  · rintro ⟨hg, he⟩
    rcases efg_trichotomy p S hchar hp with ⟨hg', -, -⟩ | ⟨-, -, hf⟩ | ⟨-, he', -⟩
    · omega
    · exact ⟨hg, he, hf⟩
    · omega
  · rintro ⟨hg, he, -⟩
    exact ⟨hg, he⟩

theorem isRamifiedIn_iff_efg [Nontrivial R] [IsDedekindDomain R]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    p.IsRamifiedIn S ↔ g(p) = 1 ∧ e(p) = 2 ∧ f(p) = 1 := by
  constructor
  · intro hram
    rcases efg_trichotomy p S hchar hp with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hg, he, hf⟩
    · exact absurd he (by unfold IsRamifiedIn at hram; omega)
    · exact absurd he (by unfold IsRamifiedIn at hram; omega)
    · exact ⟨hg, he, hf⟩
  · rintro ⟨-, he, -⟩
    change 1 < e(p)
    omega

/-- For a degree-2 extension of Dedekind domains with `ringChar R ≠ 2`, every nonzero
prime ideal is split, inert, or ramified. -/
theorem isSplit_or_isInert_or_isRamified [Nontrivial R] [IsDedekindDomain R]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    p.IsSplitIn S ∨ p.IsInertIn S ∨ p.IsRamifiedIn S := by
  rcases efg_trichotomy p S hchar hp with h | h | h
  · exact Or.inl ((isSplitIn_iff_efg p S hchar hp).mpr h)
  · exact Or.inr (Or.inl ((isInertIn_iff_efg p S hchar hp).mpr h))
  · exact Or.inr (Or.inr ((isRamifiedIn_iff_efg p S hchar hp).mpr h))

end Trichotomy

end Ideal
