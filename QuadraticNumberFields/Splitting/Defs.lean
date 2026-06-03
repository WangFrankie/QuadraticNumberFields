/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Over
import Mathlib.Data.Fintype.EquivFin
import Mathlib.NumberTheory.NumberField.Basic
import QuadraticNumberFields.Mathlib.NumberTheory.RamificationInertia.Galois
/-!
# Splitting Definitions and Trichotomy

This file states the split/inert/ramified classification for prime ideals in
Dedekind extensions using mathlib's ramification API, and proves the trichotomy
theorem for degree-2 extensions (quadratic number fields).

## Implementation notes

The predicates `IsSplitIn`/`IsInertIn`/`IsRamifiedIn` are numerical wrappers
around mathlib's `primesOver`, `ramificationIdxIn`, and `inertiaDegIn` API.
Ideal-factorization characterisations live in `Splitting.Factorization`.

## Main Theorems

* `Ideal.split_or_inert_or_ramified`: For a degree-2 extension, every prime falls
  into exactly one of the three categories, stated in terms of `(e, f, g)`.
-/

open Ideal

namespace Ideal

variable {R : Type*} [CommRing R]
variable (p : Ideal R) (S : Type*) [CommRing S] [Algebra R S]

/-- The ideal `p` splits in `S` in the numerical ramification-inertia sense:
uniform ramification index and inertia degree are both one. -/
def IsSplitIn : Prop :=
  ramificationIdxIn p S = 1 ∧ inertiaDegIn p S = 1

/-- The ideal `p` is inert in `S` in the numerical ramification-inertia sense:
there is one prime above `p`, and the ramification index is one. -/
def IsInertIn : Prop :=
  (primesOver p S).ncard = 1 ∧ ramificationIdxIn p S = 1

/-- The ideal `p` ramifies in `S` in the numerical ramification-inertia sense:
the uniform ramification index is greater than one. -/
def IsRamifiedIn : Prop :=
  1 < ramificationIdxIn p S

local notation3 "g(" p ")" => (primesOver p S).ncard

section GalDefs

local notation3 "e(" p ")" => ramificationIdxIn p S
local notation3 "f(" p ")" => Ideal.inertiaDegIn p S
local notation3 "τ(" p ")" => (e(p), f(p), g(p))

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

/-- In a Galois extension, the uniform ramification index is greater than `1`
exactly when some prime over `p` has ramification index greater than `1`. -/
lemma ramificationIdxIn_gt_one_iff_exists_ramificationIdx_gt_one
    (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] :
    1 < ramificationIdxIn p S ↔ ∃ P ∈ primesOver p S, 1 < ramificationIdx p P := by
  constructor
  · intro hpRam
    by_cases hne : ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver p
    · refine ⟨hne.choose, hne.choose_spec, ?_⟩
      have hP : hne.choose ∈ primesOver p S := hne.choose_spec
      rw [← ramificationIdxIn_eq_of_mem (p := p) (S := S) G hP]
      exact hpRam
    · simp [ramificationIdxIn, hne] at hpRam
  · rintro ⟨P, hP, hPgt⟩
    rw [ramificationIdxIn_eq_of_mem (p := p) (S := S) G hP]
    exact hPgt


end GalDefs


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

/-- In a quadratic extension, the mathlib numerical split condition
`e = 1 ∧ f = 1` is equivalent to the `(g, e, f) = (2, 1, 1)` case. -/
theorem ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg
    [Nontrivial R] [IsDedekindDomain R]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    e(p) = 1 ∧ f(p) = 1 ↔ g(p) = 2 ∧ e(p) = 1 ∧ f(p) = 1 := by
  constructor
  · rintro ⟨he, hf⟩
    rcases efg_trichotomy p S hchar hp with ⟨hg, -, -⟩ | ⟨-, -, hf'⟩ | ⟨-, he', -⟩
    · exact ⟨hg, he, hf⟩
    all_goals omega
  · rintro ⟨-, he, hf⟩
    exact ⟨he, hf⟩

/-- In a quadratic extension, the mathlib numerical inert condition
`g = 1 ∧ e = 1` is equivalent to the `(g, e, f) = (1, 1, 2)` case. -/
theorem ncard_primesOver_eq_one_and_ramificationIdxIn_eq_one_iff_efg
    [Nontrivial R] [IsDedekindDomain R]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    g(p) = 1 ∧ e(p) = 1 ↔ g(p) = 1 ∧ e(p) = 1 ∧ f(p) = 2 := by
  constructor
  · rintro ⟨hg, he⟩
    rcases efg_trichotomy p S hchar hp with ⟨hg', -, -⟩ | ⟨-, -, hf⟩ | ⟨-, he', -⟩
    · omega
    · exact ⟨hg, he, hf⟩
    · omega
  · rintro ⟨hg, he, -⟩
    exact ⟨hg, he⟩

/-- In a quadratic extension, the mathlib numerical ramification condition
`1 < e` is equivalent to the `(g, e, f) = (1, 2, 1)` case. -/
theorem one_lt_ramificationIdxIn_iff_efg [Nontrivial R] [IsDedekindDomain R]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    1 < e(p) ↔ g(p) = 1 ∧ e(p) = 2 ∧ f(p) = 1 := by
  constructor
  · intro hram
    rcases efg_trichotomy p S hchar hp with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hg, he, hf⟩
    · omega
    · omega
    · exact ⟨hg, he, hf⟩
  · rintro ⟨-, he, -⟩
    omega

/-- For a degree-2 extension of Dedekind domains with `ringChar R ≠ 2`, every nonzero
prime ideal is split, inert, or ramified. -/
theorem split_or_inert_or_ramified [Nontrivial R] [IsDedekindDomain R]
    [Algebra.IsQuadraticExtension R S]
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    IsSplitIn p S ∨ IsInertIn p S ∨ IsRamifiedIn p S := by
  rcases efg_trichotomy p S hchar hp with h | h | h
  · exact Or.inl ((ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg
      p S hchar hp).mpr h)
  · exact Or.inr (Or.inl
      ((ncard_primesOver_eq_one_and_ramificationIdxIn_eq_one_iff_efg
        p S hchar hp).mpr h))
  · exact Or.inr (Or.inr ((one_lt_ramificationIdxIn_iff_efg p S hchar hp).mpr h))

end Trichotomy

end Ideal
