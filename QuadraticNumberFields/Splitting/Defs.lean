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

-- theorem efg_trichotomy'' [Algebra.IsSeparable K L]
--     [Algebra.IsQuadraticExtension K L]
--     (hp : p ≠ ⊥) :
--     (g(p) = 2 ∧ e(p) = 1 ∧ f(p) = 1) ∨
--     (g(p) = 1 ∧ e(p) = 1 ∧ f(p) = 2) ∨
--     (g(p) = 1 ∧ e(p) = 2 ∧ f(p) = 1) := by
--   let := IsIntegralClosure.MulSemiringAction R K L S
--   have := IsGaloisGroup.of_isFractionRing Gal(L/K) R S K L
--   have h_mul:= Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S Gal(L/K)
--   have : Nat.card Gal(L/K) = 2 := by
--     rw [← Algebra.IsQuadraticExtension.finrank_eq_two K L]
--     exact IsGaloisGroup.card_eq_finrank Gal(L/K) K L
--   rw [this] at h_mul
--   apply foo
--   rw [mul_assoc]
--   assumption


-- -- TODO delete or
-- theorem IsSplitIn.not_isInert :
--      p.IsSplitIn S → ¬ p.IsInertIn S :=
--     fun hs hi => Nat.lt_irrefl 1 (hi.1 ▸ hs.1)

-- private theorem not_isRamifiedIn_of_forall_eq_one
--       (h : ∀ P ∈ primesOverFinset p S, e(P) = 1) :
--       ¬ p.IsRamifiedIn S :=
--     fun ⟨P, hP, hlt⟩ => by simp [h P hP] at hlt

-- theorem IsSplitIn.not_isRamified :
--      p.IsSplitIn S → ¬ p.IsRamifiedIn S :=
--     fun hs => not_isRamifiedIn_of_forall_eq_one p S hs.2

-- theorem IsInertIn.not_isRamified :
--      p.IsInertIn S → ¬ p.IsRamifiedIn S :=
--     fun hi => not_isRamifiedIn_of_forall_eq_one p S hi.2

-- /-! ## Helper lemmas for trichotomy

-- Three mutually exclusive cases from `∑ eᵢfᵢ = [L:K] = 2`:
-- - `(e, f, g) = (1, 1, 2)` — split
-- - `(e, f, g) = (1, 2, 1)` — inert
-- - `(e, f, g) = (2, 1, 1)` — ramified
-- -/



-- variable [IsDedekindDomain R]



-- variable (K L : Type*) [Field K] [Field L]
--     [Algebra R K] [IsFractionRing R K]
--     [Algebra S L] [IsFractionRing S L]
--     [Algebra K L] [Algebra R L]
--     [IsScalarTower R S L] [IsScalarTower R K L]
--     [Module.IsTorsionFree R S] [p.IsMaximal]

-- lemma e_ge_one (hp : p ≠ ⊥) :
--     ∀ P ∈ primesOverFinset p S, 1 ≤ e(P) := by
--   intro P hP
--   rw [mem_primesOverFinset_iff hp] at hP
--   letI : P.IsPrime := hP.1
--   letI : P.LiesOver p := hP.2
--   exact Nat.one_le_iff_ne_zero.mpr
--     (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp)

-- variable [Module.Finite R S]

-- lemma f_ge_one (hp : p ≠ ⊥) :
--   ∀ P ∈ primesOverFinset p S, 1 ≤ f(P) := by
--     intro P hP
--     refine Nat.one_le_iff_ne_zero.mpr ?_
--     rw [mem_primesOverFinset_iff hp] at hP
--     have : P.LiesOver p := hP.2
--     apply Ideal.inertiaDeg_ne_zero

-- lemma g_ge_one (hp : p ≠ ⊥) :
--       1 ≤ g := by
--     have := one_le_primesOver_ncard p S
--     rw [← coe_primesOverFinset hp S, Set.ncard_coe_finset] at this
--     exact this

-- -- `sum_ramification_inertia`
-- theorem isSplit_or_isInert_or_isRamified
--     (hp : p ≠ ⊥)
--     (h_deg : Module.finrank K L = 2) :
--   p.IsSplitIn S ∨ p.IsInertIn S ∨ p.IsRamifiedIn S := by
--   -- Apply the sum formula: ∑ e_i * f_i = [L:K] = 2
--   classical
--   have h_sum := Ideal.sum_ramification_inertia S K L hp
--   rw [h_deg] at h_sum
--   have hmul_ge_one : ∀ P ∈ primesOverFinset p S, 1 ≤ e(P) * f(P) :=
--     fun P hP => Right.one_le_mul (e_ge_one _ _ hp P hP) (f_ge_one p S hp P hP)
--   have hcard_le_sum :
--     g ≤ ∑ P ∈ primesOverFinset p S, e(P) * f(P) := by
--     rw [Finset.card_eq_sum_ones]
--     exact Finset.sum_le_sum (fun P hP => hmul_ge_one P hP)
--   have hg_le_two : g ≤ 2 := by omega
--   -- Case analysis on g
--   by_cases hg : g = 2
--   · -- Case g = 2: split
--     left
--     refine ⟨by omega, ?_⟩
--     by_contra h
--     push_neg at h
--     obtain ⟨P, hP, heP⟩ := h
--     have htwoP : 2 ≤ e(P) := by
--       have := e_ge_one p S hp P hP
--       omega
--     have : 1 ≤ ∑ Q ∈ (primesOverFinset p S).erase P, e(Q) * f(Q) := by
--       have hterm :
--           ∀ Q ∈ (primesOverFinset p S).erase P, 1 ≤ e(Q) * f(Q) :=
--           fun Q hQ => hmul_ge_one Q (Finset.mem_of_mem_erase hQ)
--       have : 1 = ((primesOverFinset p S).erase P).card := by
--         rw [Finset.card_erase_of_mem hP]
--         omega
--       rw [this, Finset.card_eq_sum_ones]
--       exact Finset.sum_le_sum (fun P hP => hterm P hP)
--     have hsum_ge_three : 3 ≤ ∑ P ∈ primesOverFinset p S, e(P) * f(P) := by
--       rw [(Finset.add_sum_erase _ _ hP).symm]
--       have : 1 ≤ f(P) := f_ge_one p S hp P hP
--       have : 2 ≤ e(P) * f(P) := by
--         calc
--           2 ≤ e(P) * 1 := by omega
--           _ ≤ e(P) * f(P) := Nat.mul_le_mul_left _ this
--       omega
--     omega
--   · -- g ≠ 2, so g = 1
--     have hg1 : g = 1 := by
--       have : 1 ≤ g := by exact g_ge_one p S hp
--       omega
--     right
--     by_cases hi : ∀ P ∈ primesOverFinset p S, e(P) = 1
--     · -- Case g = 1 and e(P) = 1: inert
--       left
--       exact ⟨hg1, hi⟩
--     · -- Case g = 1 and ∃ P, e(P) ≠ 1: ramified
--       right
--       push_neg at hi
--       obtain ⟨P, hP, _⟩ := hi
--       refine ⟨P, hP, ?_⟩
--       have h1 : 1 ≤ e(P) := e_ge_one p S hp P hP
--       omega

-- --TODO using this to simplify efg_trichotomy and efg_trichotomy' by showing g=1 or g=2 first
-- lemma g_eq_two_or_eq_one (hp : p ≠ ⊥) (h_deg : Module.finrank K L = 2) :
--     g = 2 ∨ g = 1 := by
--   have := g_ge_one p S hp
--   have := Ideal.sum_ramification_inertia S K L hp
--   rw [h_deg] at this
--   have hmul_ge_one : ∀ P ∈ primesOverFinset p S, 1 ≤ e(P) * f(P) :=
--     fun P hP => Right.one_le_mul (e_ge_one p S hp P hP) (f_ge_one p S hp P hP)
--   have hg_le : g ≤ 2 := by
--     rw [← this, Finset.card_eq_sum_ones]
--     exact Finset.sum_le_sum (fun P hP => hmul_ge_one P hP)
--   omega

-- --TODO `e_eq_two_or_eq_one`
-- lemma e_eq_two_or_eq_one {P} (hp : p ≠ ⊥) (h_deg : Module.finrank K L = 2)
--     (hP : P ∈ primesOverFinset p S) :
--     e(P) = 2 ∨ e(P) = 1 := by
--   have := e_ge_one p S hp P hP
--   sorry

-- -- variable [Module.IsTorsionFree K L]
-- --TODO `f_eq_two_or_eq_one`
-- lemma f_eq_two_or_eq_one {P} (hp : p ≠ ⊥) (h_deg : Module.finrank K L = 2)[Finite (Gal(L/K))]
--     (hP : P ∈ primesOverFinset p S)[Algebra.IsAlgebraic K L] [IsGalois K L]:
--     f(P) = 2 ∨ f(P) = 1 := by
--   have := f_ge_one p S hp P hP
--   let := IsIntegralClosure.MulSemiringAction R K L S
--   have := IsGaloisGroup.of_isFractionRing Gal(L/K) R S K L
--   have h_mul:= Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (A:=R) (B:=S) hp Gal(L/K)
--   rw [← coe_primesOverFinset hp S,Set.ncard_coe_finset] at h_mul







-- /-- In a degree-2 extension, the triple `(g, e(P), f(P))` is one of
--       `(2, 1, 1)` (split), `(1, 1, 2)` (inert), or `(1, 2, 1)` (ramified). -/
-- theorem efg_trichotomy {P}
--     (hp : p ≠ ⊥) (h_deg : Module.finrank K L = 2) (hP : P ∈ primesOverFinset p S) :
--     (g = 2 ∧ e(P) = 1 ∧ f(P) = 1) ∨
--     (g = 1 ∧ e(P) = 1 ∧ f(P) = 2) ∨
--     (g = 1 ∧ e(P) = 2 ∧ f(P) = 1) := by
--   classical
--   --  1≤  g ≤ 2, 1 ≤ e(P) ≤ 2, and 1 ≤ f(P) ≤ 2 (using interval_cases)
--   have := e_ge_one p S hp P hP -- 1 ≤ e(P)
--   have := f_ge_one p S hp P hP -- 1 ≤ f(P)
--   -- have := g_ge_one p S hp -- 1 ≤ g
--   have := g_eq_two_or_eq_one p S K L hp h_deg -- g = 1 or g = 2(interval_cases not working)
--   -- have : 1 ≤ g  := by omega
--   -- have : g ≤ 2 := by omega
--   have h_sum := Ideal.sum_ramification_inertia S K L hp
--   rw [h_deg] at h_sum
--   have hmul_ge_one : ∀ Q ∈ primesOverFinset p S, 1 ≤ e(Q) * f(Q) :=
--     fun Q hQ => Right.one_le_mul (e_ge_one p S hp Q hQ) (f_ge_one p S hp Q hQ)
--     -- Split the sum: e(P)*f(P) + rest = 2
--   have hsplit := h_sum
--   rw [(Finset.add_sum_erase _ _ hP).symm] at hsplit
--   -- hsplit : e(P)*f(P) + ∑ Q ∈ erase P, e(Q)*f(Q) = 2
--   set rest := ∑ Q ∈ (primesOverFinset p S).erase P, e(Q) * f(Q) with hrest_def
--   have hefP_le : e(P) * f(P) ≤ 2 := by omega
--   have hg_rest : g - 1 ≤ rest := by
--       rw [hrest_def, ← Finset.card_erase_of_mem hP, Finset.card_eq_sum_ones]
--       apply Finset.sum_le_sum
--       intro Q hQ
--       exact hmul_ge_one Q (Finset.mem_of_mem_erase hQ)
--   have hg1_rest0 : g = 1 → rest = 0 := by
--       intro hg1
--       obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hg1
--       have hPa : P = a := Finset.mem_singleton.mp (ha ▸ hP)
--       subst hPa
--       simp [hrest_def, ha]
--   -- e(P) ≤ 2, f(P) ≤ 2
--   have : e(P) ≤ 2 := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hefP_le
--   have : f(P) ≤ 2 := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hefP_le
--   -- interval_cases g <;> interval_cases (e(P)) <;> interval_cases (f(P)) <;>
--   --   omega
--   -- case using g_eq_two_or_eq_one
--   by_cases hg : g = 2 <;> interval_cases (e(P)) <;> interval_cases (f(P)) <;> omega

-- theorem efg_trichotomy' {P}
--       (hp : p ≠ ⊥) (h_deg : Module.finrank K L = 2) (hP : P ∈ primesOverFinset p S) :
--       τ(P) = (1, 1, 2) ∨
--       τ(P) = (1, 2, 1) ∨
--       τ(P) = (2, 1, 1) := by
--     classical
--     have := e_ge_one p S hp P hP
--     have := f_ge_one p S hp P hP
--     have := g_ge_one p S hp
--     have h_sum := h_deg ▸ Ideal.sum_ramification_inertia S K L hp
--     have hmul_ge_one : ∀ Q ∈ primesOverFinset p S, 1 ≤ e(Q) * f(Q) :=
--       fun Q hQ => Right.one_le_mul (e_ge_one p S hp Q hQ) (f_ge_one p S hp Q hQ)
--     have hg_le : g ≤ 2 := by
--       -- rw [← h_sum]
--       -- rw [Finset.card_eq_sum_ones]
--       -- apply Finset.sum_le_sum
--       -- apply hmul_ge_one
--       rw [← h_sum, Finset.card_eq_sum_ones]
--       exact Finset.sum_le_sum (fun P hP => hmul_ge_one P hP)
--     have hsplit := h_sum
--     rw [(Finset.add_sum_erase _ _ hP).symm] at hsplit
--     -- have hsplit := (Finset.add_sum_erase _ _ hP).symm ▸ h_sum
--     set rest := ∑ Q ∈ (primesOverFinset p S).erase P, e(Q) * f(Q) with hrest_def
--     have hefP_le : e(P) * f(P) ≤ 2 := by omega
--     have hg_rest : g - 1 ≤ rest := by
--       rw [hrest_def, ← Finset.card_erase_of_mem hP, Finset.card_eq_sum_ones]
--       apply Finset.sum_le_sum
--       intro Q hQ
--       exact hmul_ge_one Q (Finset.mem_of_mem_erase hQ)
--     have hg1_rest0 : g = 1 → rest = 0 := by
--       intro hg1
--       obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hg1
--       have hPa : P = a := Finset.mem_singleton.mp (ha ▸ hP)
--       subst hPa
--       simp [hrest_def, ha]
--     have : e(P) ≤ 2 := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hefP_le
--     have : f(P) ≤ 2 := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hefP_le
--     interval_cases e(P) <;> interval_cases f(P) <;> interval_cases g <;> simp <;> omega

-- --TODO move to sutable place
-- lemma ef_same_g_eq_one {P} {Q}
--   (hP : P ∈ primesOverFinset p S) (hQ : Q ∈ primesOverFinset p S) (hg1 : g = 1) :
--     e(P) = e(Q) ∧ f(P) = f(Q) := by
--   -- P=Q since g=1
--   obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hg1
--   have hPa : P = a := Finset.mem_singleton.mp (ha ▸ hP)
--   have hQa : Q = a := Finset.mem_singleton.mp (ha ▸ hQ)
--   subst hPa; subst hQa
--   refine ⟨rfl, rfl⟩

-- lemma ef_same_g_eq_two {P} {Q} (hp : p ≠ ⊥) (h_deg : Module.finrank K L = 2)
--   (hP : P ∈ primesOverFinset p S) (hQ : Q ∈ primesOverFinset p S) (hg2 : g = 2) :
--     e(P) = e(Q) ∧ f(P) = f(Q) := by
--   -- g=2 implies e(P)=f(P)=1 for all P
--   have htri := efg_trichotomy p S K L hp h_deg hP
--   have htriQ := efg_trichotomy p S K L hp h_deg hQ
--   rcases htri with ⟨hg2P, he1P, hf1P⟩ | ⟨hg1P, he1P, hf2P⟩ | ⟨hg1P, he2P, hf1P⟩
--   · rcases htriQ with ⟨hg2Q, he1Q, hf1Q⟩ | ⟨hg1Q, he1Q, hf2Q⟩ | ⟨hg1Q, he2Q, hf1Q⟩
--     · exact ⟨he1P ▸ he1Q.symm, hf1P ▸ hf1Q.symm⟩
--     · omega
--     · omega
--   · omega
--   · omega

-- /-∀P e(P) is same -/
--   --TODO(Done): lemma g=1 implies P=Q implies f(P)=f(Q) and e(P)=e(Q) forall P,Q
--   --TODO(Done): lemma g=2 using efg_trichotomy to show e(P)=e(Q)=1 and f(P)=f(Q)=1 for all P,Q
-- lemma e_same_for_all_primes {P} {Q} (hp : p ≠ ⊥) (h_deg : Module.finrank K L = 2)
-- (hP : P ∈ primesOverFinset p S) (hQ : Q ∈ primesOverFinset p S) :
--     e(P) = e(Q) := by
--   -- case on g
--   by_cases hg : g = 2
--   · exact (ef_same_g_eq_two _ _ _ _ hp h_deg hP hQ hg).1
--   · refine (ef_same_g_eq_one _ _ hP hQ ?_).1
--     -- TODO(Done) lemma g=1 or g=2
--     exact (g_eq_two_or_eq_one p S _ _ hp h_deg).resolve_left hg



-- /-∀P f(P) is same (recase htri)-/
-- lemma f_same_for_all_primes {P} {Q} (hp : p ≠ ⊥) (h_deg : Module.finrank K L = 2)
-- (hP : P ∈ primesOverFinset p S) (hQ : Q ∈ primesOverFinset p S) :
--     f(P) = f(Q) := by
--   have htri := efg_trichotomy p S K L hp h_deg hP
--   have htriQ := efg_trichotomy p S K L hp h_deg hQ
--   rcases htri with ⟨hg2, he1, hf1⟩ | ⟨hg1, he1, hf2⟩ | ⟨hg1, he2, hf1⟩
--   · refine (ef_same_g_eq_two _ _ _ _ hp h_deg hP hQ hg2).2
--   · exact (ef_same_g_eq_one p S hP hQ hg1).2
--   · exact (ef_same_g_eq_one p S hP hQ hg1).2

-- --?
-- variable (P : Ideal S) (hP : P ∈ primesOverFinset p S)
-- local notation3 "e" => e(P) -- TODO define `e` not depending on P
-- local notation3 "f" => f(P)
-- local notation3 "τ" => τ(P)


-- lemma isSplit_iff (hp : p ≠ ⊥) (hP : P ∈ primesOverFinset p S)
--     (h_deg : Module.finrank K L = 2) : p.IsSplitIn S ↔ τ = (1, 1, 2) := by
--   have htri := efg_trichotomy p S K L hp h_deg hP
--   constructor
--   · intro hs
--     rw [IsSplitIn] at hs
--     simp
--     omega
--   · intro h
--     -- rw [IsSplitIn]
--     simp at h
--     refine ⟨by omega, fun Q hQ => ?_⟩
--     have:=e_same_for_all_primes p S K L hp h_deg hP hQ
--     omega


-- theorem isSplit_iff_g_eq_two (hp : p ≠ ⊥)
--     (hP : P ∈ primesOverFinset p S) (h_deg : Module.finrank K L = 2) : p.IsSplitIn S ↔ g = 2 := by
--   have : g=2 ↔ τ = (1, 1, 2) := by
--     constructor
--     · have htri := efg_trichotomy p S K L hp h_deg hP
--       rcases htri with ⟨hg2, he1, hf1⟩ | ⟨hg1, he1, hf2⟩ | ⟨hg1, he2, hf1⟩
--       · simp [he1, hf1]
--       · omega
--       · omega
--     · simp
--   rw [isSplit_iff p S K L _ hp hP h_deg, this]




-- theorem isInert_iff_f_eq_two {P} (hp : p ≠ ⊥)
--     (h_deg : Module.finrank K L = 2)
--     (hP : P ∈ primesOverFinset p S) : p.IsInertIn S ↔ f(P) = 2 := by
--   sorry

-- lemma isRamified_iff_e_eq_two {P} (hp : p ≠ ⊥)
--     (h_deg : Module.finrank K L = 2)
--     (hP : P ∈ primesOverFinset p S) : p.IsRamifiedIn S ↔ e(P) = 2 := by
--   sorry
-- /-using efg_trichotomy-/
-- theorem isSplit_or_isInert_or_isRamified'
--     (hp : p ≠ ⊥)
--     (h_deg : Module.finrank K L = 2) :
--   p.IsSplitIn S ∨ p.IsInertIn S ∨ p.IsRamifiedIn S := by
--   classical
--   have hg := g_ge_one p S hp
--   obtain ⟨P, hP⟩ := Finset.card_pos.mp (by omega : 0 < g)
--   have htri := efg_trichotomy p S K L hp h_deg hP
--   rcases htri with ⟨hg2, he1, hf1⟩ | ⟨hg1, he1, hf2⟩ | ⟨hg1, he2, hf1⟩
--   · left
--     refine ⟨by omega, fun Q hQ => ?_⟩
--     have := efg_trichotomy p S K L hp h_deg hQ
--     rcases this with ⟨_, h, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩
--     · exact h
--     · omega
--     · omega
--   · right; left
--     refine ⟨hg1, fun Q hQ => ?_⟩
--     have hQP : Q = P := by
--       obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hg1
--       -- P=a ▸ Q=a
--       exact (Finset.mem_singleton.mp (ha ▸ hP)) ▸ (Finset.mem_singleton.mp (ha ▸ hQ))
--     subst hQP; exact he1
--   · right; right
--     refine ⟨P, hP, by omega⟩


-- end Trichotomy

-- end Ideal
