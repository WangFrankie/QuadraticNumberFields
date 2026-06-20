/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Tactic

/-!
# A quadratic Dedekind extension whose fraction-field extension is not separable

This file gives a counterexample showing that the ring-theoretic hypotheses used before the
separability step in `Splitting/Defs.lean` do not imply separability of the fraction-field
extension.

The construction is the standard characteristic-`2` example:

* `K = 𝔽₂(t)`, implemented as `RatFunc (ZMod 2)`;
* `L = K(α)` where `α` is a root of `X^2 - t`.

Then `L / K` is quadratic but not separable.

## Main Theorems

* `Counterexample.isQuadraticExtension_not_imply_isSeparable`
* `Counterexample.quadratic_dedekind_not_imply_separable`
-/

open Polynomial

noncomputable section

namespace Counterexample

/-- The base field `𝔽₂(t)`. -/
abbrev BaseField := RatFunc (ZMod 2)

/-- The polynomial `X^2 - t` over `𝔽₂(t)`. -/
abbrev polynomial : BaseField[X] := X ^ 2 - C (RatFunc.X : BaseField)

/-- The extension field `𝔽₂(t)[X] / (X^2 - t)`. -/
abbrev ExtensionField := AdjoinRoot polynomial

theorem polynomial_ne_zero : polynomial ≠ (0 : BaseField[X]) :=
  X_pow_sub_C_ne_zero (n := 2) (by decide) (RatFunc.X : BaseField)

theorem sq_ne_X (x : BaseField) : x ^ 2 ≠ (RatFunc.X : BaseField) := by
  intro hx
  by_cases hx0 : x = 0
  · subst hx0
    have hx0' : (0 : BaseField) * 0 = RatFunc.X := by
      simpa [pow_two] using hx
    have hx' : (0 : BaseField) = RatFunc.X := by
      calc
        (0 : BaseField) = (0 : BaseField) * 0 := by
          symm
          exact zero_mul 0
        _ = RatFunc.X := hx0'
    exact RatFunc.X_ne_zero hx'.symm
  have hdeg : (1 : ℤ) = 2 * RatFunc.intDegree x := by
    calc
      (1 : ℤ) = RatFunc.intDegree (RatFunc.X : BaseField) := by simp
      _ = RatFunc.intDegree (x ^ 2) := by rw [hx]
      _ = RatFunc.intDegree x + RatFunc.intDegree x := by
        simpa [pow_two] using (RatFunc.intDegree_mul hx0 hx0)
      _ = 2 * RatFunc.intDegree x := by ring
  omega

theorem polynomial_irreducible : Irreducible polynomial := by
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two ?_
  intro x
  exact sq_ne_X x

instance : Fact (Irreducible polynomial) := ⟨polynomial_irreducible⟩

theorem polynomial_not_separable : ¬ polynomial.Separable := by
  rw [Polynomial.X_pow_sub_C_separable_iff (n := 2) (x := (RatFunc.X : BaseField))
    (by decide) RatFunc.X_ne_zero]
  simpa using (CharP.cast_eq_zero (R := BaseField) 2)

theorem root_not_isSeparable : ¬ IsSeparable BaseField (AdjoinRoot.root polynomial) := by
  rw [IsSeparable]
  rw [show minpoly BaseField (AdjoinRoot.root polynomial) = polynomial by
    simpa [polynomial] using
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic (f := polynomial)
        (monic_X_pow_sub_C (RatFunc.X : BaseField) (by decide)))]
  exact polynomial_not_separable

noncomputable instance : Algebra.IsQuadraticExtension BaseField ExtensionField where
  exists_basis := ⟨_, (AdjoinRoot.powerBasis polynomial_ne_zero).basis⟩
  finrank_eq_two' := by
    simpa [ExtensionField, polynomial] using
      (finrank_quotient_span_eq_natDegree (f := polynomial) (K := BaseField))

theorem not_isSeparable : ¬ Algebra.IsSeparable BaseField ExtensionField := by
  intro hsep
  exact root_not_isSeparable <|
    Algebra.IsSeparable.isSeparable BaseField (AdjoinRoot.root polynomial)

/-- A quadratic field extension need not be separable. -/
theorem isQuadraticExtension_not_imply_isSeparable :
    ¬ ∀ (F E : Type) [Field F] [Field E] [Algebra F E]
        [Algebra.IsQuadraticExtension F E], Algebra.IsSeparable F E := by
  intro h
  exact not_isSeparable <|
    @h BaseField ExtensionField inferInstance inferInstance inferInstance inferInstance

/-- Even the stronger ring-theoretic hypotheses from the abstract trichotomy setup do not imply
separability of the fraction-field extension. -/
theorem quadratic_dedekind_not_imply_separable :
    ¬ ∀ (R S K L : Type) [CommRing R] [CommRing S] [Field K] [Field L]
        [Algebra R S] [Algebra R K] [Algebra S L] [Algebra R L] [Algebra K L]
        [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
        [IsFractionRing R K] [IsFractionRing S L]
        [IsScalarTower R K L] [IsScalarTower R S L]
        [Algebra.IsQuadraticExtension R S],
        Algebra.IsSeparable K L := by
  intro h
  exact not_isSeparable <|
    @h BaseField ExtensionField BaseField ExtensionField
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance

end Counterexample
