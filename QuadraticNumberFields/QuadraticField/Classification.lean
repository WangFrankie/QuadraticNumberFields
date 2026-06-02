/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.QuadraticField.Parameters
import QuadraticNumberFields.QuadraticField.Basic
import QuadraticNumberFields.Instances
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Field.Equiv
import Mathlib.Tactic

/-!
# Classification of Quadratic Fields by Squarefree Integer Parameters

This file proves that a field over `ℚ` is quadratic exactly when it is
isomorphic to one of the explicit models `Qsqrtd (z : ℚ) = ℚ(√z)` with
`z : ℤ` squarefree and `z ≠ 1`.

## Main Theorems

* `exists_squarefree_int_param_of_isQuadraticField`: every quadratic field is
  isomorphic to `Qsqrtd (z : ℚ)` for some squarefree integer `z ≠ 1`.
* `exists_algEquiv_qsqrtd`: the same classification interface stated using the
  project-level `[QuadraticField K]` abstraction.
* `exists_ringEquiv_qsqrtd`: the ring-equivalence shadow of the classification
  interface, useful for invariants that do not depend on the chosen `ℚ`-algebra
  structure.
* `isQuadraticField_iff_exists_squarefree_int_param`: characterization of
  quadratic fields via the normalized models `Qsqrtd (z : ℚ)`.

## Implementation Note

To avoid the `ℚ`-algebra diamond on `Qsqrtd q`, this file disables the
instance `DivisionRing.toRatAlgebra` locally, following the same pattern as
`TotallyRealComplex.lean`.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped QuadraticAlgebra
open Polynomial IntermediateField

/-- `d` is a normalized standard parameter for the abstract quadratic field `K`
if it is squarefree, not equal to `1`, and `K` is isomorphic to `Qsqrtd d`. -/
def IsStandardParameter (K : Type*) [Field K] [Algebra ℚ K] (d : ℤ) : Prop :=
  Squarefree d ∧ d ≠ 1 ∧ Nonempty (K ≃ₐ[ℚ] Qsqrtd (d : ℚ))

/-- Completing the square: a quadratic field over `ℚ` has a generator `β` whose
square is a rational scalar `q = b²/4 - c`, where `X² + bX + c` is the minimal
polynomial of a primitive element. -/
private theorem exists_top_generator_sq_rat
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K] :
    ∃ (β : K) (q : ℚ),
      IntermediateField.adjoin ℚ ({β} : Set K) = ⊤ ∧ β * β = algebraMap ℚ K q := by
  obtain ⟨α, hαtop⟩ := Field.exists_primitive_element ℚ K
  let b : ℚ := (minpoly ℚ α).coeff 1
  let c : ℚ := (minpoly ℚ α).coeff 0
  have hdeg : (minpoly ℚ α).natDegree = 2 := by
    have h := (Field.primitive_element_iff_minpoly_natDegree_eq ℚ α).mp hαtop
    have hfin : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
    simpa [hfin] using h
  have hmonic : (minpoly ℚ α).Monic := minpoly.monic (IsIntegral.of_finite (R := ℚ) (B := K) α)
  have hpoly : minpoly ℚ α = X ^ 2 + C b * X + C c := by
    rcases (Polynomial.isMonicOfDegree_two_iff.mp ⟨hdeg, hmonic⟩) with ⟨b', c', hp⟩
    have hb : b' = b := by simp [b, hp]
    have hc : c' = c := by simp [c, hp]
    simpa [b, c, hb, hc] using hp
  have hroot : α * α + algebraMap ℚ K b * α + algebraMap ℚ K c = 0 := by
    have h : aeval α (X ^ 2 + C b * X + C c : ℚ[X]) = 0 := by
      simpa [hpoly] using minpoly.aeval ℚ α
    simpa [aeval_def, sq] using h
  refine ⟨α + algebraMap ℚ K (b / 2), b ^ 2 / 4 - c, ?_, ?_⟩
  · apply top_unique
    rw [← hαtop]
    refine (IntermediateField.adjoin_simple_le_iff).2 ?_
    set β : K := α + algebraMap ℚ K (b / 2) with hβdef
    have hβ : β ∈ IntermediateField.adjoin ℚ ({β} : Set K) :=
      IntermediateField.mem_adjoin_simple_self ℚ β
    have hconst : algebraMap ℚ K (b / 2) ∈ IntermediateField.adjoin ℚ ({β} : Set K) :=
      IntermediateField.adjoin.algebraMap_mem ℚ ({β} : Set K) (b / 2)
    simpa [hβdef, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using sub_mem hβ hconst
  · have hroot' : α * α + algebraMap ℚ K b * α = - algebraMap ℚ K c := by
      linear_combination hroot
    have hcoeff : algebraMap ℚ K (b / 2) + algebraMap ℚ K (b / 2) = algebraMap ℚ K b := by
      exact_mod_cast (by ring : b / 2 + b / 2 = b)
    have hsq : (algebraMap ℚ K (b / 2)) ^ 2 = algebraMap ℚ K (b ^ 2 / 4) := by
      have h : (b / 2) ^ 2 = b ^ 2 / 4 := by ring
      simpa [pow_two, map_mul] using congrArg (algebraMap ℚ K) h
    calc
      (α + algebraMap ℚ K (b / 2)) * (α + algebraMap ℚ K (b / 2))
          = α * α + (algebraMap ℚ K (b / 2) + algebraMap ℚ K (b / 2)) * α +
              (algebraMap ℚ K (b / 2)) ^ 2 := by
                ring
      _ = α * α + algebraMap ℚ K b * α + algebraMap ℚ K (b ^ 2 / 4) := by
        rw [hcoeff, hsq]
      _ = - algebraMap ℚ K c + algebraMap ℚ K (b ^ 2 / 4) := by
        rw [hroot']
      _ = algebraMap ℚ K (b ^ 2 / 4 - c) := by
        exact_mod_cast (by ring : -c + b ^ 2 / 4 = b ^ 2 / 4 - c)

/-- A generator of a quadratic field is never the image of a rational under
`algebraMap`, since that would collapse the extension to dimension `1`. -/
private lemma top_generator_ne_algebraMap
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K]
    {β : K} (hβtop : IntermediateField.adjoin ℚ ({β} : Set K) = ⊤) (s : ℚ) :
    β ≠ algebraMap ℚ K s := by
  intro hβalg
  have htop' : (⊥ : IntermediateField ℚ K) = ⊤ := by
    have hA : IntermediateField.adjoin ℚ ({algebraMap ℚ K s} : Set K) = ⊤ := by
      simpa [hβalg] using hβtop
    have hB : IntermediateField.adjoin ℚ ({algebraMap ℚ K s} : Set K) = ⊥ := by simp
    exact hB.symm.trans hA
  have h1 : Module.finrank ℚ (⊥ : IntermediateField ℚ K) = 1 := by simp
  have h2 : Module.finrank ℚ (⊤ : IntermediateField ℚ K) = 2 := by
    simpa using Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  rw [htop'] at h1
  omega

/-- If a generator `β` of a quadratic field squares to the rational scalar `q`,
then `q` is not a square in `ℚ`: otherwise `β` would equal `±√q ∈ ℚ`. -/
private lemma not_isSquare_of_top_generator_sq
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K]
    {β : K} {q : ℚ} (hβtop : IntermediateField.adjoin ℚ ({β} : Set K) = ⊤)
    (hβsq : β * β = algebraMap ℚ K q) :
    ¬ IsSquare q := by
  rintro ⟨r, hr⟩
  have hfac : (β - algebraMap ℚ K r) * (β + algebraMap ℚ K r) = 0 := by
    have hmapsq : (algebraMap ℚ K r) ^ 2 = algebraMap ℚ K (r ^ 2) := by
      simp [pow_two, map_mul]
    calc
      (β - algebraMap ℚ K r) * (β + algebraMap ℚ K r) = β ^ 2 - (algebraMap ℚ K r) ^ 2 := by
        ring
      _ = β * β - algebraMap ℚ K (r ^ 2) := by rw [pow_two, hmapsq]
      _ = 0 := by simp [hr, hβsq, pow_two]
  rcases mul_eq_zero.mp hfac with h | h
  · exact top_generator_ne_algebraMap hβtop r (sub_eq_zero.mp h)
  · exact top_generator_ne_algebraMap hβtop (-r)
      (by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h)

/-- A quadratic field over `ℚ` containing an element `β` whose square is a
nonsquare rational scalar `q` is isomorphic to the standard model `Qsqrtd q`. -/
private theorem algEquiv_qsqrtd_of_sq_eq
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K]
    {q : ℚ} [Fact (¬ IsSquare q)] {β : K} (hβsq : β * β = algebraMap ℚ K q) :
    Nonempty (K ≃ₐ[ℚ] Qsqrtd q) := by
  let f : Qsqrtd q →ₐ[ℚ] K :=
    (QuadraticAlgebra.lift (R := ℚ) (a := q) (b := (0 : ℚ)) (A := K))
      ⟨β, by simpa [← Algebra.algebraMap_eq_smul_one] using hβsq⟩
  have hdim : Module.finrank ℚ (Qsqrtd q) = Module.finrank ℚ K := by
    have h1 : Module.finrank ℚ (Qsqrtd q) = 2 := by
      simpa using QuadraticAlgebra.finrank_eq_two q (0 : ℚ)
    have h2 : Module.finrank ℚ K = 2 := by
      simpa using Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
    omega
  have hinj : Function.Injective f.toLinearMap := RingHom.injective f.toRingHom
  have hsurj : Function.Surjective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hbij : Function.Bijective f := ⟨RingHom.injective f.toRingHom, hsurj⟩
  exact ⟨(AlgEquiv.ofBijective f hbij).symm⟩

/-- Every quadratic field over `ℚ` is isomorphic to `ℚ(√q)` for some
nonsquare rational parameter `q`. This is an internal intermediate step before
normalizing the parameter to a squarefree integer. -/
private theorem exists_rat_param_of_isQuadraticField
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K] :
    ∃ q : ℚ, ¬ IsSquare q ∧ Nonempty (K ≃ₐ[ℚ] Qsqrtd q) := by
  obtain ⟨β, q, hβtop, hβsq⟩ := exists_top_generator_sq_rat K
  have hq : ¬ IsSquare q := not_isSquare_of_top_generator_sq hβtop hβsq
  letI : Fact (¬ IsSquare q) := ⟨hq⟩
  exact ⟨q, hq, algEquiv_qsqrtd_of_sq_eq hβsq⟩

/-- Every quadratic field over `ℚ` is isomorphic to `ℚ(√z)` for some squarefree
integer parameter `z ≠ 1`. -/
theorem exists_squarefree_int_param_of_isQuadraticField
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsQuadraticExtension ℚ K] :
    ∃ z : ℤ, Squarefree z ∧ z ≠ 1 ∧ Nonempty (K ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  obtain ⟨q, _hq, hKq⟩ := exists_rat_param_of_isQuadraticField K
  rcases hKq with ⟨eKq⟩
  obtain ⟨n, hqn⟩ := Qsqrtd_iso_int_param q
  rcases hqn with ⟨eqn⟩
  have hn0 : n ≠ 0 := by
    intro hn0
    subst n
    have e : K ≃ₐ[ℚ] Qsqrtd (0 : ℚ) := eKq.trans eqn
    have hF : IsField (Qsqrtd (0 : ℚ)) := e.toMulEquiv.symm.isField (Field.toIsField K)
    exact Qsqrtd.zero_not_isField hF
  obtain ⟨z, hzsf, hNz⟩ := Qsqrtd_iso_squarefree_int_param (d := n) hn0
  rcases hNz with ⟨enz⟩
  have hz1 : z ≠ 1 := by
    intro hz1
    subst z
    have e : K ≃ₐ[ℚ] Qsqrtd (1 : ℚ) := (eKq.trans eqn).trans enz
    have hF : IsField (Qsqrtd (1 : ℚ)) := e.toMulEquiv.symm.isField (Field.toIsField K)
    exact Qsqrtd.one_not_isField hF
  exact ⟨z, hzsf, hz1, ⟨(eKq.trans eqn).trans enz⟩⟩

/-- Every abstract quadratic field over `ℚ` is isomorphic to a standard model
`Qsqrtd (d : ℚ)` for some squarefree integer parameter `d ≠ 1`. -/
theorem exists_algEquiv_qsqrtd
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧ Nonempty (K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) :=
  exists_squarefree_int_param_of_isQuadraticField K

/-- Every abstract quadratic field is ring-equivalent to a standard model
`Qsqrtd (d : ℚ)` for some squarefree integer parameter `d ≠ 1`.

This forgetful version is convenient for transporting invariants, such as the
absolute discriminant, whose transport lemmas are stated for ring equivalences. -/
theorem exists_ringEquiv_qsqrtd
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧ Nonempty (K ≃+* Qsqrtd (d : ℚ)) := by
  obtain ⟨d, hd_sf, hd_ne, ⟨e⟩⟩ := exists_algEquiv_qsqrtd K
  exact ⟨d, hd_sf, hd_ne, ⟨e.toRingEquiv⟩⟩

/-- Every abstract quadratic field has a normalized standard parameter. -/
theorem exists_isStandardParameter
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    ∃ d : ℤ, IsStandardParameter K d :=
  exists_algEquiv_qsqrtd K

/-- A field over `ℚ` is quadratic iff it is isomorphic to `ℚ(√z)` for some
squarefree integer `z ≠ 1`. -/
theorem isQuadraticField_iff_exists_squarefree_int_param
    (K : Type*) [Field K] [Algebra ℚ K] :
    Algebra.IsQuadraticExtension ℚ K ↔
      ∃ z : ℤ, Squarefree z ∧ z ≠ 1 ∧ Nonempty (K ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  constructor
  · intro hK
    letI : Algebra.IsQuadraticExtension ℚ K := hK
    exact exists_squarefree_int_param_of_isQuadraticField K
  · rintro ⟨z, hzsf, hz1, ⟨e⟩⟩
    letI : Fact (Squarefree z) := ⟨hzsf⟩
    letI : Fact (z ≠ 1) := ⟨hz1⟩
    have h2 : Module.finrank ℚ (Qsqrtd (z : ℚ)) = 2 := by
      simpa using QuadraticAlgebra.finrank_eq_two (z : ℚ) (0 : ℚ)
    refine { finrank_eq_two' := ?_ }
    exact (LinearEquiv.finrank_eq e.toLinearEquiv).trans h2
