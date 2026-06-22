/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-!
# Idèle Groups

Material destined for mathlib.

This file defines the idèle group of a number field, its principal idèle
subgroup, and the algebraic idèle class group. The definitions follow the
existing `AdeleRing R K` API, keeping the same generality of a Dedekind domain
`R` with field of fractions `K`.

## Main definitions

- `NumberField.FiniteIdeleGroup`: the group of finite idèles.
- `NumberField.IdeleGroup`: the idèle group.
- `NumberField.principalIdeleHom`: the diagonal embedding of `Kˣ` into the
  idèle group.
- `NumberField.principalIdeleSubgroup`: the subgroup of principal idèles.
- `NumberField.IdeleClassGroup`: the algebraic quotient by principal idèles.

## Implementation notes

The quotient `IdeleClassGroup R K` is only the algebraic quotient group. Class
field theory needs additional topology on the idèle group and its quotients,
which is intentionally not introduced here.
-/

noncomputable section

open IsDedekindDomain
open scoped RestrictedProduct

namespace NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The finite idèle group of `K` with respect to a Dedekind domain `R` whose
field of fractions is `K`. -/
abbrev FiniteIdeleGroup : Type _ :=
  (FiniteAdeleRing R K)ˣ

/-- The finite idèle group as the restricted product of the local unit groups. -/
noncomputable def finiteIdeleGroupEquivRestrictedProductUnits :
    FiniteIdeleGroup R K ≃*
      Πʳ v : HeightOneSpectrum R,
        [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  RestrictedProduct.unitsEquiv fun v : HeightOneSpectrum R => v.adicCompletion K

/-- The idèle group of `K` with respect to a Dedekind domain `R` whose field of
fractions is `K`. -/
abbrev IdeleGroup : Type _ :=
  (AdeleRing R K)ˣ

/-- The idèle group is the product of the infinite adèle units and the finite
idèle group. -/
noncomputable def ideleGroupEquivInfiniteFinite :
    IdeleGroup R K ≃* (InfiniteAdeleRing K)ˣ × FiniteIdeleGroup R K :=
  MulEquiv.prodUnits

/-- The diagonal embedding of `Kˣ` into the idèle group. -/
noncomputable def principalIdeleHom : Kˣ →* IdeleGroup R K :=
  Units.map (algebraMap K (AdeleRing R K)).toMonoidHom

@[simp]
theorem principalIdeleHom_apply (x : Kˣ) :
    ((principalIdeleHom R K x : IdeleGroup R K) : AdeleRing R K) =
      algebraMap K (AdeleRing R K) x :=
  rfl

/-- For a number field `K`, the diagonal embedding of `Kˣ` into the idèle group
is injective. -/
theorem principalIdeleHom_injective [NumberField K] :
    Function.Injective (principalIdeleHom R K) := by
  intro x y h
  ext
  exact AdeleRing.algebraMap_injective R K (congrArg Units.val h)

/-- The subgroup of principal idèles, i.e. the image of `Kˣ` under the diagonal
embedding into the idèle group. -/
abbrev principalIdeleSubgroup : Subgroup (IdeleGroup R K) :=
  (principalIdeleHom R K).range

/-- The algebraic idèle class group: the quotient of the idèle group by the
subgroup of principal idèles. This definition does not equip the quotient with
the quotient topology. -/
abbrev IdeleClassGroup : Type _ :=
  (IdeleGroup R K) ⧸ (principalIdeleSubgroup R K)

end NumberField
