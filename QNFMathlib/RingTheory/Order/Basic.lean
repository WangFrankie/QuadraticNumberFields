/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension

/-!
# Orders in algebras

An `R`-order in a `K`-algebra `A` (Reiner, *Maximal Orders*, §8) is an `R`-subalgebra
that is a finitely generated `R`-module and spans `A` over `K`. The intended setting is
that `K` is the fraction field of `R`, but the definition imposes no such hypothesis,
nor any degree condition on `A`.
-/

namespace Subalgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- An `R`-subalgebra `Λ` of a `K`-algebra `A` is an `R`-order in `A` if it is a finitely
generated `R`-module whose `K`-span is all of `A`. No relation between `R` and `K`, and no
finiteness of `A` over `K`, is assumed. -/
structure IsOrder (K : Type*) [CommRing K] [Algebra K A] (Λ : Subalgebra R A) : Prop where
  /-- An order is a finitely generated module over the base ring. -/
  finite : Module.Finite R Λ
  /-- An order spans the ambient algebra over `K`. -/
  span_eq_top : Submodule.span K (Λ : Set A) = ⊤

end Subalgebra
