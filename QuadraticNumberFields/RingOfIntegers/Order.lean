/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.RingOfIntegers.Integrality

/-!
# Embedded Orders in a Quadratic Field

This file introduces a lightweight structure `EmbeddedOrder K` recording a
commutative ring embedded into a quadratic field `K` by an injective ring
homomorphism whose image consists of integral elements over `ℤ`.  It unifies
the two standard integer models `ℤ[√d]` (`Zsqrtd`) and `ℤ[(1+√d)/2]`
(`ZOnePlusSqrtOverTwo`) under a common "order embedded in the ambient field"
language.

## Main definitions

* `QuadraticNumberFields.EmbeddedOrder`: a ring embedded in `K` by an injective,
  integrality-preserving ring homomorphism.
* `QuadraticNumberFields.Zsqrtd.embeddedOrder`: `ℤ[√d]` as an embedded order of
  `ℚ(√d)`.
* `QuadraticNumberFields.ZOnePlusSqrtOverTwo.embeddedOrder`: `ℤ[(1+√d)/2]` as an
  embedded order of `ℚ(√(1 + 4k))`.

## Implementation notes

The ambient `K` is required to be a `ℚ`-algebra field, so the standard-model
instantiations carry the `Fact (Squarefree _)` / `Fact (_ ≠ 1)` hypotheses that
supply the field structure on `Qsqrtd`.  Integrality is taken over `ℤ` using the
canonical `ℤ`-algebra structure available on every commutative ring.
-/

namespace QuadraticNumberFields

/-- An order of a quadratic field `K`, presented as a commutative ring `R`
together with an injective ring embedding `R →+* K` whose image is integral over
`ℤ`. -/
structure EmbeddedOrder (K : Type*) [Field K] [Algebra ℚ K] where
  /-- The underlying commutative ring. -/
  R : Type*
  /-- Its commutative-ring structure. -/
  [instCommRing : CommRing R]
  /-- The embedding into the ambient field. -/
  emb : R →+* K
  /-- The embedding is injective. -/
  inj : Function.Injective emb
  /-- Every element of the image is integral over `ℤ`. -/
  integral : ∀ r : R, IsIntegral ℤ (emb r)

attribute [instance] EmbeddedOrder.instCommRing

namespace Zsqrtd

/-- `ℤ[√d]` as an embedded order of the quadratic field `ℚ(√d)`. -/
def embeddedOrder (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    EmbeddedOrder (Qsqrtd (d : ℚ)) where
  R := Zsqrtd d
  emb := Zsqrtd.toQsqrtdHom d
  inj := Zsqrtd.toQsqrtdHom_injective d
  integral := RingOfIntegers.isIntegral_toQsqrtd d

end Zsqrtd

namespace ZOnePlusSqrtOverTwo

/-- `ℤ[(1+√d)/2]` as an embedded order of the quadratic field `ℚ(√(1 + 4k))`. -/
def embeddedOrder (k : ℤ) [Fact (Squarefree (1 + 4 * k))] [Fact ((1 + 4 * k : ℤ) ≠ 1)] :
    EmbeddedOrder (Qsqrtd ((1 + 4 * k : ℤ) : ℚ)) where
  R := _root_.ZOnePlusSqrtOverTwo k
  emb := _root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k
  inj := _root_.ZOnePlusSqrtOverTwo.toQsqrtdHom_injective k
  integral := RingOfIntegers.isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k

end ZOnePlusSqrtOverTwo

end QuadraticNumberFields
