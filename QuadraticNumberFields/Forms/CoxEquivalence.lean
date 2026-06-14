/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.InverseCox

/-!
# Cox 7.7 Equivalence Assembly

This file is the assembly layer for the imaginary Cox 7.7 correspondence.  The
forward map from form classes to ideal classes lives in `Forms.Bridge`; the
inverse-direction map from ideal classes to form classes lives in
`Forms.InverseCox`, which imports `Forms.Bridge`.  Therefore the final
equivalence belongs here rather than in `Forms.Bridge`.
-/

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section CoxEquivalence

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- Assemble the Cox 7.7 equivalence once the forward and inverse maps have
been proved to be inverse to each other. -/
noncomputable def formClassEquivClassGroupOfInverseLaws (hdneg : d < 0)
    (hleft : ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C)
    (hright : ∀ C : ClassGroup 𝓞K,
      formClassToClassGroup d (classGroupToFormClass hdneg C) = C) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup 𝓞K where
  toFun := formClassToClassGroup d
  invFun := classGroupToFormClass hdneg
  left_inv := hleft
  right_inv := hright

end CoxEquivalence
end BinaryQuadraticForm
end QuadraticNumberFields
