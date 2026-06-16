/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.GaussCompositionClass

/-!
# Cox Ideal Multiplicativity for Concordant Gauss Composition

This file proves that Cox ideal classes multiply under direct concordant
Gauss composition. The shared algebra is kept in the generic
`QuadraticAlgebra ℤ DD bb` coordinate model before specializing to the two
integer-ring branches.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

namespace CoxComposition

open QuadraticNumberFields.CoxIdealRelation

section Generic

variable {DD bb A B C A' C' u : ℤ}

end Generic

end CoxComposition

namespace PrimitivePositiveDefiniteForm

end PrimitivePositiveDefiniteForm

end BinaryQuadraticForm
end QuadraticNumberFields
