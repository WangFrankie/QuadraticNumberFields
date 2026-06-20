/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import FiniteAbelianSmith.Correctness

/-!
# Standard Finite-Abelian Targets

This file is the first layer of the class-group structure examples.  It checks
the standard product targets and the multiplication-table classifier before any
quadratic-form data is involved.
-/

set_option linter.hashCommand false

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

open FiniteAbelianSmith

#guard (standardZModProductElems []).length == 1

#guard (standardZModProductElems [2, 6]).length == 12

#guard (StandardGroupIsoType.product [2, 6]).targetElems.length == 12

#guard
    standardZModProductCoords [2, 6]
        (standardZModProductOfCoords [2, 6] [1, 5]) =
      [1, 5]

#guard
    (standardZModProductElems [2, 2]).map (standardZModProductCoords [2, 2]) =
      [[0, 0], [0, 1], [1, 0], [1, 1]]

#guard
    tableMapIsStandardMulEquiv (standardZModProductElems [2, 2])
        (fun x y => x * y) [2, 2] id

#guard
    tableCoordinateMapIsStandardMulEquiv (standardZModProductElems [2, 6])
        (fun x y => x * y) [2, 6] (standardZModProductCoords [2, 6])

#guard
    standardIsoTypeOfMulTable (standardZModProductElems [2, 2])
        (1 : standardZModProduct [2, 2]) (fun x y => x * y) =
      StandardGroupIsoType.product [2, 2]

#guard
    standardIsoTypeOfMulTable (standardZModProductElems [4, 2])
        (1 : standardZModProduct [4, 2]) (fun x y => x * y) =
      StandardGroupIsoType.product [2, 4]

#guard
    standardIsoTypeOfMulTable (standardZModProductElems [2, 6])
        (1 : standardZModProduct [2, 6]) (fun x y => x * y) =
      StandardGroupIsoType.product [2, 6]

end BinaryQuadraticForm
end QuadraticNumberFields
