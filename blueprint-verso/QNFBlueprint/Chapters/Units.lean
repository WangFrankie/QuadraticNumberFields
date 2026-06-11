import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Units" =>

:::group "units_core"
Pell-type units, imaginary unit classifications, and fundamental-unit scaffolding.
:::

:::definition "pell_solution_predicate" (parent := "units_core") (lean := "QuadraticNumberFields.Units.IsPellSolution") (tags := "complete, project-only")
`IsPellSolution d n x y` records the Pell-type equation $`x^2-dy^2=n`.
This is the bridge between coordinate arithmetic in `Zsqrtd d` and units.
:::

:::theorem "pell_solution_multiplication" (parent := "units_core") (lean := "QuadraticNumberFields.Units.IsPellSolution.mul") (tags := "complete, project-only")
Pell solutions multiply according to the norm multiplication law in
$`\mathbb{Z}[\sqrt d]`.
:::

:::theorem "zsqrtd_units_pell" (parent := "units_core") (lean := "QuadraticNumberFields.Units.isUnit_mk_iff_isPellSolution") (tags := "complete, project-only")
A coordinate element $`x + y\sqrt d` is a unit exactly when the corresponding
Pell equation has norm $`1` or $`-1`.
:::

:::theorem "imaginary_zsqrtd_units" (parent := "units_core") (lean := "QuadraticNumberFields.Units.isUnit_zsqrtd_iff_of_lt_neg_one") (tags := "complete, project-only")
For $`d < -1`, the only units of $`\mathbb{Z}[\sqrt d]` are $`\pm 1`.
:::

:::theorem "imaginary_zomega_units" (parent := "units_core") (lean := "QuadraticNumberFields.Units.isUnit_zOnePlusSqrtOverTwo_iff_of_le_neg_two") (tags := "complete, project-only")
The analogous imaginary result holds in the half-integer order for parameters
$`k \le -2`.
:::

:::definition "fundamental_unit_predicate" (parent := "units_core") (lean := "QuadraticNumberFields.Units.IsFundamentalUnit") (tags := "complete, project-only")
`IsFundamentalUnit` is the project predicate for a generator of the infinite
part of a real quadratic unit group, modulo sign and inverse ambiguity.
:::

:::theorem "fundamental_unit_transport" (parent := "units_core") (lean := "QuadraticNumberFields.Units.IsFundamentalUnit.map_ringEquiv") (tags := "complete, project-only")
Fundamental-unit structure transports across ring equivalences, matching the
project's broader transport-first architecture.
:::

:::theorem "continued_fraction_units" (parent := "units_core") (tags := "partial, project-only") (effort := "large")
The future real-quadratic unit pipeline should connect continued fractions and
Pell solutions to explicit fundamental units.
:::
