import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Class-group checks" =>

:::group "class_group_checks_core"
Minkowski bounds and finite checks for quadratic class groups.
:::

:::definition "minkowski_bound" (parent := "class_group_checks_core") (lean := "QuadraticNumberFields.Qsqrtd.minkowskiBound") (tags := "complete, project-only")
`Qsqrtd.minkowskiBound d` specializes the number-field Minkowski bound to the
quadratic field $`\mathbb{Q}(\sqrt d)`.
:::

:::theorem "minkowski_representatives" (parent := "class_group_checks_core") (lean := "QuadraticNumberFields.Qsqrtd.exists_ideal_in_class_of_norm_le") (tags := "complete, project-only")
Every ideal class has a representative whose norm is at most
{uses "minkowski_bound"}[the specialized Minkowski bound].
:::

:::theorem "imaginary_minkowski_bound" (parent := "class_group_checks_core") (lean := "QuadraticNumberFields.Qsqrtd.exists_ideal_in_class_of_norm_le_imaginary") (tags := "complete, project-only")
The imaginary quadratic branch has the explicit constant
$`(2/\pi)\sqrt{|D|}`.
:::

:::theorem "real_minkowski_bound" (parent := "class_group_checks_core") (lean := "QuadraticNumberFields.Qsqrtd.exists_ideal_in_class_of_norm_le_real") (tags := "complete, project-only")
The real quadratic branch has the explicit constant $`\frac12\sqrt{|D|}`.
:::

:::theorem "sqrt_neg_five_class_group_checks" (parent := "class_group_checks_core") (lean := "QuadraticNumberFields.Examples.SqrtNeg5.minkowskiBound_lt_three, QuadraticNumberFields.Examples.SqrtNeg5.exists_ideal_in_class_of_norm_le") (tags := "complete, project-only")
The $`\sqrt{-5}` example contains concrete bounded-norm checks that exercise the
class-number interface.
:::

:::theorem "finite_norm_search" (parent := "class_group_checks_core") (tags := "partial, project-only") (effort := "large")
A future class-group pipeline should turn the Minkowski representative theorem
into finite norm searches for selected quadratic fields and families.
:::

:::theorem "class_number_one_certificates" (parent := "class_group_checks_core") (tags := "future, project-only") (effort := "large")
The planned output of the finite-check machinery is reusable certificates for
class-number-one or nontrivial class-group computations.
:::
