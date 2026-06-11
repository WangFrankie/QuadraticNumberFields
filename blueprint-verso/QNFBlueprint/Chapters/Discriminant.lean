import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Discriminants" =>

:::group "discriminant_core"
The discriminant formula and its Dedekind-domain consequences.
:::

:::theorem "discr_zsqrtd_basis" (parent := "discriminant_core") (lean := "QuadraticNumberFields.RingOfIntegers.discr_zsqrtd_basis") (tags := "complete, project-only")
The $`\mathbb{Z}[\sqrt d]` basis has discriminant $`4d`. This is the basis
calculation for the non-$`1 \pmod 4` branch.
:::

:::theorem "discr_zomega_basis" (parent := "discriminant_core") (lean := "QuadraticNumberFields.RingOfIntegers.discr_zOnePlusSqrtOverTwo_basis") (tags := "complete, project-only")
The $`\mathbb{Z}[(1+\sqrt d)/2]` basis has discriminant $`d` when
$`d = 1 + 4k`.
:::

:::theorem "discr_formula" (parent := "discriminant_core") (lean := "QuadraticNumberFields.RingOfIntegers.discr_formula") (tags := "complete, project-only")
For squarefree $`d \ne 1`, the discriminant of $`\mathbb{Q}(\sqrt d)` is
$`d` in the $`1 \pmod 4` branch and $`4d` otherwise.
:::

:::theorem "discr_formula_transport" (parent := "discriminant_core") (lean := "QuadraticNumberFields.RingOfIntegers.discr_formula_of_algEquiv_qsqrtd, QuadraticNumberFields.RingOfIntegers.exists_discr_formula_of_quadraticField") (tags := "complete, project-only")
The discriminant formula transports from the standard model to an abstract
quadratic field once an algebra equivalence to {uses "discr_formula"}[a standard
parameter] is chosen.
:::

:::theorem "dedekind_domain_project_zsqrtd" (parent := "discriminant_core") (lean := "QuadraticNumberFields.Zsqrtd.isDedekindDomain_iff_mod_four_ne_one") (tags := "complete, project-only")
The project model $`\mathbb{Z}[\sqrt d]` is Dedekind exactly in the same branch
where it is already the full ring of integers: $`d \not\equiv 1 \pmod 4`.
:::

:::theorem "discriminant_examples" (parent := "discriminant_core") (lean := "QuadraticNumberFields.RingOfIntegers.discr_gaussian, QuadraticNumberFields.RingOfIntegers.discr_eisenstein, QuadraticNumberFields.RingOfIntegers.discr_Qsqrtd_neg_five") (tags := "complete, project-only")
The library includes concrete discriminant checks for the Gaussian, Eisenstein,
and $`\mathbb{Q}(\sqrt{-5})` examples.
:::
