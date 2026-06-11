import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Rings of integers" =>

:::group "ring_of_integers_core"
The mod-4 classification of rings of integers in quadratic fields.
:::

:::definition "zsqrtd_order" (parent := "ring_of_integers_core") (lean := "QuadraticNumberFields.Zsqrtd") (tags := "complete, project-only")
`Zsqrtd d` is the project-owned model of $`\mathbb{Z}[\sqrt d]`. It is not
mathlib's `Zsqrtd`; the bridge to mathlib's model is intentionally thin and
isolated.
:::

:::definition "zomega_order" (parent := "ring_of_integers_core") (lean := "ZOnePlusSqrtOverTwo") (tags := "complete, project-only")
`ZOnePlusSqrtOverTwo k` is the project model of
$`\mathbb{Z}[(1+\sqrt{1+4k})/2]`, the integral model used in the
$`d \equiv 1 \pmod 4` branch.
:::

:::theorem "roi_zsqrtd_branch" (parent := "ring_of_integers_core") (lean := "QuadraticNumberFields.RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one") (tags := "complete, project-only")
If $`d` is squarefree, $`d \ne 1`, and $`d \not\equiv 1 \pmod 4`, then the ring
of integers of $`\mathbb{Q}(\sqrt d)` is equivalent to
{uses "zsqrtd_order"}[$`\mathbb{Z}[\sqrt d]`].
:::

:::theorem "roi_zomega_branch" (parent := "ring_of_integers_core") (lean := "QuadraticNumberFields.RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one") (tags := "complete, project-only")
If $`d \equiv 1 \pmod 4`, then the ring of integers is equivalent to
{uses "zomega_order"}[$`\mathbb{Z}[(1+\sqrt d)/2]`].
:::

:::theorem "roi_classification" (parent := "ring_of_integers_core") (lean := "QuadraticNumberFields.RingOfIntegers.ringOfIntegers_classification") (tags := "complete, project-only")
The classification packages the two branches
{uses "roi_zsqrtd_branch"}[away from $`1 \pmod 4`] and
{uses "roi_zomega_branch"}[at $`1 \pmod 4`] into a single theorem.
:::

:::theorem "integrality_normal_forms" (parent := "ring_of_integers_core") (lean := "QuadraticNumberFields.RingOfIntegers.exists_zsqrtd_of_isIntegral_of_ne_one_mod_four, QuadraticNumberFields.RingOfIntegers.exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four") (tags := "complete, project-only")
The proof runs through half-integer normal forms: integral elements land in the
correct explicit order according to the same mod-4 branch.
:::

:::theorem "roi_transport_to_abstract_fields" (parent := "ring_of_integers_core") (lean := "QuadraticNumberFields.RingOfIntegers.exists_ringOfIntegers_classification_of_quadraticField") (tags := "complete, project-only")
After the standard-model calculation, the result transports to any abstract
quadratic field through the classification by squarefree parameters.
:::

:::theorem "roi_norm_unit_criteria" (parent := "ring_of_integers_core") (lean := "QuadraticNumberFields.RingOfIntegers.isUnit_zsqrtd_iff_norm_eq_one_or_neg_one, QuadraticNumberFields.RingOfIntegers.isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one") (tags := "complete, project-only")
The two explicit integer-ring models have norm-based unit criteria. These are
used again in the unit-theory chapter.
:::
