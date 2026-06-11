import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Quadratic core" =>

:::group "quadratic_core"
The abstract quadratic-field layer and the standard coordinate model.
:::

:::definition "standard_model_qsqrtd" (parent := "quadratic_core") (lean := "Qsqrtd") (tags := "complete, mathlib-candidate")
The standard coordinate model is $`\mathbb{Q}(\sqrt d)`, implemented as
`Qsqrtd d := QuadraticAlgebra ℚ d 0`. It is the computational model used for
trace, norm, conjugation, discriminants, and splitting calculations.
:::

:::definition "abstract_quadratic_field" (parent := "quadratic_core") (lean := "QuadraticField") (tags := "complete, mathlib-candidate")
`QuadraticField K` is the project-level property that a field over
$`\mathbb{Q}` is a quadratic extension. It is the abstract object of study;
{uses "standard_model_qsqrtd"}[the standard model] is a coordinate chart.
:::

:::definition "quadratic_field_category" (parent := "quadratic_core") (tags := "project-only")
`QuadraticFieldCat` bundles fields satisfying {uses "abstract_quadratic_field"}[`QuadraticField`]
and organizes isomorphisms, functors, transport, and classification.
:::

:::definition "standard_parameters" (parent := "quadratic_core") (lean := "IsStandardParameter") (tags := "complete, mathlib-candidate")
A standard parameter is a squarefree integer $`d \ne 1` together with an algebra
equivalence from the abstract field to {uses "standard_model_qsqrtd"}[`Qsqrtd d`].
:::

:::theorem "abstract_qf_classification" (parent := "quadratic_core") (lean := "exists_algEquiv_qsqrtd") (tags := "complete, mathlib-candidate")
Every {uses "abstract_quadratic_field"}[abstract quadratic field] is
$`\mathbb{Q}`-algebra-equivalent to {uses "standard_model_qsqrtd"}[`Qsqrtd d`]
for some squarefree integer $`d \ne 1`.
:::

:::theorem "ring_equiv_shadow" (parent := "quadratic_core") (lean := "exists_ringEquiv_qsqrtd") (tags := "complete, mathlib-candidate")
The classification also has a ring-equivalence shadow. This is useful when
transporting invariants whose API is stated for ring equivalences rather than
algebra equivalences.
:::

:::theorem "quadratic_field_iff_standard_model" (parent := "quadratic_core") (lean := "isQuadraticField_iff_exists_squarefree_int_param") (tags := "complete, mathlib-candidate")
A field over $`\mathbb{Q}` is quadratic if and only if it is isomorphic to one of
{uses "standard_parameters"}[the normalized standard models].
:::

:::theorem "parameter_uniqueness" (parent := "quadratic_core") (lean := "Qsqrtd.param_unique") (tags := "complete, mathlib-candidate")
Squarefree standard parameters are unique: an algebra equivalence between
`Qsqrtd d₁` and `Qsqrtd d₂` forces $`d_1 = d_2` under the normalized hypotheses.
:::

:::theorem "trace_norm_coordinate_api" (parent := "quadratic_core") (lean := "Qsqrtd.trace_eq_two_re, Qsqrtd.normHom_apply") (tags := "complete, mathlib-candidate")
The coordinate API computes trace and norm directly in
{uses "standard_model_qsqrtd"}[`Qsqrtd d`]. These formulas feed the
ring-of-integers and unit calculations.
:::

:::theorem "quadratic_automorphism_dichotomy" (parent := "quadratic_core") (lean := "Qsqrtd.algEquiv_self_eq_refl_or_star, QuadraticField.univ_aut_eq_pair") (tags := "complete, project-only")
The automorphism group of a quadratic field has the expected dichotomy: the only
automorphisms are the identity and conjugation.
:::
