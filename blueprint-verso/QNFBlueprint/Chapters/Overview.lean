import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Overview" =>

:::group "overview_surface"
The presentation surface for the current project architecture and roadmap.
:::

:::author "qnf_author" (name := "QuadraticNumberFields project")
:::

:::definition "quadratic_number_fields_project" (parent := "overview_surface") (owner := "qnf_author") (tags := "project-only")
The project formalizes quadratic number fields over $`\mathbb{Q}`. Its core
workflow is to classify an abstract quadratic field, move to a standard
coordinate model $`\mathbb{Q}(\sqrt d)`, compute there, and then transport the
result back to the abstract field.
:::

:::definition "stable_public_surface" (parent := "overview_surface") (lean := "Qsqrtd, QuadraticField, QuadraticNumberFields.RingOfIntegers.ringOfIntegers_classification") (tags := "complete, project-only")
The stable public import surface contains the completed, sorry-free library:
standard models, abstract quadratic-field infrastructure, ring-of-integers and
discriminant classifications, splitting results, units, and examples. It builds
on {uses "quadratic_number_fields_project"}[the project architecture].
:::

:::definition "sketch_surface" (parent := "overview_surface") (tags := "partial, project-only")
The sketch import surface collects work-in-progress modules such as Euclidean,
class-group, continued-fraction, family, and research scaffolding. Nodes that use
this surface should not be marked complete until the corresponding Lean modules
are promoted to {uses "stable_public_surface"}[the stable import surface].
:::

:::definition "mathlib_upstream_boundary" (parent := "overview_surface") (tags := "partial, mathlib-candidate")
General-purpose lemmas live first under `QuadraticNumberFields/Mathlib/`, are
used locally, and should later move upstream to mathlib. Project-only results,
such as the ring-of-integers classification and concrete examples, remain in the
project. This boundary protects {uses "stable_public_surface"}[the public API]
from pretending local shims are already upstream facts.
:::

:::theorem "baker_heegner_stark_long_term_goal" (parent := "overview_surface") (tags := "future, external-assumption, project-only") (effort := "large") (priority := "medium")
The long-term Diophantine goal is a Baker--Heegner--Stark-style route toward
class-number-one and related quadratic-field classification results. In the
first blueprint this remains conditional on substantial future CM, ring-class
field, modular-function, and finite-check input, and it depends on the distinction
between {uses "stable_public_surface"}[formalized infrastructure] and
{uses "sketch_surface"}[research scaffolding].
:::

:::definition "status_vocabulary" (parent := "overview_surface") (tags := "project-only")
Blueprint nodes use explicit tags: `complete` only for existing Lean declarations,
`partial` for scaffolds, `future` for planned mathematics, `mathlib-candidate` for
upstreamable general facts, `project-only` for local APIs, and
`external-assumption` for deferred mathematical input.
:::
