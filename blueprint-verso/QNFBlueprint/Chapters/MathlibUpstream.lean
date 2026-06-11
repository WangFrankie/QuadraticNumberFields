import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Mathlib upstream boundary" =>

:::group "mathlib_upstream_core"
Local shims, upstream candidates, and project-only APIs.
:::

:::definition "local_mathlib_shims" (parent := "mathlib_upstream_core") (tags := "partial, mathlib-candidate")
General-purpose facts that are missing from mathlib are developed locally under
`QuadraticNumberFields/Mathlib/`, mirroring likely upstream paths.
:::

:::theorem "discriminant_transport_shim" (parent := "mathlib_upstream_core") (lean := "NumberField.discr_eq_of_algEquiv") (tags := "complete, mathlib-candidate")
`NumberField.discr_eq_of_algEquiv` is a local upstream candidate for transporting
absolute discriminants across algebra equivalences.
:::

:::definition "ring_of_integers_transport_shim" (parent := "mathlib_upstream_core") (lean := "AlgEquiv.ringOfIntegers") (tags := "complete, mathlib-candidate")
`AlgEquiv.ringOfIntegers` transports rings of integers across algebra
equivalences and belongs to the general transport layer.
:::

:::theorem "dedekind_transport_shim" (parent := "mathlib_upstream_core") (lean := "RingEquiv.isDedekindDomain_ringOfIntegers") (tags := "complete, mathlib-candidate")
The Dedekind-domain transport lemma is another candidate for eventual upstream
movement once its final mathlib home is chosen.
:::

:::definition "project_owned_zsqrtd_boundary" (parent := "mathlib_upstream_core") (lean := "QuadraticNumberFields.Zsqrtd") (tags := "complete, project-only")
The project-owned `Zsqrtd` model stays independent from mathlib's `Zsqrtd` except
for the dedicated bridge file. This is project architecture, not an upstream API.
:::

:::theorem "ring_of_integers_project_only" (parent := "mathlib_upstream_core") (lean := "QuadraticNumberFields.RingOfIntegers.ringOfIntegers_classification") (tags := "complete, project-only")
The ring-of-integers classification is currently project-only: it is central to
this repository but not presented as a finished mathlib theorem.
:::

:::theorem "upstream_lifecycle" (parent := "mathlib_upstream_core") (tags := "partial, mathlib-candidate")
The intended lifecycle is: add a local shim, use it in the project, upstream it
through a mathlib PR, then delete the local shim and migrate callers.
:::
