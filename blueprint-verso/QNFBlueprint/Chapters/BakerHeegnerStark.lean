import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Baker--Heegner--Stark route" =>

:::group "baker_heegner_stark_core"
The long-term conditional route beyond the current formalized infrastructure.
:::

:::theorem "cox_class_number_one_route" (parent := "baker_heegner_stark_core") (tags := "future, external-assumption, project-only") (effort := "large")
The long-term route follows the classical Cox-style story around imaginary
quadratic class-number-one fields, singular moduli, and ring class fields.
This is not yet a Lean theorem in the project.
:::

:::theorem "cm_ring_class_field_input" (parent := "baker_heegner_stark_core") (tags := "future, external-assumption, project-only") (effort := "large")
The route requires substantial CM and ring-class-field input. The current
blueprint records this as an external mathematical dependency rather than a
completed formalization.
:::

:::theorem "stark_transcendence_input" (parent := "baker_heegner_stark_core") (tags := "future, external-assumption, project-only") (effort := "large")
The Baker--Stark analytic/transcendence ingredients are also external
assumptions at this stage.
:::

:::theorem "conditional_diophantine_endgame" (parent := "baker_heegner_stark_core") (tags := "future, project-only") (effort := "large")
Once the external CM and analytic inputs are available, the project should
connect them to explicit finite Diophantine checks in quadratic fields.
:::

:::theorem "reuse_discriminant_and_splitting" (parent := "baker_heegner_stark_core") (tags := "future, project-only")
The conditional endgame should reuse the existing discriminant, splitting,
ring-of-integers, units, and class-group check layers rather than duplicating
coordinate arguments.
:::

:::theorem "bhs_public_status" (parent := "baker_heegner_stark_core") (tags := "future, external-assumption, project-only")
All Baker--Heegner--Stark nodes are deliberately marked future or external in
this first blueprint. None should be read as a completed Lean proof.
:::
