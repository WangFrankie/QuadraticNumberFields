import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import QNFBlueprint.Chapters.BakerHeegnerStark
import QNFBlueprint.Chapters.ClassGroupChecks
import QNFBlueprint.Chapters.Discriminant
import QNFBlueprint.Chapters.IdealsSplitting
import QNFBlueprint.Chapters.MathlibUpstream
import QNFBlueprint.Chapters.Overview
import QNFBlueprint.Chapters.QuadraticCore
import QNFBlueprint.Chapters.RingOfIntegers
import QNFBlueprint.Chapters.Units

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Quadratic Number Fields Blueprint" =>

This is a Verso blueprint for the `QuadraticNumberFields` project. It presents
how the formalization organizes abstract quadratic fields, the standard model
$`\mathbb{Q}(\sqrt d)`, integer-ring classifications, discriminants, ideals,
units, class-group checks, and the longer Baker--Heegner--Stark route.

The blueprint is intentionally a nested Lake package: it imports the project for
declaration links, but it does not add Verso dependencies to the main Lean
library.

{include 0 QNFBlueprint.Chapters.Overview}
{include 0 QNFBlueprint.Chapters.QuadraticCore}
{include 0 QNFBlueprint.Chapters.RingOfIntegers}
{include 0 QNFBlueprint.Chapters.Discriminant}
{include 0 QNFBlueprint.Chapters.IdealsSplitting}
{include 0 QNFBlueprint.Chapters.Units}
{include 0 QNFBlueprint.Chapters.ClassGroupChecks}
{include 0 QNFBlueprint.Chapters.BakerHeegnerStark}
{include 0 QNFBlueprint.Chapters.MathlibUpstream}

{blueprint_graph}
{blueprint_summary}
