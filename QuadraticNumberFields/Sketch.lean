/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassGroup.Divisibility
import QuadraticNumberFields.ClassGroup.Families
import QuadraticNumberFields.ClassGroup.GenusTheory
import QuadraticNumberFields.ClassGroup.Infrastructure
import QuadraticNumberFields.ClassGroup.Minkowski
import QuadraticNumberFields.ClassGroup.ReducedIdeals
import QuadraticNumberFields.ClassGroup.Torsion
import QuadraticNumberFields.ClassNumber
import QuadraticNumberFields.ContinuedFraction.Families
import QuadraticNumberFields.ContinuedFraction.Periodic
import QuadraticNumberFields.ContinuedFraction.Qsqrtd
import QuadraticNumberFields.Euclidean.Basic
import QuadraticNumberFields.Families.Basic
import QuadraticNumberFields.Families.Chowla
import QuadraticNumberFields.Families.RichaudDegert
import QuadraticNumberFields.Families.Yokoi
import QuadraticNumberFields.Heegner.StarkHeegner
import QuadraticNumberFields.Qsqrtd.Automorphism
import QuadraticNumberFields.Qsqrtd.Basic
import QuadraticNumberFields.Qsqrtd.Equiv
import QuadraticNumberFields.Qsqrtd.TraceNorm
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.Sketch.KroneckerCharacter

/-!
# Work-in-progress surface

This module collects the **unfinished** parts of the library — modules that
still contain `sorry` placeholders or theorem skeletons. It is intentionally
kept out of the stable `QuadraticNumberFields` entry point so that
`import QuadraticNumberFields` exposes only completed, sorry-free results.

Current work in progress:

* `Euclidean.Basic`: imaginary-quadratic norm-Euclidean classification skeleton.
* `Sketch.KroneckerCharacter`: `DirichletCharacter` packaging of the Kronecker
  symbol; the `MulChar` obligations are still `sorry`.
* `Heegner.StarkHeegner`: full Baker–Heegner–Stark statement; the deep
  direction (completeness of the nine Heegner numbers) is still `sorry`.
* `Families.*`, `ContinuedFraction.*`, and `ClassGroup.*`: research
  scaffolding for real quadratic class-number problems.

Promote a module into `QuadraticNumberFields.lean` once it is sorry-free.
-/
