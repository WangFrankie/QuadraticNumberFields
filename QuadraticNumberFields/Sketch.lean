/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassGroup
import QuadraticNumberFields.ClassNumber
import QuadraticNumberFields.ContinuedFraction
import QuadraticNumberFields.Euclidean.Basic
import QuadraticNumberFields.Families
import QuadraticNumberFields.Qsqrtd.Automorphism
import QuadraticNumberFields.Qsqrtd.Basic
import QuadraticNumberFields.Qsqrtd.Equiv
import QuadraticNumberFields.Qsqrtd.TraceNorm
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex

/-!
# Work-in-progress surface

This module collects the **unfinished** parts of the library — modules that
still contain `sorry` placeholders or theorem skeletons. It is intentionally
kept out of the stable `QuadraticNumberFields` entry point so that
`import QuadraticNumberFields` exposes only completed, sorry-free results.

Current work in progress:

* `Euclidean.Basic`: imaginary-quadratic norm-Euclidean classification skeleton.
* `Families.*`, `ContinuedFraction.*`, and `ClassGroup.*`: research
  scaffolding for real quadratic class-number problems.

Promote a module into `QuadraticNumberFields.lean` once it is sorry-free.
-/
