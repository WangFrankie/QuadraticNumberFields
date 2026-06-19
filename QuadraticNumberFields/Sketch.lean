/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassGroup.Computed
import QuadraticNumberFields.ClassGroup.Divisibility
import QuadraticNumberFields.ClassGroup.Families
import QuadraticNumberFields.ClassGroup.GenusTheory.Characters
import QuadraticNumberFields.ClassGroup.GenusTheory.Discriminant
import QuadraticNumberFields.ClassGroup.GenusTheory.Formula
import QuadraticNumberFields.ClassGroup.GenusTheory.OddProduct
import QuadraticNumberFields.ClassGroup.GenusTheory.Sieve
import QuadraticNumberFields.ClassGroup.GenusTheory.SquareClass
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
import QuadraticNumberFields.Forms.Computable.ClassGroup
import BinaryQuadraticForms.Computable.Composition
import BinaryQuadraticForms.Computable.Reduction
import QuadraticNumberFields.Forms.Computable.Structure
import QuadraticNumberFields.Examples.ClassGroupStructure
import BinaryQuadraticForms.Gauss.Composition
import QuadraticNumberFields.Forms.Gauss.CompositionClass
import QuadraticNumberFields.Heegner.Diophantine
import QuadraticNumberFields.Heegner.WeberData.Core
import QuadraticNumberFields.Heegner.WeberData.FormsProvider
import QuadraticNumberFields.Heegner.Framework
import QuadraticNumberFields.Heegner.StarkHeegner
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

* `Forms.Computable.Composition`: computable Dirichlet composition (`composeForm`,
  CRT-adjusted).  Correctness proofs (`disc_composeForm`, `composeForm_mk`) WIP.
* `Forms.Computable.Reduction`: computable Gauss reduction (`reduceForm`,
  well-founded recursion).  Correctness proofs (`reduceForm_isReduced`,
  `reduceForm_properEquivalent`) WIP.
* `Forms.Computable.ClassGroup`: computable Gauss multiplication `gaussMul` /
  `composeAndReduce` with Klein-four-group verification for `d=-21`.
  Consistency proof (`gaussMul = reducedFormRepMul`) WIP.
* `Forms.Computable.Structure`: reduced-form class-group output transported to
  standard finite-abelian targets; concrete computations live in
  `Examples.ClassGroupStructure`.
* `Euclidean.Basic`: imaginary-quadratic norm-Euclidean classification skeleton.
* `Heegner.Diophantine`, `Heegner.WeberData.Core`,
  `Heegner.WeberData.FormsProvider`, `Heegner.Framework`, and
  `Heegner.StarkHeegner`: proof-framework layers for the Baker–Heegner–Stark
  statement; the core Weber data interface is sorry-free, while the named genus,
  Forms-provider, and Diophantine inputs are still `sorry`.
* `Families.*`, `ContinuedFraction.*`, and `ClassGroup.*`: research
  scaffolding for real quadratic class-number problems.

Promote a module into `QuadraticNumberFields.lean` once it is sorry-free.
-/
