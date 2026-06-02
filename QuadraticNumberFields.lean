/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Mathlib
import QuadraticNumberFields.Basic
import QuadraticNumberFields.Parameters
import QuadraticNumberFields.Instances
import QuadraticNumberFields.Category.Basic
import QuadraticNumberFields.FieldClassification
import QuadraticNumberFields.Mathlib.RingTheory.DedekindDomain.Basic
import QuadraticNumberFields.RingOfIntegers.ModFour
import QuadraticNumberFields.Zsqrtd.Basic
import QuadraticNumberFields.Zsqrtd.Dedekind
import QuadraticNumberFields.Zsqrtd.MathlibInstances
import QuadraticNumberFields.Zsqrtd.Ideals
import QuadraticNumberFields.RingOfIntegers.HalfInt
import QuadraticNumberFields.ZOnePlusSqrtOverTwo.Basic
import QuadraticNumberFields.RingOfIntegers.TraceNorm
import QuadraticNumberFields.RingOfIntegers.Integrality
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.Examples.ZsqrtdNeg5.Ideals
import QuadraticNumberFields.Examples.ZsqrtdNeg5.RamificationInertia
import QuadraticNumberFields.TotallyRealComplex

/-!
# Quadratic Number Fields

This library develops the theory of quadratic number fields `ℚ(√d)` over `ℚ`,
including:

* Basic definitions and the `Qsqrtd d` model
* Parameter classification via squarefree integers
* Ring of integers classification (`ℤ[√d]` vs `ℤ[(1+√d)/2]`)
* Discriminant formulas
* Totally real/complex classification

## Main Import

This file is the main entry point; it re-exports the completed, sorry-free
public modules. Work-in-progress modules (the Euclidean classification
framework and the prime-splitting development) are collected separately in
`QuadraticNumberFields.Sketch`.
-/
