/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Mathlib
import QuadraticNumberFields.Qsqrtd.Basic
import QuadraticNumberFields.QuadraticField.Basic
import QuadraticNumberFields.QuadraticField.Parameters
import QuadraticNumberFields.QuadraticField.Category
import QuadraticNumberFields.QuadraticField.SqfreeParam
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.Conj
import QuadraticNumberFields.Qsqrtd.Automorphism
import QuadraticNumberFields.Qsqrtd.Galois
import QuadraticNumberFields.QuadraticField.Transport
import QuadraticNumberFields.QuadraticField.RingOfIntegers
import QuadraticNumberFields.RingOfIntegers.ModFour
import QuadraticNumberFields.Zsqrtd.Basic
import QuadraticNumberFields.Zsqrtd.Dedekind
import QuadraticNumberFields.Zsqrtd.MathlibInstances
import QuadraticNumberFields.Zsqrtd.Ideals
import QuadraticNumberFields.RingOfIntegers.HalfInt
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic
import QuadraticNumberFields.Qsqrtd.TraceNorm
import QuadraticNumberFields.RingOfIntegers.Integrality
import QuadraticNumberFields.RingOfIntegers.Basis
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.Splitting.Defs
import QuadraticNumberFields.Splitting.Factorization
import QuadraticNumberFields.Splitting.MinpolyMod
import QuadraticNumberFields.Splitting.Qsqrtd.Classification
import QuadraticNumberFields.Splitting.Qsqrtd.Discriminant
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker
import QuadraticNumberFields.Splitting.Qsqrtd.KroneckerCharacter
import QuadraticNumberFields.Splitting.Qsqrtd.KummerDedekind
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic
import QuadraticNumberFields.Splitting.Qsqrtd.OddPrime
import QuadraticNumberFields.Splitting.Qsqrtd.Two
import QuadraticNumberFields.Splitting.QuadraticField.Basic
import QuadraticNumberFields.Forms.Core.Basic
import QuadraticNumberFields.Forms.Core.Action
import QuadraticNumberFields.Forms.Cox.Bridge
import QuadraticNumberFields.Forms.Cox.LeftInverse
import QuadraticNumberFields.Forms.Cox.LeftInverseEqOne
import QuadraticNumberFields.Forms.Cox.RightInverse
import QuadraticNumberFields.Forms.Cox.Equivalence
import QuadraticNumberFields.Forms.Core.Enumeration
import QuadraticNumberFields.Forms.Core.Reduction
import QuadraticNumberFields.Forms.ClassGroup.ClassNumber
import QuadraticNumberFields.Forms.ClassGroup.Structure
import QuadraticNumberFields.Forms.ClassGroup.Law
import QuadraticNumberFields.ClassNumber
import QuadraticNumberFields.Examples.SqrtNeg5.Ideals
import QuadraticNumberFields.Examples.SqrtNeg5.RamificationInertia
import QuadraticNumberFields.Examples.SqrtNeg5.Splitting
import QuadraticNumberFields.Examples.SqrtNeg5.Invariants
import QuadraticNumberFields.Examples.SqrtNeg5.ClassNumber
import QuadraticNumberFields.Examples.SqrtNeg5.Forms
import QuadraticNumberFields.Examples.Sqrt17.Splitting
import QuadraticNumberFields.Examples.Sqrt17.Invariants
import QuadraticNumberFields.Examples.Sqrt17.ClassNumber
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.Units.Pell
import QuadraticNumberFields.Units.Imaginary
import QuadraticNumberFields.Units.Fundamental
import QuadraticNumberFields.Units.Families
import QuadraticNumberFields.Heegner.ClassNumberOne
import QuadraticNumberFields.Heegner.ClassNumberOneByForms

/-!
# Quadratic Number Fields

This library develops the theory of quadratic number fields `ℚ(√d)` over `ℚ`,
including:

* Basic definitions and the `Qsqrtd d` model
* Parameter classification via squarefree integers
* Ring of integers classification (`ℤ[√d]` vs `ℤ[(1+√d)/2]`)
* Discriminant formulas
* Totally real/complex classification
* Unit groups: Pell-type units, torsion classification in the imaginary case,
  fundamental units, and explicit Richaud-Degert unit candidates
* Class number one for the nine Heegner numbers (the elementary direction of
  the Baker–Heegner–Stark theorem), via Minkowski bounds and inert primes

## Main Import

This file is the main entry point; it re-exports the completed, sorry-free
public modules. Work-in-progress modules (the Euclidean classification
framework and other research scaffolding) are collected separately in
`QuadraticNumberFields.Sketch`.
-/
