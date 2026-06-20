/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib
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
import QuadraticNumberFields.ClassGroup.ClassNumber
import QuadraticNumberFields.ClassGroup.Minkowski
import QuadraticNumberFields.ClassGroup.SmallNorm
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.Units.Pell
import QuadraticNumberFields.Units.Imaginary
import QuadraticNumberFields.Units.Fundamental
import QuadraticNumberFields.Units.Families

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

## Main Import

This file is the main entry point for the core quadratic-number-field library.
App layers such as form class groups, imaginary class-number-one results, and
examples live in separate Lake libraries.
-/
