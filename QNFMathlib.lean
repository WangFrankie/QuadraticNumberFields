/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.Algebra.Squarefree.Basic
import QNFMathlib.Algebra.QuadraticAlgebra.Basic
import QNFMathlib.Algebra.QuadraticAlgebra.Defs
import QNFMathlib.Data.Int.ModFour
import QNFMathlib.Data.Int.Parity
import QNFMathlib.Data.Int.Squarefree
import QNFMathlib.FieldTheory.Galois.Basic
import QNFMathlib.GroupTheory.Index
import QNFMathlib.NumberTheory.DirichletCharacter.Kronecker
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbol
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QNFMathlib.NumberTheory.NumberField.ClassNumber
import QNFMathlib.NumberTheory.RamificationInertia.Galois
import QNFMathlib.NumberTheory.Zsqrtd.Basic
import QNFMathlib.RingTheory.PrincipalIdealDomain
import QNFMathlib.RingTheory.Ideal.Span
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QNFMathlib.RingTheory.Krull
import QNFMathlib.RingTheory.DedekindDomain.Basic
import QNFMathlib.RingTheory.DedekindDomain.Ideal

/-!
# Temporary Mathlib Material

This file re-exports project-local material that is intended to be upstreamed to
mathlib. Modules under `QNFMathlib` should mirror the target
mathlib import path when possible and should stay independent of project-specific
quadratic-field definitions.
-/
