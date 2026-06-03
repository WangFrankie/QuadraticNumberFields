/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Mathlib.Algebra.Squarefree.Basic
import QuadraticNumberFields.Mathlib.Algebra.QuadraticAlgebra.Defs
import QuadraticNumberFields.Mathlib.Data.Int.ModFour
import QuadraticNumberFields.Mathlib.Data.Int.Squarefree
import QuadraticNumberFields.Mathlib.FieldTheory.Galois.Basic
import QuadraticNumberFields.Mathlib.NumberTheory.RamificationInertia.Galois
import QuadraticNumberFields.Mathlib.NumberTheory.Zsqrtd.Basic
import QuadraticNumberFields.Mathlib.RingTheory.PrincipalIdealDomain
import QuadraticNumberFields.Mathlib.RingTheory.Ideal.Span
import QuadraticNumberFields.Mathlib.RingTheory.Krull
import QuadraticNumberFields.Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Temporary Mathlib Material

This file re-exports project-local material that is intended to be upstreamed to
mathlib. Modules under `QuadraticNumberFields.Mathlib` should mirror the target
mathlib import path when possible and should stay independent of project-specific
quadratic-field definitions.
-/
