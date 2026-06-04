/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Defs
import QuadraticNumberFields.Splitting.Factorization
import QuadraticNumberFields.Splitting.MinpolyMod
import QuadraticNumberFields.Splitting.Qsqrtd.Classification
import QuadraticNumberFields.Splitting.Qsqrtd.Discriminant
import QuadraticNumberFields.Splitting.Qsqrtd.KummerDedekind
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic
import QuadraticNumberFields.Splitting.Qsqrtd.OddPrime
import QuadraticNumberFields.Splitting.Qsqrtd.Two
import QuadraticNumberFields.Splitting.QuadraticField.Basic

/-!
# Prime Splitting in Quadratic Number Fields

This module re-exports the prime-splitting development for quadratic number fields.

The concrete `Qsqrtd d` layer gives the explicit split, inert, and ramified
classification in terms of congruence and Legendre-symbol conditions. The abstract
quadratic-field layer provides the general quadratic-extension trichotomy for rings of
integers.
-/
