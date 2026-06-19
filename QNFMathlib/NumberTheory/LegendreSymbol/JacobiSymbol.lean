/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Jacobi Symbol Prime-Factor Products

Material destined for mathlib.

This file adds a bridge between the `primeFactorsList` definition of the Jacobi
symbol and products over the distinct prime-factor finset in the squarefree case.
-/

namespace jacobiSym

/-- For a squarefree denominator, the Jacobi symbol is the product of the
Legendre symbols over the distinct prime factors of the denominator. -/
theorem eq_prod_primeFactors_of_squarefree (a : ℤ) {n : ℕ} (hn : Squarefree n) :
    jacobiSym a n =
      n.primeFactors.prod fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩ a else 1 := by
  rw [jacobiSym]
  rw [List.pmap_eq_map_attach]
  change (List.map (fun x : {p // p ∈ n.primeFactorsList} =>
        @legendreSym x.1 ⟨Nat.prime_of_mem_primeFactorsList x.2⟩ a)
      n.primeFactorsList.attach).prod =
    n.primeFactors.prod (fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩ a else 1)
  have hmap :
      List.map (fun x : {p // p ∈ n.primeFactorsList} =>
          @legendreSym x.1 ⟨Nat.prime_of_mem_primeFactorsList x.2⟩ a)
        n.primeFactorsList.attach =
      List.map (fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩ a else 1)
        n.primeFactorsList := by
    calc
      List.map (fun x : {p // p ∈ n.primeFactorsList} =>
          @legendreSym x.1 ⟨Nat.prime_of_mem_primeFactorsList x.2⟩ a)
        n.primeFactorsList.attach =
          List.map (fun x : {p // p ∈ n.primeFactorsList} =>
            if hp : x.1.Prime then @legendreSym x.1 ⟨hp⟩ a else 1)
            n.primeFactorsList.attach := by
            apply List.map_congr_left
            intro x _hx
            simp [Nat.prime_of_mem_primeFactorsList x.2]
      _ = List.map (fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩ a else 1)
          n.primeFactorsList := by
            exact (List.attach_map_val
              (f := fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩ a else 1)
              (l := n.primeFactorsList))
  rw [hmap]
  rw [← Nat.toFinset_factors n]
  exact (List.prod_toFinset
    (f := fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩ a else 1)
    (Squarefree.nodup_primeFactorsList hn)).symm

end jacobiSym
