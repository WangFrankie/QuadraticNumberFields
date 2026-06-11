import Verso
import VersoManual
import VersoBlueprint
import QuadraticNumberFields

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Ideals and splitting" =>

:::group "ideals_splitting_core"
Concrete ideal computations and the quadratic prime-splitting API.
:::

:::definition "zsqrtd_ideal_membership" (parent := "ideals_splitting_core") (lean := "QuadraticNumberFields.Zsqrtd.Ideal.mem_span_p_one_minus_sqrtd_iff, QuadraticNumberFields.Zsqrtd.Ideal.mem_span_p_one_plus_sqrtd_iff") (tags := "complete, project-only")
For primes $`p` dividing $`d-1`, the ideals $`(p,1-\sqrt d)` and
$`(p,1+\sqrt d)` in `Zsqrtd d` have coordinate membership criteria.
:::

:::definition "zsqrtd_quotients" (parent := "ideals_splitting_core") (lean := "QuadraticNumberFields.Zsqrtd.Ideal.quotEquivZModP, QuadraticNumberFields.Zsqrtd.Ideal.quotEquivZModPNeg") (tags := "complete, project-only")
Those concrete ideals have quotient descriptions by $`\mathbb{Z}/p\mathbb{Z}`,
which supply the primality proofs.
:::

:::theorem "zsqrtd_ideal_primality" (parent := "ideals_splitting_core") (lean := "QuadraticNumberFields.Zsqrtd.Ideal.isPrime_span_p_one_minus_sqrtd, QuadraticNumberFields.Zsqrtd.Ideal.isPrime_span_p_one_plus_sqrtd") (tags := "complete, project-only")
The quotient descriptions prove that both ideals are prime in the relevant
concrete splitting branch.
:::

:::theorem "quadratic_splitting_trichotomy" (parent := "ideals_splitting_core") (lean := "QuadraticNumberFields.Splitting.splitting_classification") (tags := "complete, project-only")
The stable splitting API packages split, inert, and ramified behavior for primes
in quadratic number fields.
:::

:::theorem "legendre_symbol_split_inert" (parent := "ideals_splitting_core") (lean := "QuadraticNumberFields.Splitting.isSplit_iff_legendreSym_eq_one, QuadraticNumberFields.Splitting.isInert_iff_legendreSym_eq_neg_one") (tags := "complete, project-only")
For odd primes not dividing the parameter, splitting and inertia are controlled
by the Legendre symbol.
:::

:::theorem "two_adic_splitting" (parent := "ideals_splitting_core") (lean := "QuadraticNumberFields.Splitting.isSplit_two_of_mod_eight_eq_one, QuadraticNumberFields.Splitting.isInert_two_of_mod_eight_eq_five, QuadraticNumberFields.Splitting.isRamified_two_of_mod_four_ne_one") (tags := "complete, project-only")
The prime $`2` is handled by the expected congruences modulo $`8` and modulo
$`4`.
:::

:::theorem "sqrt_neg_five_factorizations" (parent := "ideals_splitting_core") (lean := "QuadraticNumberFields.Examples.SqrtNeg5.factorization_of_two, QuadraticNumberFields.Examples.SqrtNeg5.factorization_of_three") (tags := "complete, project-only")
The $`\mathbb{Z}[\sqrt{-5}]` examples verify ideal factorizations above $`2`
and $`3`, serving as concrete tests of the ideal API.
:::

:::theorem "kronecker_symbol_unification" (parent := "ideals_splitting_core") (tags := "future, project-only") (effort := "medium")
A future cleanup should unify the odd-prime and two-adic splitting statements
using a Kronecker-symbol formulation where that abstraction is helpful.
:::
