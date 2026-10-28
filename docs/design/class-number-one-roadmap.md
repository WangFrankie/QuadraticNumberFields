# Class Number One: Roadmap for the Weber/CM Input

This note tracks the remaining work for an unconditional Baker--Heegner--Stark
theorem along Heegner's route (Cox, *Primes of the form x² + ny²*, §12.D,
Theorem 12.34).

## Current state

`classNumber_eq_one_iff_mem_heegnerSet_of_conductorTwoWeberInput` proves the
theorem from one explicit hypothesis, `ConductorTwoWeberInput`. Everything else
on the route is formalized and sorry-free:

- the genus-theory sieve and the ideal-theoretic reductions leave the inert
  family `d = -p`, `p ≡ 3 (mod 8)`;
- class number one for `-p` gives exactly three reduced forms of discriminant
  `-4p` (`card_enumPrimitiveReducedForms_neg_four_mul_eq_three`), i.e. the order
  `ℤ[√-p]` of conductor `2` has class number `3`;
- the integral points of `Y² = 2X(X³ + 1)` and their gamma values
  (`heegner_xy_solutions`, `gamma_mem_heegnerGammaSet_of_xy_solution`).

`ConductorTwoWeberInput` is Heegner's Weber-function step: for such `p`, three
reduced forms of discriminant `-4p` produce an integral point of the curve whose
gamma value identifies `p`.

## Milestones

### M1. Weber functions and `j` (general modular-function theory)

Files under `QNFMathlib/NumberTheory/ModularForms/`.

- Weber functions as eta quotients:
  `𝔣₁(τ) = η(τ/2)/η(τ)`, `𝔣₂(τ) = √2 η(2τ)/η(τ)`,
  `𝔣(τ) = ζ₄₈⁻¹ η((τ+1)/2)/η(τ)`.
- Transformation laws under `T` and `S`; these only need
  `η(τ + 1) = ζ₂₄ η(τ)` and `η(-1/τ) = √(τ/i) η(τ)`.
- `𝔣 𝔣₁ 𝔣₂ = √2`, from the product expansions and Euler's identity.
- `γ₂ = E₄/η⁸`, `j = E₄³/Δ = γ₂³`, and
  `γ₂ = (𝔣²⁴ - 16)/𝔣⁸ = (𝔣₁²⁴ + 16)/𝔣₁⁸ = (𝔣₂²⁴ + 16)/𝔣₂⁸`,
  `𝔣⁸ = 𝔣₁⁸ + 𝔣₂⁸`. Method: the symmetric functions of
  `{𝔣²⁴, -𝔣₁²⁴, -𝔣₂²⁴}` are level-one weight-zero modular forms (or become
  so after subtracting `j`); compare constant terms at `i∞` and use
  `levelOne_weight_zero_const`.
- Values on the imaginary axis are real and positive.

### M2. The modular polynomial `Φ₂`

`Φ₂(X, Y) ∈ ℤ[X, Y]` with `Φ₂(j(2τ), j(τ)) = 0`. Its three roots in `X` over
`j(τ_K)` are the `j`-values of the three index-two sublattices of `𝓞_K`, i.e.
of the three reduced forms of discriminant `-4p` counted above.

### M3. Complex multiplication I (research level)

`j` at an imaginary quadratic point is an algebraic integer, and
`h(K) = 1 ⇒ j(τ_K) ∈ ℤ`. This needs a Galois-stable characterization of the
`j`-values with complex multiplication by `𝓞_K` (elliptic curves and the action
of `Aut(ℂ)`, or class field theory). Mathlib currently has neither.

### M4. Weber's rationality theorems (research level)

For `3 ∤ d_K`, `γ₂(τ_K) ∈ ℚ(j(τ_K))`; for `p ≡ 3 (mod 8)`,
`𝔣(√-p)² ∈ ℚ(j(√-p))` and `[ℚ(j(√-p)) : ℚ] = h(-4p) = 3`.

### M5. Heegner's algebra

From the cubic minimal polynomial of `𝔣(√-p)²` and the identities of M1,
derive the integral point of `Y² = 2X(X³ + 1)` and the gamma value
`γ₂(τ_K)`; identify `p` from the gamma table. This assembles
`ConductorTwoWeberInput`.

## Notes

- `RingClassNumberConductorTwoData` in `ImaginaryClassNumberOne/WeberData/Core.lean`
  is inhabited for every `p`; deep inputs must take the Forms-side reduced-form
  count as hypothesis instead.
- References: D. A. Cox, *Primes of the form x² + ny²*, 2nd ed., §§11–12;
  H. M. Stark, *On the "gap" in a theorem of Heegner*, J. Number Theory 1
  (1969); H. Weber, *Lehrbuch der Algebra III*.
