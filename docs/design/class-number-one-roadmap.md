# Class Number One: Weber Functions and Complex Multiplication

This note tracks the remaining work for an unconditional Baker--Heegner--Stark
theorem along Heegner's route (Cox, *Primes of the form x² + ny²*, §12.D,
Theorem 12.34).

This development is preserved on `legacy/baker-heegner-stark` as of 2026-10-28.
Completion is planned in a separate repository; the statements below record
the mathematical status of this snapshot. See the
[preservation record](../contributions.md#baker-heegner-stark-development).

## Current state

`classNumber_eq_one_iff_mem_heegnerSet_of_conductorTwoWeberHypothesis` proves the
theorem from one explicit hypothesis, `ConductorTwoWeberHypothesis`. The following
elementary results are formalized and sorry-free:

- the genus-theory sieve and the ideal-theoretic reductions leave the inert
  family `d = -p`, `p ≡ 3 (mod 8)`;
- class number one for `-p` gives exactly three reduced forms of discriminant
  `-4p` (`card_enumPrimitiveReducedForms_neg_four_mul_eq_three`); identifying
  this count with the class number of the order `ℤ[√-p]` is still required;
- the integral points of `Y² = 2X(X³ + 1)` and their gamma values
  (`heegner_xy_solutions`, `gamma_mem_heegnerGammaSet_of_xy_solution`).

`ConductorTwoWeberHypothesis` is Heegner's Weber-function step: for such `p`, three
reduced forms of discriminant `-4p` produce an integral point of the curve whose
gamma value identifies `p`.

## Milestones

### M1. Weber functions and `j` (general modular-function theory)

Files under `QNFMathlib/NumberTheory/ModularForms/`.

Proved:

- Weber functions as eta quotients (`Weber.lean`):
  `𝔣₁(τ) = η(τ/2)/η(τ)`, `𝔣₂(τ) = √2 η(2τ)/η(τ)`,
  `𝔣(τ) = ζ₄₈⁻¹ η((τ+1)/2)/η(τ)`.
- Transformation laws under `T` and `S`, using
  `η(τ + 1) = ζ₂₄ η(τ)` and `η(-1/τ) = √(τ/i) η(τ)`.
- `𝔣 𝔣₁ 𝔣₂ = √2`, from the product expansions and Euler's identity.
- `γ₂ = E₄/η⁸`, `j = E₄³/Δ = γ₂³`; `j` is holomorphic on `ℍ` and invariant
  under `SL₂(ℤ)` (`JInvariant.lean`).
- The full factorization of Weber's cubic (`weber_cubic_factorization` in
  `WeberPolynomial.lean`):
  `(X - 𝔣²⁴)(X + 𝔣₁²⁴)(X + 𝔣₂²⁴) = (X - 16)³ - jX`.
  The first two symmetric functions follow from the weight-12 and weight-24
  cusp forms in `HeckeTwo.lean` and `HeckeTwoSymmetric.lean`; the third follows
  from Weber's product identity.
- Consequently,
  `j = (𝔣²⁴ - 16)³/𝔣²⁴ = (𝔣₁²⁴ + 16)³/𝔣₁²⁴ = (𝔣₂²⁴ + 16)³/𝔣₂²⁴`.

- Weber's `γ₂`-identities (`WeberGamma.lean`):
  `γ₂ = (𝔣²⁴ - 16)/𝔣⁸ = (𝔣₁²⁴ + 16)/𝔣₁⁸ = (𝔣₂²⁴ + 16)/𝔣₂⁸`.
  The cubes agree by Weber's cubic. For `𝔣₂` the cube root is fixed because
  both sides tend to `16` at `i∞`, and the identity theorem extends the
  equality from a half-plane to `ℍ`; the other two are its `S`- and
  `T`-transforms.

Remaining:

- `𝔣⁸ = 𝔣₁⁸ + 𝔣₂⁸`.
- Values on the imaginary axis are real and positive.

### M2. The modular polynomial `Φ₂`

Proved in `ModularPolynomialTwo.lean`:

- `modularPolynomialTwo : ℤ[X][Y]` is symmetric, monic, and cubic in `Y`.
- `Φ₂(j(τ), j(2τ)) = 0`, by eliminating `t = 𝔣₂(τ)²⁴` from
  `j(τ) = (t + 16)³/t` and `j(2τ) = (t + 256)³/t²`.
- `j(τ/2)` and `j((τ+1)/2)` also satisfy `Φ₂(j(τ), Y) = 0`.

Remaining: identify these analytic values, with multiplicities, with the
`j`-values of the three index-two sublattices of `𝓞_K`, and hence with the
three reduced forms of discriminant `-4p` counted above. The polynomial
identities alone do not supply that CM/order correspondence.

### M3. Complex multiplication I (research level)

`j` at an imaginary quadratic point is an algebraic integer, and
`h(K) = 1 ⇒ j(τ_K) ∈ ℤ`. This needs a Galois-stable characterization of the
`j`-values with complex multiplication by `𝓞_K` (elliptic curves and the action
of `Aut(ℂ)`, or class field theory). These CM theorems are not yet proved in
the present development.

### M4. Weber's rationality theorems (research level)

For `3 ∤ d_K`, `γ₂(τ_K) ∈ ℚ(j(τ_K))`; for `p ≡ 3 (mod 8)`,
`𝔣(√-p)² ∈ ℚ(j(√-p))` and `[ℚ(j(√-p)) : ℚ] = h(-4p) = 3`.

### M5. Heegner's algebra

From the cubic minimal polynomial of `𝔣(√-p)²` and the identities of M1,
derive the integral point of `Y² = 2X(X³ + 1)` and the gamma value
`γ₂(τ_K)`; identify `p` from the gamma table. This assembles
`ConductorTwoWeberHypothesis`.

## Notes

- `ConductorTwoClassNumberParameters` in `ImaginaryClassNumberOne/Weber/Heegner.lean`
  is inhabited for every `p`; Weber's existence hypothesis must assume the
  actual reduced-form count.
- References: D. A. Cox, *Primes of the form x² + ny²*, 2nd ed., §§11–12;
  H. M. Stark, *On the "gap" in a theorem of Heegner*, J. Number Theory 1
  (1969); H. Weber, *Lehrbuch der Algebra III*.
