import Mathlib

/-!
# OEIS A002070: coefficients at primes of `x ∏ (1-x^k)²(1-x^(11k))²`

Source: https://oeis.org/A002070
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the coefficient of `x^p`, `p = prime(n)`, in `x ∏_{k ≥ 1} (1 - x^k)² (1 - x^(11k))²`.
Conjecture (OEIS entry):
`a(n) = ∑_{k=1}^{p} ∑_{y=1}^{p} ∑_{x=1}^{p} (A023900(k)/p) [gcd(f(x, y), p) = k]` with
`f(x, y) = x³ - x² - y² - y`, where `A023900` is the Dirichlet inverse of Euler's totient,
`A023900(k) = ∏_{q prime, q ∣ k} (1 - q)`.

Conventions:
* The coefficient of `x^p` only involves the factors with `k ≤ p`, so the product is truncated
  at `k ≤ p`. `p` ranges over all primes (equivalently `n ≥ 1`).
* `gcd` is `Int.gcd` (so `gcd(0, p) = p`); the sum is computed in `ℚ`.
-/

namespace OMA.S_oeis_a002070

open Polynomial

/-- Coefficient of `x^p` in `x ∏_{k ≥ 1} (1 - x^k)²(1 - x^(11k))²`. -/
noncomputable def coeffAt (p : ℕ) : ℤ :=
  (X * ∏ k ∈ Finset.range p, ((1 - X ^ (k + 1)) ^ 2 * (1 - X ^ (11 * (k + 1))) ^ 2 : ℤ[X])).coeff p

/-- `A023900(k) = ∏_{q ∣ k prime} (1 - q)`. -/
def A023900 (k : ℕ) : ℤ := ∏ q ∈ k.primeFactors, (1 - (q : ℤ))

/-- `f(x, y) = x³ - x² - y² - y`. -/
def f (x y : ℤ) : ℤ := x ^ 3 - x ^ 2 - y ^ 2 - y

/-- The conjectured triple sum. -/
def S (p : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 p, ∑ y ∈ Finset.Icc 1 p, ∑ x ∈ Finset.Icc 1 p,
    if Int.gcd (f x y) p = k then (A023900 k : ℚ) / p else 0

/-- For every prime `p`, the coefficient equals the triple sum. -/
theorem main : ∀ p : ℕ, p.Prime → (coeffAt p : ℚ) = S p := by
  sorry

end OMA.S_oeis_a002070
